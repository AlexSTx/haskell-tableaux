import           Data.Binary (Binary)
import           Data.Char (isAlpha, isSpace)
import           Data.List (find, isPrefixOf, stripPrefix)
import           Data.Maybe (isJust, isNothing, maybe)

operators :: [String]
operators = ["&", "|", "~", "->", "<->"]

type HasParens = Bool

type Operator = String

type Operand = String

data Node = BinaryOperation Operator Node Node HasParens
          | UnaryOperation Operator Node HasParens
          | Leaf Operand HasParens
  deriving (Show, Eq)

trimm :: String -> String
trimm = filter (not . isSpace)

takeRestAfterParens' :: String -> Int -> String
takeRestAfterParens' string level
  | null string = ""
  | level == 0 = string
  | head string == '(' = takeRestAfterParens' (tail string) (level + 1)
  | head string == ')' = takeRestAfterParens' (tail string) (level - 1)
  | otherwise = takeRestAfterParens' (tail string) level

takeRestAfterParens :: String -> String
takeRestAfterParens s = takeRestAfterParens' (tail s) 1

takeInsideParens :: String -> String
takeInsideParens string = tail
  (take (length string - length (takeRestAfterParens string) - 1) string)

startsWithOperator :: String -> Bool
startsWithOperator s = not (null s) && any (`isPrefixOf` s) operators

getOperator :: String -> String
getOperator s = do
  let operator = find (`isPrefixOf` s) operators
  case operator of
    Just operator -> operator
    Nothing       -> error "no operator found"

getAfterOperator :: String -> String -> String
getAfterOperator op s = do
  let rest = stripPrefix op s
  case rest of
    Just rest -> rest
    Nothing   -> error "nothing found after operator"

createNodeFromStr :: String -> HasParens -> Node
createNodeFromStr e hasParens
  | head e == '~' = do
    let nextChar = head (tail e)
    let rest = tail (tail e)
    if isAlpha nextChar
      then if startsWithOperator rest
           then BinaryOperation
             (getOperator rest)
             (UnaryOperation "~" (createNodeFromStr [nextChar] False) hasParens)
             (createNodeFromStr
                (getAfterOperator (getOperator rest) rest)
                False)
             hasParens
           else UnaryOperation
             "~"
             (createNodeFromStr [nextChar] False)
             hasParens
      else if nextChar == '('
           then if startsWithOperator (takeRestAfterParens (tail e))
                then BinaryOperation
                  (getOperator (takeRestAfterParens (tail e)))
                  (UnaryOperation
                     "~"
                     (createNodeFromStr (takeInsideParens (tail e)) True)
                     hasParens)
                  (createNodeFromStr
                     (getAfterOperator
                        (getOperator (takeRestAfterParens (tail e)))
                        (takeRestAfterParens (tail e)))
                     False)
                  hasParens
                else UnaryOperation
                  "~"
                  (createNodeFromStr (takeInsideParens (tail e)) True)
                  hasParens
           else Leaf "Invalid Operation" False
  | head e == '(' = do
    let rest = takeRestAfterParens e
    if startsWithOperator rest
      then BinaryOperation
        (getOperator rest)
        (createNodeFromStr (takeInsideParens e) True)
        (createNodeFromStr (getAfterOperator (getOperator rest) rest) False)
        hasParens
      else createNodeFromStr (takeInsideParens e) True
  | isAlpha (head e) = do
    let rest = tail e
    if startsWithOperator rest
      then BinaryOperation
        (getOperator rest)
        (Leaf [head e] False)
        (createNodeFromStr (getAfterOperator (getOperator rest) rest) False)
        hasParens
      else Leaf [head e] hasParens
  | otherwise = Leaf e False

createSyntaxTree :: String -> Node
createSyntaxTree equation = createNodeFromStr (trimm equation) False

printSyntaxTree :: Node -> String
printSyntaxTree (BinaryOperation operator operand1 operand2 hasParens)
  | hasParens = "("
    ++ printSyntaxTree operand1
    ++ operator
    ++ printSyntaxTree operand2
    ++ ")"
  | not hasParens =
    printSyntaxTree operand1 ++ operator ++ printSyntaxTree operand2
printSyntaxTree (UnaryOperation operator operand hasParens)
  | hasParens = "(" ++ operator ++ printSyntaxTree operand ++ ")"
  | not hasParens = operator ++ printSyntaxTree operand
printSyntaxTree (Leaf operand hasParens)
  | hasParens = "(" ++ operand ++ ")"
  | not hasParens = operand

negateNode :: Node -> Node
negateNode (BinaryOperation operator operand1 operand2 hasParens) =
  UnaryOperation "~" (BinaryOperation operator operand1 operand2 True) False
negateNode (UnaryOperation operator operand hasParens) = operand -- can do that because negation is the only unary operation
negateNode (Leaf operand hasParens) =
  UnaryOperation "~" (Leaf operand hasParens) False

xor :: Bool -> Bool -> Bool
xor p q = (p && not q) || (not p && q)

fromMaybe :: a -> Maybe a -> a
fromMaybe defval Nothing = defval
fromMaybe _ (Just val) = val

data Type = Dysjunction
          | Conjunction
          | Terminal
  deriving (Show, Eq)

type IsNegated = Bool

getTypeData :: Operator -> IsNegated -> (Type, IsNegated, IsNegated)
getTypeData op isNeg
  | isNeg = case op of
    "->" -> (Conjunction, False, True)
    "&"  -> (Dysjunction, True, True)
    "|"  -> (Conjunction, True, True)
    _    -> (Terminal, True, True)
  | not isNeg = case op of
    "->" -> (Dysjunction, True, False)
    "&"  -> (Conjunction, False, False)
    "|"  -> (Dysjunction, False, False)
    _    -> (Terminal, False, False)

data RefutationNode =
    RefNode Node Type IsNegated (Maybe RefutationNode) (Maybe RefutationNode)
  | RefLeaf String Type IsNegated (Maybe RefutationNode) (Maybe RefutationNode)
  deriving (Show, Eq)

getInfoCarga :: Node -> (Operator, Maybe Node, Maybe Node)
getInfoCarga (BinaryOperation operator first second _) =
  (operator, Just first, Just second)
getInfoCarga (UnaryOperation operator _ _) = error "invalid operator"
getInfoCarga (Leaf operator _) = (operator, Nothing, Nothing)

isLeaf :: Node -> Bool
isLeaf (Leaf {}) = True
isLeaf _ = False

type Carga = [Maybe (Node, IsNegated)]

pegarCarga :: Node -> (String, Maybe Node, Maybe Node)
pegarCarga (BinaryOperation operator left right _) =
  (operator, Just left, Just right)
pegarCarga (Leaf operand _) = (operand, Nothing, Nothing)
pegarCarga (UnaryOperation operator operand hasParens) =
  (operator, Just operand, Nothing)

getOperandFromLeaf :: Node -> String
getOperandFromLeaf (Leaf operand _) = operand
getOperandFromLeaf _ = error "not leaf"

createRefutationNode
  :: Maybe Node -> IsNegated -> Carga -> Maybe RefutationNode
createRefutationNode Nothing _ _ = Nothing
createRefutationNode
  (Just (UnaryOperation operator operand _))
  isNegated
  unappliedRule =
  createRefutationNode (Just operand) (xor True isNegated) unappliedRule
createRefutationNode (Just (Leaf operand _)) isNegated carga
  | null carga = Just (RefLeaf operand Terminal isNegated Nothing Nothing)
  | otherwise = do
    let currentCarga = head carga
    let (nodeCarga, isCargaNegated) =
          fromMaybe (error "Carga Invalida") currentCarga
    let (operator, left, right) = pegarCarga nodeCarga
    let (tipo, isLeftNegated, isRightNegated) =
          getTypeData operator isCargaNegated
    Just
      (RefLeaf
         operand
         tipo
         isNegated
         (createRefutationNode left isLeftNegated (tail carga))
         (createRefutationNode right isRightNegated (tail carga)))
createRefutationNode
  (Just (BinaryOperation operator operand1 operand2 hasParens))
  isNegated
  unappliedRule = do
  let (tipo, b1, b2) = getTypeData operator isNegated
  Just
    (RefNode
       (BinaryOperation operator operand1 operand2 hasParens) -- node
       tipo -- type
       isNegated -- isNegated
       (if (tipo /= Conjunction)
        then (createRefutationNode (Just operand1) b1 (unappliedRule))
        else (if (isLeaf operand1)
              then (Just
                      (RefLeaf
                         (getOperandFromLeaf operand1)
                         Terminal
                         b1
                         Nothing
                         Nothing))
              else Just (RefNode operand1 Terminal b1 Nothing Nothing)))
        -- refutation node 1
       (createRefutationNode
          (Just operand2)
          b2
          (if tipo == Conjunction
           then (unappliedRule ++ [Just (operand1, b1)])
           else unappliedRule)) -- refutation node 2
     )

createRefutationTree :: Node -> Maybe RefutationNode
createRefutationTree arvore = createRefutationNode (Just arvore) False []

type FoundContradiction = Bool

type VariableList = [(String, IsNegated)]

isRefLeaf :: RefutationNode -> Bool
isRefLeaf (RefLeaf {}) = True
isRefLeaf _ = False

getVariableRefLeaf :: Maybe RefutationNode -> [(String, IsNegated)]
getVariableRefLeaf (Just (RefLeaf operand _ isNegated _ _)) =
  [(operand, isNegated)]
getVariableRefLeaf _ = []

refuta :: VariableList -> Maybe RefutationNode -> FoundContradiction
refuta _ Nothing = False
refuta _ (Just (RefNode _ Terminal _ _ _)) = False
refuta variaveis (Just (RefNode node tipo isNegated left right))
  | tipo == Dysjunction = ((refuta variaveis left) && (refuta variaveis right))
  | tipo == Conjunction = do
    let varLeft = getVariableRefLeaf left
    let [(operand, isOperandNegated)] = if (not (null varLeft))
                                        then varLeft
                                        else [("", False)]
    let valorRecebido = lookup operand variaveis
    if (isNothing valorRecebido
        || ((isJust valorRecebido) && (valorRecebido == Just isOperandNegated)))
      then (refuta (variaveis ++ varLeft) right)
      else True
refuta [] (Just (RefLeaf valor tipo isNegated left right))
  | tipo == Terminal = False
  | tipo == Dysjunction =
    (refuta [(valor, isNegated)] left && refuta [(valor, isNegated)] right)
  | tipo == Conjunction = do
    let varLeft = getVariableRefLeaf left
    let [(operand, isOperandNegated)] = if (not (null varLeft))
                                        then varLeft
                                        else [("", False)]
    if (valor == operand && isNegated /= isOperandNegated)
      then True
      else (refuta ((valor, isNegated):varLeft) right)
refuta variaveis (Just (RefLeaf valor tipo isNegated left right))
  | tipo == Terminal = do
    let valorRecebido = lookup valor variaveis
    if (isNothing valorRecebido
        || ((isJust valorRecebido) && (valorRecebido == Just isNegated)))
      then False
      else True
  | tipo == Dysjunction = do
    let valorRecebido = lookup valor variaveis
    if (isNothing valorRecebido
        || ((isJust valorRecebido) && (valorRecebido == Just isNegated)))
      then (refuta (variaveis ++ [(valor, isNegated)]) left
            && refuta (variaveis ++ [(valor, isNegated)]) right)
      else True
  | tipo == Conjunction = do
    let valorRecebido = lookup valor variaveis
    if (isNothing valorRecebido
        || ((isJust valorRecebido) && (valorRecebido == Just isNegated)))
      then (refuta
              (variaveis ++ [(valor, isNegated)] ++ getVariableRefLeaf left)
              right)
      else True

printRefutationTree :: Maybe RefutationNode -> String
printRefutationTree (Just node) = go node 0
  where
    go (RefNode node t isNeg left right) indent =
      replicate (indent*2) ' ' ++ (if isNeg then "[f] - " else "[v] - ") ++ printSyntaxTree node ++ " (" ++ show t ++ ")\n" ++
      maybe "" (\n -> go n (indent + 2)) left ++
      maybe "" (\n -> go n (indent + 2)) right
    go (RefLeaf operand t isNeg left right) indent =
      replicate (indent*2) ' ' ++ (if isNeg then "[f] - " else "[v] - ") ++ operand ++ " (" ++ show t ++ ")\n" ++
      maybe "" (\n -> go n (indent + 2)) left ++
      maybe "" (\n -> go n (indent + 2)) right
printRefutationTree Nothing = "Nothing"

--------------------------------------------------------------------------------

equation :: String
equation = "(p | (q & r)) -> ((p | q) & (p | r))" :: String

-- equation = "a|~a" -- expected: True

-- equation = "(a->b)&a"

-- equation = "(p -> q)" :: String

main :: IO ()
main = do
  -- input <- getLine
  let arvore = negateNode (createSyntaxTree equation)
  print (printSyntaxTree arvore)
  let refutationTree = createRefutationTree (arvore)
  case refutationTree of
    -- Nothing -> print ("Entrada Invalida")
    -- Just refutationTree -> print (show (refuta [] (Just refutationTree)))
    Nothing -> print ("Entrada Invalida")
    Just refutationTree -> putStr (printRefutationTree (Just refutationTree))
