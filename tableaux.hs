import Data.Binary (Binary)
import Data.Char (isAlpha, isSpace)
import Data.List (find, isPrefixOf, stripPrefix)
import Data.Maybe
import Language.Haskell.TH.Ppr (hashParens)

operators :: [String]
operators = ["&", "|", "~", "->", "<->"]

type HasParens = Bool

type Operator = String

data Node
  = BinaryOperation Operator Node Node HasParens
  | UnaryOperation Operator Node HasParens
  | Leaf String HasParens
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
takeInsideParens string = tail (take (length string - length (takeRestAfterParens string) - 1) string)

startsWithOperator :: String -> Bool
startsWithOperator s = not (null s) && any (`isPrefixOf` s) operators

getOperator :: String -> String
getOperator s = do
  let operator = find (`isPrefixOf` s) operators
  case operator of
    Just operator -> operator
    Nothing -> error "no operator found"

getAfterOperator :: String -> String -> String
getAfterOperator op s = do
  let rest = stripPrefix op s
  case rest of
    Just rest -> rest
    Nothing -> error "nothing found after operator"

createNodeFromStr :: String -> HasParens -> Node
createNodeFromStr e hasParens
  | head e == '~' = do
      let nextChar = head (tail e)
      let rest = tail (tail e)
      if isAlpha nextChar
        then
          if startsWithOperator rest
            then
              BinaryOperation
                (getOperator rest)
                (UnaryOperation "~" (createNodeFromStr [nextChar] False) hasParens)
                (createNodeFromStr (getAfterOperator (getOperator rest) rest) False)
                hasParens
            else UnaryOperation "~" (createNodeFromStr [nextChar] False) hasParens
        else
          if nextChar == '('
            then
              if startsWithOperator (takeRestAfterParens (tail e))
                then
                  BinaryOperation
                    (getOperator (takeRestAfterParens (tail e)))
                    (UnaryOperation "~" (createNodeFromStr (takeInsideParens (tail e)) True) hasParens)
                    (createNodeFromStr (getAfterOperator (getOperator (takeRestAfterParens (tail e))) (takeRestAfterParens (tail e))) False)
                    hasParens
                else UnaryOperation "~" (createNodeFromStr (takeInsideParens (tail e)) True) hasParens
            else Leaf "Invalid Operation" False
  | head e == '(' = do
      let rest = takeRestAfterParens e
      if startsWithOperator rest
        then
          BinaryOperation
            (getOperator rest)
            (createNodeFromStr (takeInsideParens e) True)
            (createNodeFromStr (getAfterOperator (getOperator rest) rest) False)
            hasParens
        else createNodeFromStr (takeInsideParens e) True
  | isAlpha (head e) = do
      let rest = tail e
      if startsWithOperator rest
        then
          BinaryOperation
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
  | hasParens = "(" ++ printSyntaxTree operand1 ++ operator ++ printSyntaxTree operand2 ++ ")"
  | not hasParens = printSyntaxTree operand1 ++ operator ++ printSyntaxTree operand2
printSyntaxTree (UnaryOperation operator operand hasParens)
  | hasParens = "(" ++ operator ++ printSyntaxTree operand ++ ")"
  | not hasParens = operator ++ printSyntaxTree operand
printSyntaxTree (Leaf operand hasParens)
  | hasParens = "(" ++ operand ++ ")"
  | not hasParens = operand

negateNode :: Node -> Node
negateNode (BinaryOperation operator operand1 operand2 hasParens) = UnaryOperation "~" (BinaryOperation operator operand1 operand2 True) False
negateNode (UnaryOperation operator operand hasParens) = operand -- can do that because negation is the only unary operation
negateNode (Leaf operand hasParens) = UnaryOperation "~" (Leaf operand hasParens) False

xor :: Bool -> Bool -> Bool
xor p q = (p && not q) || (not p && q)

-- type IsNegated = Bool

-- data LogicNode
--   = LogicOperation Operator Node Node HasParens IsNegated
--   | LogicLeaf String HasParens IsNegated

-- convertToLogicTree :: Node -> IsNegated -> LogicNode
-- convertToLogicTree (Leaf operand hasParens) isNegated = LogicLeaf operand hasParens (xor False isNegated)
-- convertToLogicTree (BinaryOperation operator operand1 operand2 hasParens) isNegated = LogicOperation operator operand1 operand2 hasParens (xor False isNegated)
-- convertToLogicTree (UnaryOperation operator operand hasParens) isNegated = convertToLogicTree operand (xor True isNegated)

-- caralho :: Bool -> Node -> Maybe Node -> Node
-- caralho taNegado node resto =

data Type = Dysjunction | Conjunction | Terminal
  deriving (Show, Eq)

getType :: Operator -> IsNegated -> Type
getType op isNeg
  | isNeg = case op of
      "->" -> Conjunction
      "&" -> Dysjunction
      "/" -> Conjunction
      _ -> Terminal
  | not isNeg = case op of
      "->" -> Dysjunction
      "&" -> Conjunction
      "/" -> Dysjunction
      _ -> Terminal

-- ESSES BOOLS AQUI NÃO SÃO SE TÁ NEGADO, SÃO O VALOR OFICIAL
getTypeData :: Operator -> IsNegated -> (Type, Bool, Bool)
getTypeData op isNeg
  | isNeg = case op of
      "->" -> (Conjunction, True, False)
      "&" -> (Dysjunction, False, False)
      "/" -> (Conjunction, False, False)
      _ -> (Terminal, False, False)
  | not isNeg = case op of
      "->" -> (Dysjunction, False, True)
      "&" -> (Conjunction, True, True)
      "/" -> (Dysjunction, True, True)
      _ -> (Terminal, False, False)

type IsNegated = Bool

data RefutationNode
  = RefNode Node Type IsNegated (Maybe RefutationNode) (Maybe RefutationNode)
  | RefLeaf String Type IsNegated (Maybe RefutationNode) (Maybe RefutationNode)
  deriving (Show, Eq)

getInfoCarga :: Node -> (Operator, Node, Node)
getInfoCarga (BinaryOperation operator first second _) = (operator, first, second)
getInfoCarga (UnaryOperation {}) = error "Invalid Node Type - Unary"
getInfoCarga (Leaf {}) = error "Invalid Node Type - Leaf"

isLeaf :: Node -> Bool
isLeaf (Leaf {}) = True
isLeaf _ = False

createRefutationNode :: Node -> Bool -> Maybe (Node, Bool) -> Maybe RefutationNode
createRefutationNode (UnaryOperation operator operand hasParens) isNegated unappliedRule = createRefutationNode operand (xor True isNegated) unappliedRule -- check
createRefutationNode (Leaf operand hasParens) isNegated carga
  | isNothing carga = Just (RefLeaf operand Terminal isNegated Nothing Nothing)
  | isJust carga =
      do
        ((operator, first, second), negadoCarga) <- case carga of
          Just (node, negadoCarga) -> return (getInfoCarga node, negadoCarga)
          Nothing -> error "Expected a Node, but got Nothing"
        Just (RefLeaf operand (getType operator negadoCarga) isNegated (createRefutationNode first False Nothing) (createRefutationNode second False Nothing))
createRefutationNode (BinaryOperation operator operand1 operand2 hasParens) isNegated unappliedRule = do
  let (tipo, b1, b2) = getTypeData operator isNegated
  let transferirCarga = tipo == Dysjunction && not (isLeaf operand1)
  Just
    ( RefNode
        (BinaryOperation operator operand1 operand2 hasParens) -- node
        tipo -- type
        (xor True isNegated) -- isNegated
        (createRefutationNode operand1 (not b1 && False) Nothing) -- refutation node 1
        (createRefutationNode operand2 (not b2 && False) (if transferirCarga then Just (operand1, not b1 && False) else Nothing)) -- refutation node 2
    )

printRefutationTree :: Maybe RefutationNode -> String
printRefutationTree (Just (RefNode node t isNeg esq dir)) = show (RefNode node t isNeg esq dir)

--------------------------------------------------------------------------------

equation :: String
-- equation = "(p | (q & r)) -> ((p | q) & (p | r))" :: String
equation = "(p -> q)" :: String

main :: IO ()
main = do
  let arvore = createSyntaxTree equation
  -- print (printSyntaxTree arvore)
  let refutationTree = createRefutationNode arvore False Nothing
  putStrLn (printRefutationTree refutationTree)
