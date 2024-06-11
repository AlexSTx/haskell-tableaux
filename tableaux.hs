import Data.Char (isAlpha, isSpace)
import Data.List (find, isPrefixOf, stripPrefix)
import Language.Haskell.TH.Ppr (hashParens)

operators :: [String]
operators = ["&", "|", "~", "->", "<->"]

type HasParens = Bool

type Operator = String

data Node
  = BinaryOperation Operator Node Node HasParens
  | UnaryOperation Operator Node HasParens
  | Leaf String HasParens

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

data RefutationNode = NodeC Node (Maybe RefutationNode) (Maybe RefutationNode) (Maybe RefutationNode) (Maybe RefutationNode)

createRefutationTree :: Node -> Bool -> Maybe RefutationNode
createRefutationTree (UnaryOperation operator operand hasParens) hasNot = createRefutationTree operand (xor True hasNot)
createRefutationTree (Leaf operand hasParens) hasNot
  | hasNot = Just (NodeC (negateNode (Leaf operand hasParens)) Nothing Nothing Nothing Nothing)
  | not hasNot = Just (NodeC (Leaf operand hasParens) Nothing Nothing Nothing Nothing)
createRefutationTree (BinaryOperation operator operand1 operand2 hasParens) hasNot
  | hasNot = case operator of
      "->" ->
        Just
          ( NodeC
              (negateNode (BinaryOperation operator operand1 operand2 hasParens))
              (createRefutationTree operand1 False)
              (createRefutationTree (negateNode operand2) False)
              Nothing
              Nothing
          )
      "&" ->
        Just
          ( NodeC
              (negateNode (BinaryOperation operator operand1 operand2 hasParens))
              Nothing
              Nothing
              (createRefutationTree (negateNode operand1) False)
              (createRefutationTree (negateNode operand2) False)
          )
      "|" ->
        Just
          ( NodeC
              (negateNode (BinaryOperation operator operand1 operand2 hasParens))
              (createRefutationTree (negateNode operand1) False)
              (createRefutationTree (negateNode operand2) False)
              Nothing
              Nothing
          )
      _ -> Nothing
  | otherwise = case operator of
      "->" ->
        Just
          ( NodeC
              (BinaryOperation operator operand1 operand2 hasParens)
              Nothing
              Nothing
              (createRefutationTree (negateNode operand1) False)
              (createRefutationTree operand2 False)
          )
      "&" ->
        Just
          ( NodeC
              (BinaryOperation operator operand1 operand2 hasParens)
              (createRefutationTree operand1 False)
              (createRefutationTree operand2 False)
              Nothing
              Nothing
          )
      "|" ->
        Just
          ( NodeC
              (BinaryOperation operator operand1 operand2 hasParens)
              Nothing
              Nothing
              (createRefutationTree operand1 False)
              (createRefutationTree operand2 False)
          )
      _ -> Nothing

instance Show Node where
  show (BinaryOperation operator operand1 operand2 hasParens) =
    if hasParens
      then "(" ++ show operand1 ++ operator ++ show operand2 ++ ")"
      else show operand1 ++ operator ++ show operand2
  show (UnaryOperation operator operand hasParens) =
    if hasParens
      then "(" ++ operator ++ show operand ++ ")"
      else operator ++ show operand
  show (Leaf operand hasParens) =
    if hasParens
      then "(" ++ operand ++ ")"
      else operand

instance Show RefutationNode where
  show (NodeC node left right third fourth) =
    "NodeC ("
      ++ show node
      ++ ") "
      ++ "("
      ++ show left
      ++ ") "
      ++ "("
      ++ show right
      ++ ") "
      ++ "("
      ++ show third
      ++ ") "
      ++ "("
      ++ show fourth
      ++ ")"

-- criando funcao que vai pegar todos os valores de nós folha da operação 1 para comparar com folhas da op 2
-- takeAndCompare :: Node -> Bool -> Node

-- \| not hasNot = Case operator of
-- NodeC Operator (AND node) (AND node) (OR node) (OR node) HasParen
--------------------------------------------------------------------------------

equation :: String
equation = "(p | (q & r)) -> ((p | q) & (p | r))" :: String

main :: IO ()
main = do
  -- print (trimm equation)
  let arvore = createSyntaxTree equation
  -- print (printSyntaxTree arvore)
  let refutationTree = createRefutationTree arvore False
  print refutationTree