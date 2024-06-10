import Data.Char (isAlpha, isSpace)
import Data.List (find, isPrefixOf, stripPrefix)
import Debug.Trace
import Language.Haskell.TH.Ppr (hashParens)
import System.Console.Terminfo (restoreDefaultColors)

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

-- TODO: create guard function for this
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

--------------------------------------------------------------------------------

equation :: String
equation = "~(p | (q & r)) -> ((p | q) & (p | v))" :: String


--1. quebrar a stringzona em vários nós folha para fazer a refutação add a mais na árvore
--2. busca por profundidade até achar tabela v f

depthSearch :: Node -> [String]
depthSearch (Leaf e hashParens) = [e]
depthSearch (UnaryOperation op node hasParens) = [op] ++ depthSearch node
depthSearch (BinaryOperation op left right hasParens) = [op] ++ depthSearch left ++ depthSearch right


-- eq "~(p|(q&r))->((p|q)&(p|v))"
-- ["->","~","|","p","&","q","r","&","|","p","q","|","p","v"]

valida :: Node -> [Bool]
valida (Leaf _ _) = [True]
valida (UnaryOperation "~" node _) = False : valida node 
valida (BinaryOperation op left right _) =
  case op of
    "&"   -> (False : valida left) ++ (False : valida right) 
    "|"   -> (False : valida left) ++ (False : valida right) 
    "->"  -> (True : valida left) ++ (False : valida right)
    "<->" -> (False : valida left) ++ (False : valida right) 
    _     -> error "Operador desconhecido" 

a = "p->p"



main :: IO ()
main = do
  print (trimm equation)
  let arvore = createSyntaxTree a
  let arvore_validacao = createSyntaxTree equation 
  print (printSyntaxTree arvore)

  let result = depthSearch arvore
  putStrLn "Result Depth-Search:"
  print result

  let testevalid = valida arvore
  print (valida arvore)
  