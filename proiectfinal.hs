import System.IO  
import Control.Monad
import Data.Bits


--TOKENIZER
nbr :: Char -> Bool
nbr c = elem c "0123456789."

digit :: Char -> Bool
digit c = elem c "0123456789"

symbol :: Char -> Bool
symbol c = elem c "-+*/abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

var :: Char -> Bool
var c = elem c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

isSymbol :: String -> Bool
isSymbol = all symbol

isVariable :: String -> Bool
isVariable x = (all var x) && x /= "let" && x /= "in"

isNumber :: String -> Bool
isNumber [] = False
isNumber (x:xs) = (all nbr xs) && digit x

isNegNumber :: String -> Bool
isNegNumber (x:xs) = x == '-' && isNumber xs && xs /= []


tokenize :: String -> [String]
tokenize [] = []
tokenize (x:xs)
  | x == '(' = [x] : tokenize xs
  | x == ')' = [x] : tokenize xs
  | nbr x = tokenizeNr (x:xs) ""
  | symbol x = tokenizeS (x:xs) ""
  | otherwise = tokenize xs

tokenizeNr :: String -> String -> [String]
tokenizeNr [] formedNumber = [formedNumber]
tokenizeNr (x:xs) formedNumber
  | nbr x = tokenizeNr xs (formedNumber ++ [x])
  | otherwise = formedNumber : tokenize (x:xs) --de ex daca are un input prost gen 15s sa dau eroare sau interpretez ca 2 chestii dif

tokenizeS :: String -> String -> [String]
tokenizeS [] formedSymbol = [formedSymbol]
tokenizeS (x:xs) formedSymbol
  | symbol x = tokenizeS xs (formedSymbol ++ [x])
  | otherwise = formedSymbol : tokenize (x:xs)


--INTERPRETOR

type Ident = String --variabila nume

data Expr = Number Double           --expresie care poate fi functie sau let sau expr matem
               | Plus [Expr]
               | Minus [Expr]
               | Mul [Expr]
               | Div [Expr]
               | Var Ident
               | Let Ident Expr Expr
               | Lambd [Ident] Expr
               | Apply Expr [Expr]
               deriving Show
-- fib 10 :: Apply (Lam ["n"] ..) [Number 10] -- evaluation of a function
-- \x y -> x + y :: Lam ["x", "y"] (Plus (Var "x") (Var "y"))
data Value = NumVal Double | Closure [Ident] Expr Env --closure este o functie/lambda care se foloseste de o variabila bounded in afara functiei
           deriving (Show)

type Env = [(Ident, Value)] --retinem tuple de variabile cu valorile lor in mediul in care lucram

eval :: Expr -> Env -> Value --o expresie trebuie evaluata intr-un mediu si va avea o valoare
eval (Number i)    env = NumVal i
eval (Plus e1)     env = plus' e1 env
eval (Minus e1)    env = minus' e1 env
eval (Mul e1)      env = mul' e1 env
eval (Div e1)      env = div' e1 env
eval (Var i)       env = find env i
eval (Let i e1 e2) env = eval e2 (elab env i e1)
eval (Lambd ids e) env = Closure ids e env
eval (Apply f xs)  env = apply f' xs'
    where f' = eval f env
          xs'= map (flip eval env) xs --vezi ce face flip

plus':: [Expr]-> Env -> Value
plus' [] env     = (NumVal 0)
plus' (x:xs) env = let (NumVal n1) = eval x env in
                   let (NumVal n2) = plus' xs env in
                   NumVal (n1 + n2)
                   
minus'::[Expr]-> Env -> Value
minus' [] env     = (NumVal 0)
minus' (x:xs) env = let (NumVal n1) = eval x env in
                    let (NumVal n2) = plus' xs env in
                    NumVal (n1 - n2)
               
mul':: [Expr]-> Env -> Value
mul' [] env     = (NumVal 1)
mul' (x:xs) env = let (NumVal n1) = eval x env in
                  let (NumVal n2) = mul' xs env in
                  NumVal (n1 * n2)
                   
div':: [Expr]-> Env -> Value
div' [] env     = (NumVal 1)
div' (x:xs) env = let (NumVal n1) = eval x env in
                  let (NumVal n2) = mul' xs env in
                  NumVal (n1 / n2)

apply :: Value -> [Value] -> Value

apply (Closure ids e env) vals = eval e (zip ids vals ++ env)


find env i = snd $ head $ filter (\(i',_) -> i == i') env 

elab env i e = (i, eval e env) : env --adauga inca o variabila la environment


--Adaugare token-uri in arbore de tip AST

data Tree a = Node a [Tree a] | EmptyTree
  deriving (Show)

instance Eq a => Eq (Tree a) where
    EmptyTree == EmptyTree = True
    EmptyTree == _         = False
    _         == EmptyTree = False
    Node x xs == Node y ys = (x == y) && xs == ys



brothers :: [String] -> [[String]] --pentru a crea copii unui nod, expresile din care se va evalua expresia parinte (Plus [Expr])
brothers [] = []
brothers (x:xs)
  |x == "(" = takeBracket (x:xs) 0 : brothers (elimBracket (xs) 1)
  |otherwise = [x] : brothers xs

elimBracket :: [String] -> Int -> [String]
elimBracket [] _ = []
elimBracket (x:xs) l
  |l == 0 = x:xs
  |x == "(" = elimBracket xs (l + 1)  
  |x == ")" = elimBracket xs (l - 1)
  |otherwise = elimBracket xs l

takeBracket :: [String] -> Int -> [String]
takeBracket [] _ = []
takeBracket (x:xs) l  
  |x == "(" = x: (takeBracket xs (l + 1) ) 
  |x == ")" = x: (takeBracket xs (l - 1) )
  |l == 0 = []
  |otherwise = x: (takeBracket xs l )
  
createTree :: [String] -> Tree String
createTree [] = EmptyTree
createTree (x:xs) 
  |isNumber x = Node x [EmptyTree]
  |isNegNumber x = Node x [EmptyTree]
  |x == "in" = createTree xs
  |isVariable x = Node x [EmptyTree]
  |x ==")" = createTree xs
  |x =="(" = createTree xs
  |isSymbol x = Node x (filter (/= EmptyTree) (map createTree (brothers xs)))
  |otherwise = EmptyTree
 

checkTree:: Tree String -> Bool
checkTree (Node "let" [(Node x1 x11), x2, x3]) = (isVariable x1) && (checkTree x2) && (checkTree x3)
checkTree (Node x [EmptyTree]) = (isVariable x) || (isNumber x) || (isNegNumber x)
checkTree (Node x []) = (isVariable x) || (isNumber x) || (isNegNumber x)
checkTree (Node x xs)
  |x == "+" = foldl (&&) True (map checkTree xs)
  |x == "-" = foldl (&&) True (map checkTree xs)
  |x == "*" = foldl (&&) True (map checkTree xs)
  |x == "/" = foldl (&&) True (map checkTree xs)
  |otherwise = False


createExprFromTree :: Tree String -> Expr
createExprFromTree (Node "let" [(Node x1 x11), (Node x2 x22), x3]) = Let x1 (Number $ (read x2 :: Double)) (createExprFromTree x3)
createExprFromTree (Node x xs)
  |isNumber x = Number $ (read x :: Double)
  |isNegNumber x = Number $ (read x :: Double)
  |isVariable x = Var x
  |x == "+" = Plus (map createExprFromTree xs)
  |x == "-" = Minus (map createExprFromTree xs)
  |x == "*" = Mul (map createExprFromTree xs)
  |x == "/" = Div (map createExprFromTree xs)

  

evalExpr::String -> Value
evalExpr x = eval (createExprFromTree.createTree.tokenize $ x) []



main = do  
        --let list = []
        handle <- openFile "arbore.lisp" ReadMode
        contents <- hGetContents handle
        --let singlewords = tokenize contents
        if checkTree.createTree.tokenize $ contents then
        	print (evalExpr contents)
        else
        	print "Not a good input"
        hClose handle  
