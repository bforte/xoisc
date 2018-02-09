{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad
import Control.Monad.State as ST
import System.Console.GetOpt
import System.IO
import System.Environment
import Text.Parsec
import Text.Parsec.Expr
import Text.Read (readEither)


-- | Data type for untyped lambda calculus
data Exp = Var Integer | Lam Exp | App Exp Exp | X
  deriving Eq

-- | Infix operator for function application
(.$) = App

instance Show Exp where
  show (Var a) = show a
  show (Lam a@(App _ _)) = "λ(" ++ show a ++ ")"
  show (Lam a) = "λ" ++ show a
  show (App a b@(App _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show X = "X"

-- | Construct Church numeral
number :: Integer -> Exp
number n = Lam (Lam (foldr App (Var 1) [Var 2 | _ <- [1..n]]))

-- | Pattern match Booleans
toBool :: Exp -> Maybe Bool
toBool exp
  | exp == number 0  = Just False
  | exp == toExp 'K' = Just True
  | otherwise = Nothing

-- | Pattern match Church numerals
toNum :: Exp -> Maybe Integer
toNum = go.simplify
  where go (Lam (Lam (Var 1))) = Just 0
        go (Lam (Lam (App (Var 2) x))) = go x
          where go (Var 1) = Just 1
                go (App (Var 2) x) = (1+) <$> go x
                go _ = Nothing
        go _ = Nothing

-- | Reduce Lambda terms in normal-order until the term doesn't simplify further
simplify :: Exp -> Exp
simplify e
  | e' == e   = e
  | otherwise = simplify e'
  where e' = go e
        go (Lam a) = Lam $ go a
        go (App (Lam a) b) = betaReduce a b
        go (App a b) = App (go a) (go b)
        go e = e

        betaReduce a b = sub 1 b a
          where sub n a (Var b)
                  | n == b = a
                  | n <  b = Var $ b-1
                  | otherwise = Var b
                sub n a (Lam b) = Lam $ sub (n+1) (incFree 0 a) b
                sub n a (App b c) = App (sub n a b) (sub n a c)
                sub _ _ X = X

                incFree n (Var a)
                  | n < a = Var $ a+1
                  | otherwise = Var a
                incFree n (Lam a) = Lam $ incFree (n+1) a
                incFree n (App a b) = App (incFree n a) (incFree n b)
                incFree _ X = X


-- | Parse arguments and source, evaluate program and print results
runSrc :: Bool -> [String] -> String -> IO ()
runSrc bool as e = withRight (zipWithM parseInput [0..] as) $ \inputs ->
  withRight (mapM readEither $ words e) $ \prog -> do
    let stack = reverse inputs ++ execState (mapM_ evalInstr prog) []
        exp = simplify $ foldr (flip App) (Lam $ Var 1) stack
        typ | bool      = maybe "" (tstr "Boolean") (toBool exp)
            | otherwise = maybe "" (tstr "Church numeral") (toNum exp)
    hPutStrLn stderr "Final stack: "
    mapM_ (hPutStrLn stderr.show') stack
    putStrLn $ "Final expression: " ++ show exp ++ typ

  where tstr t n = " (" ++ t ++ ": " ++ show n ++ ")"
        show' (App a b@(App _ _)) = show' a ++ " (" ++ show' b ++ ")"
        show' (App a b) = show' a ++ " " ++ show' b
        show' l@(Lam _)
          | l == toExp 'X' = "X"
          | otherwise      = show l
        show' x = show x

-- | Evaluate a single instruction
evalInstr :: Int -> ST.State [Exp] ()
evalInstr n = do
  (top,bot) <- splitAt n <$> get
  put $ foldl (flip App) (toExp 'X') top : bot

-- | Either fail or do something with value
withRight :: Either String a -> (a -> IO b) -> IO b
withRight e f = either (ioError.userError) f e

-- | Parse a number or function - used for command-line inputs
parseInput :: Int -> String -> Either String Exp
parseInput n = either (Left . show) Right . parse inputP ("input" ++ show n)
  where inputP = spaced (number <$> intP <|> expP) <* eof

        expP  = spaced $ buildExpressionParser [[Infix appP AssocLeft]] atomP
        atomP =  varP
             <|> lamP
             <|> toExp <$> oneOf (fst <$> combinators)
             <|> between (char '(') (char ')') (spaced expP)

        appP = many1 space *> return App
        varP = Var <$> intP
        lamP = Lam <$> (oneOf "λ\\" *> atomP)

        intP = read <$> many1 digit

        spaced :: Parsec String () a -> Parsec String () a
        spaced p = spaces *> p <* spaces

-- | Built-in combinators for parsing
combinators :: [(Char,Exp)]
combinators = [ ('S', Lam . Lam . Lam $ Var 3 .$ Var 1 .$ (Var 2 .$ Var 1))
              , ('K', Lam . Lam $ Var 2)
              , ('I', Lam $ Var 1)
              , ('X', Lam $ Var 1 .$ toExp 'S' .$ (Lam . Lam . Lam $ Var 3))
              ]

toExp :: Char -> Exp
toExp c = snd . head $ filter ((c==).fst) combinators


-- | Parse an expression and convert to a program (first 2 arguments ignored)
asm :: Bool -> [String] -> String -> IO ()
asm _ _ = either (hPutStrLn stderr)
               (putStrLn . unwords . map show . convertXs . toXs) . parseInput 0
  where
    toXs = go
      where go l@(Lam a)
              | notFree a = X .$ X .$ go (unLambda a)
              | otherwise = case a of
                  Var 1   -> X .$ (X .$ X) .$ (X .$ X) .$ (X .$ X)
                  Var _   -> error "won't happen"
                  Lam b   -> go . Lam . go $ Lam b
                  App b c -> X .$ (X .$ X) .$ go (Lam b) .$ go (Lam c)
                  _ -> l
            go (App a b) = go a .$ go b
            go a = a

    notFree = go 1
      where go n (Var i) = i /= n
            go n (Lam a) = go (n+1) a
            go n (App a b) = go n a && go n b
            go _ _ = True

    unLambda = go 1
      where go n v@(Var i)
              | n <= i    = Var (i-1)
              | otherwise = v
            go n (Lam a)  = Lam (go (n+1) a)
            go n (App a b)= App (go n a) (go n b)
            go _ x = x

    convertXs = go 0
      where go n (App a b) = go 0 a ++ go (n+1) b
            go n X = [n]
            go _ _ = error "won't happen"


-- | Parse command-line arguments and let the fun begin
main :: IO ()
main = getOpt Permute options <$> getArgs >>= \case
  (args,rem,[]) -> evalOpts (foldr ($) (runSrc,Nothing,False) args) rem
  (_,_,err)     -> die (concat err)

  where options = [ Option "e" ["expr"] (ReqArg setExpr "EXPR") "specify source"
                  , Option "a" ["asm"] (NoArg setAsm) "translate expression to source"
                  , Option "b" ["bool"] (NoArg setBool) "interpret output type as a boolean"
                  ]
        setAsm (_,s,b) = (asm,s,b)
        setBool (f,s,_) = (f,s,True)
        setExpr s (f,_,b) = (f,Just s,b)

        die s   = ioError.userError $ s ++ "\n" ++ usageInfo usage options
        usage   = "usage: xoisc [-a | -b] [-e EXPR | FILE] [INPUTS]\n"

        evalOpts (f,Just e,b) as      = f b as e
        evalOpts (f,Nothing,b) (a:as) = openFile a ReadMode >>= hGetContents >>= f b as
        evalOpts _ _                  = die "argument FILE required\n"
