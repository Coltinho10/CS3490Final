import Data.List
import Data.Char

{-
	Author: Colton Bailey
	Last Update: May 2nd, 2021

	This is a Search-and-Replace program. The main purpose of this program is to search a file
	and replace a specified String with another with the assistance of regular expressions.
-}

{-
	The Reg datatype allows us to utilize regular expressions with search-and-replace. The types are listed below:
	Letter: Type Char and represents single characters. (ex. ‘a’)
	Choice: Resembles the way the program picks one Reg over another. (ex. ab+cd)
	Concat: Represents the concatenation of two regular expressions. (ex. (a+b)(c+d))
	Seq: Represents a sequence of a String. (ex. “ab”)
	Range: Represents a combination of characters within a String (not concatenated)
	Lam: Representation for Lambda expressions
	Save: Allows for saving a regular expression within a file
	Empty: Representation for empty expressions
	Star: Represents the “*” character also commonly found in regular expressions. (ex. c*)
-}
data Reg = Letter Char | Choice Reg Reg | Concat Reg Reg
                       | Lam | Empty | Star Reg | Save (Reg)
                       | Seq String  | Range String
    deriving Show

{-
	The Token datatype allows us to use the various tokens that are in regular expressions. The types are listed below:

	LPar: Represents the ‘(‘ character.
	RPar: Represents the ‘)’ character.
	SStar: Represents the ‘*’ character.
	PR: Connects the Token to the Reg datatype.
	VSym: Helps differentiate between Range and Seq from Reg.
	LSym: Represents Letter from Reg.
	RSym: Helps differentiate between Range and Seq from Reg.
	SeqToken: Represents Seq from Reg.
	OpChoice: Represents the ‘+’ character.
	OpConcat: Represents the equivalent of Concat in Reg. (ex. ()())
	OpLam: Represents Lambda from Reg.
	OpEmpty: Represents Empty from Reg.
	RBrace: Represents the ‘]’ character.
	LBrace:Represents the ‘[‘ character.
-}
data Token = LPar | RPar | SStar | PR Reg | VSym String | LSym Char
                  | RSym String | SeqToken String | OpChoice | OpConcat | OpLam
                  | OpEmpty | RBrace | LBrace
  deriving Show


-- Matches a regular expression against a String and returns True if they match and False otherwise.
match :: Reg -> String -> Bool
match (Letter l) (z:[]) | l == z = True
match (Letter l) _ = False
match (Choice r1 r2) z = match r1 z || match r2 z
match (Concat r1 r2) z =
            let list = combs z
                predicate (x,y) = match r1 x && match r2 y
            in any predicate list
match Lam z = z == ""
match Empty z = False
match (Star r) "" = True
match (Star r1) s = matchHelper r1 (Star r1) (combs s)
match (Save r) z = match r z
match (Seq s) z = s == z
match (Range r) (z:[]) = z `elem` r
match (Range r) (z:zs) = z `elem` r
match (Range r) _ = False


-- Generates a regular expression as a String given a regular expression and a String as input.
generate :: Reg -> String -> String
generate _ "" = ""
generate (Letter l) p@(z:zs) = if l == z then zs else p
generate (Choice r1 r2) z =
              let a = (generate r1 z)
                  b = (generate r2 z)
              in if length a > length b then b else a
generate (Concat r1 r2) z =
              let a = (generate r1 z)
                  b = (generate r2 a)
              in if (a /= z) then b else a
generate Lam z = z
generate Empty z = []
generate (Star r) z =
              let a = (generate r z)
                  b = (generate r a)
              in if a == b then a
              else (generate (Star r) b)
generate (Seq s) p@(z:zs) = if s `isPrefixOf` p then snd(splitAt(length(s))p) else p
generate (Range r) p@(z:zs) = if r `isPrefixOf` p then snd(splitAt(length(r))p) else p




-- Helper Functions

-- Checks whether or not a String exists.
exists' :: String -> Bool
exists' [] = False
exists' [x] = True
exists' (x:xs) = True


-- Combs through a String and puts it into a list like so: [("","ab"),("a","b"),("ab","")]
combs :: String -> [(String, String)]
combs "" = [("","")]
combs x = zip (inits x) (tails x)


-- A helper function to assist match with calculations.
matchHelper :: Reg -> Reg -> [(String, String)] -> Bool
matchHelper r1 r2 [] = False
matchHelper r1 r2 ((z1,z2):zs)
   | z1 /= "" && match r1 z1 && match r2 z2     = True
   | otherwise                                  = matchHelper r1 r2 zs


-- The shift reduce function. It takes two token lists and reduces them into one.
sr :: [Token] -> [Token] -> [Token]
sr (SeqToken s : LBrace : stack) (RBrace : input) = sr (PR (Seq s) : stack) input
sr (RPar : (PR r1) : LPar : stack)      input = sr ((PR r1) : stack) input
sr (LPar : (PR r1) : RPar : stack)      input = sr ((PR r1) : stack) input
sr (RBrace : (PR r1) : LBrace : stack)      input = sr ((PR r1) : stack) input
sr (LBrace : (PR r1) : RBrace : stack)      input = sr ((PR r1) : stack) input
sr (VSym v : stack) input = sr (PR (Seq v) : stack) input
sr (LSym c : stack) input = sr (PR (Letter c) : stack) input
sr (RSym r : stack) input = sr (PR (Range r) : stack) input
sr (PR r1 : PR r2 : stack) input = sr (PR (Concat r1 r2) : stack) input
sr (PR r1 : OpChoice : PR r2 : stack) input = sr (PR (Choice r1 r2) : stack) input
sr (PR r : SStar : stack) input = sr (PR (Star r) : stack) input
sr (SeqToken s : stack) input = sr (PR (Seq s) : stack) input
sr (OpLam : stack) input = sr (PR (Lam) : stack) input
sr stack (i : input)     = sr (i : stack) input
sr stack [] = stack


-- Adds space to the front and end of specified characters.
addSpaces :: String -> String
addSpaces "" = ""
addSpaces ('*' : s) = " * " ++ addSpaces s
addSpaces ('+' : s) = " + " ++ addSpaces s
addSpaces ('(' : s) = " ( " ++ addSpaces s
addSpaces (')' : s) = " ) " ++ addSpaces s
addSpaces ('[' : s) = " [ " ++ addSpaces s
addSpaces (']' : s) = " ] " ++ addSpaces s
addSpaces (x : s) = x : addSpaces s


-- Classifies certain characters as their respective tokens.
classify :: String -> Token
classify "(" = LPar
classify ")" = RPar
classify "[" = LBrace
classify "]" = RBrace
classify "+" = OpChoice
classify "*" = SStar
classify "" = OpLam
classify [s] | isLSym s = LSym s
classify (x:xs:xss) | isSlash x = LSym xs
classify s | isSeq s = SeqToken s
classify s | isVSym s = VSym s
classify _  = OpEmpty


-- Checks if a character is of type LSym.
isLSym :: Char -> Bool
isLSym x = ('A' <= x && x <= 'Z') || ('a' <= x && x <= 'z')
           || ('0' <= x && x <= '9')


-- Checks if a character is a double backslash.
isSlash :: Char -> Bool
isSlash x = if x == '\\' then True else False


-- Checks if a character is of type VSym.
isVSym :: String -> Bool
isVSym "" = False
isVSym (x:xs) = isLower x && q1 xs
  where q1 "" = True
        q1 (y:ys) = (isAlpha y || isDigit y || y `elem` "-_'") && q1 ys


-- Checks if a character is of type RSym.
isRSym :: String -> Bool
isRSym "" = False
isRSym x = if "[" `isPrefixOf` x && "]" `isSuffixOf` x then True else False


-- Returns RSym without the braces.
getRSym :: String -> String
getRSym x =
      let a = delete '[' x
          b = delete ']' a
      in if "[" `isPrefixOf` x && "]" `isSuffixOf` x then b else x


-- Checks if a character is of type Seq.
isSeq :: String -> Bool
isSeq "" = False
isSeq x = if not ("[" `isPrefixOf` x || "]" `isSuffixOf` x) then True else False


-- Returns Seq given a list of Strings into a condensed String.
getSeq :: [String] -> String
getSeq [] = []
getSeq p@(x:xs) =
          let z = (takeWhile isVSym p)
          in flatten (z)


-- Checks if a character is a LBrace.
isBrace :: String -> Bool
isBrace x = if "[" `isPrefixOf` x then True else False


-- Flattens a list of Strings into a single String.
flatten :: [String] -> String
flatten [] = []
flatten (x:xs) = x ++ flatten xs


-- Parses a list of tokens. (ex. test -> [PR (Concat (Choice (Seq "ab") (Seq "ac")) (Choice (Seq "bd") (Letter 'd')))])
parse :: [Token] -> [Token]
parse input = sr [] (reverse input)


-- Converts a given String into a list of tokens. (ex. ab+c* -> [SeqToken "ab",OpChoice,LSym 'c',SStar])
lexer :: String -> [Token]
lexer s = map classify (words (addSpaces s))


-- Converts a list of tokens into a regular expression. (ex. test -> Concat (Choice (Letter 'd') (Seq "bd")) (Choice (Seq "ac") (Seq "ab")))
tokenToReg :: [Token] -> Reg
tokenToReg [] = Lam
tokenToReg input = case sr [] input of
  [PR r] -> r
  ps -> error ("No parse:" ++ show ps)


-- Replaces a String in a regular expression with another String.
replace :: Reg -> String -> String -> String
replace r s1 file = if (search r file) then s1 else file


-- Searches a regular expression for a certain String and returns True if it is present and False otherwise.
search :: Reg -> String -> Bool
search target file = if (generate target file == "") then True else False


-- The main function.
main :: IO ()
main = do
   putStrLn "Input Filename"
   filename <- getLine
   contents <- readFile filename
   putStrLn "Input target string to search file for"
   target   <- getLine
   putStrLn "Input the string you want to replace it with"
   replacement <- getLine
   let file = lexer target
   let fileReg = tokenToReg file
   let searched = search fileReg target
   let replaced = replace fileReg replacement contents
   putStrLn "Results of search"
   putStrLn (replaced)




-- Test cases

ex :: Reg -- file[0-9].png
ex = (Concat (Seq "file") (Concat (Star (Range "0123456789")) (Seq ".png")))

ex2 :: Reg -- ab + c*a
ex2 = (Choice (Concat (Letter 'a') (Letter 'b')) (Concat (Star (Letter 'c')) (Letter 'a')))

ex3 :: Reg -- (ab+ac)(bd+d)
ex3 = (Concat (Choice (Seq "ab") (Seq "ac")) (Choice (Seq "bd") (Letter 'd')))

test :: [Token] -- [LPar,SeqToken "ab",OpChoice,SeqToken "ac",RPar,LPar,SeqToken "bd",OpChoice,LSym 'd',RPar]
test = lexer "(ab+ac)(bd+d)"

test2 :: [Token] -- [SeqToken "ab",OpChoice,LSym 'c',SStar]
test2 = lexer "ab+\\c*"

test3 :: [Token] -- [LPar,SeqToken "ab",RPar,LPar,SeqToken "cd",RPar]
test3 = lexer "(ab)(cd)"

test4 :: [Token] -- [SeqToken "file",LBrace,SeqToken "123",RBrace]
test4 = lexer "file[123]"
