-- Homework 6
-- main

-- how to run
-- $ ghc -o main main.hs
-- $ ./main test.TLBN

import System.IO (openFile, IOMode (ReadMode), hGetContents)
import System.Environment (getArgs)
import Text.ParserCombinators.Parsec
import Data.Monoid
import Data.Either.Unwrap (fromRight)
import AbstractSyntax
import Parser
import Evaluation
import Unification
import ConstraintTyping

parseFile filePath = do
	file <- openFile filePath ReadMode
	text <- hGetContents file
	return (fromRight $ parse parserTerm filePath text)

main = do

	args <- getArgs
	let firstarg = head args
	parseResult <- parseFile firstarg

	putStrLn "---Term:---"
	let parseTerm = fromJust $ reconstructType parseResult
	-- fromRight is used to grab the value out of a Right Value (recall fromMaybe)
	print parseTerm
	
	putStrLn "--Type:--"
	let termType = detType Empty parseTerm
	print termType

	putStrLn "--Normal Form:--"
	let evalResult = eval Empty parseTerm
	print evalResult



