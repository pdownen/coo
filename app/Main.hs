module Main (main) where

import Coo.REPL.Inside
import Data.Char (toLower)
import Data.Maybe (isNothing)
import Options.Applicative
import Prettyprinter

main :: IO ()
main = do
  opts <- execParser cli
  let initOpts = RO{ typeOption = initTypeOption opts,
                     stopAfterTypes = checkOnly opts,
                     batchOption = not $ isNothing $ scriptFile opts,
                     showInternals = if dumpCore opts
                                     then ShowInternals
                                     else HideInternals }
  case scriptFile opts of
    Nothing   -> do putStrLn "Coo!    (feel free to ask for #help)"
                    replTopWith initOpts initCmd
    Just file -> do runScript initOpts file
                    return ()

data CommandOptions = CmdOpt
  { scriptFile :: Maybe FilePath,
    initTypeOption :: TypeCheckingOption,
    checkOnly :: Bool,
    dumpCore :: Bool }
  deriving (Show, Eq)

cli :: ParserInfo CommandOptions
cli = info
  (commandOptions <**> helper)
  (fullDesc
  <> header "coo - a friendly little language to talk about co things"
  <> progDescDoc (Just description))
  where description = vsep $ pretty <$>
          [ "Run coo code in one of two ways:",
            "1. If no FILE is given, start the interactive interpreter.",
            "2. If FILE is given, interpret and run its contents, then exit." ]

commandOptions :: Parser CommandOptions
commandOptions =  CmdOpt
              <$> optional cliScriptFile
              <*> cliTypeOpt
              <*> cliCheckOpt
              <*> cliDumpOpt

cliScriptFile :: Parser String
cliScriptFile = argument str
              $ metavar "FILE"

cliTypeOpt :: Parser TypeCheckingOption
cliTypeOpt = option (eitherReader readTyOpt)
           $  long "type"
           <> short 't'
           <> metavar "MODE"
           <> value IgnoreTypes
           <> help "static type checking mode: ignore, warning, error"
  where readTyOpt str = case map toLower str of
          "ignore" -> Right IgnoreTypes
          "warn" -> Right TypeWarnings
          "error" -> Right TypeErrors
          _ -> Left $ "`" ++ str ++ "` is not a type checking mode: ignore, warning, error"

cliCheckOpt :: Parser Bool
cliCheckOpt = switch
            $  long "check"
            <> short 'c'
            <> help "only check types, do not run (implies --type=warn)"

cliDumpOpt :: Parser Bool
cliDumpOpt = switch
           $ long "dumpdc"
           <> short 'd'
           <> help "dump internal Dual Core representations"
