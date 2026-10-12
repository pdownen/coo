module Main (main) where

import Test.Hspec
import Test.Hspec.Core.Spec(SpecM(..))
import Control.Monad.IO.Class (liftIO)
import Control.Exception (try, IOException)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))

prefix :: FilePath
prefix = "test/case/"

main :: IO ()
main = do
  hspec (runTestCases allTestCases)
  let n = length allTestCases
  putStrLn $ unwords ["A total of", show n, "Coo programs have been evaluated."]

data TestCase = TC { testName :: String
                   , runsWell :: Bool
                   , wellTyped :: Bool
                   , dumpCore :: Bool }

allTestCases :: [TestCase]
allTestCases =
  [ TC { testName="hello",                  runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="abc",                    runsWell=True,  wellTyped=False, dumpCore=True  }
  , TC { testName="crash",                  runsWell=False, wellTyped=False, dumpCore=True  }
  , TC { testName="pairs-poly",             runsWell=True,  wellTyped=False, dumpCore=True  }
  , TC { testName="pairs-mono",             runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="pairs-wrong",            runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="abs",                    runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="match-loop",             runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="fact",                   runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="collatz",                runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="sum",                    runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="and-eager",              runsWell=False, wellTyped=True,  dumpCore=False }
  , TC { testName="and-lazy",               runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="map",                    runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="always",                 runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="count",                  runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="powers",                 runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="zigzag",                 runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="range",                  runsWell=True,  wellTyped=True,  dumpCore=True  }
  , TC { testName="sizing",                 runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="collecting",             runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="iterating",              runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="yielding",               runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="fast-product",           runsWell=True,  wellTyped=False, dumpCore=False }
  , TC { testName="safe-div",               runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="par-div",                runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="fizzbuzz",               runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="divide2",                runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="parsimonious-filter",    runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="prescient-filter-short", runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="prescient-filter-long",  runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="pigeons-short",          runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="pigeons-long",           runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="classical",              runsWell=True,  wellTyped=True,  dumpCore=False }
  , TC { testName="mispolar",               runsWell=False, wellTyped=False, dumpCore=True  }
  , TC { testName="type-polarity-mismatch", runsWell=True,  wellTyped=False, dumpCore=True  }

  -- The following is an intentionally broken test case, because the expected
  -- outputs are wrong/missing.  Uncomment to detect a broken test case.
  
  -- , TC { testName="broken-test",            runsWell=True,  wellTyped=True,  dumpCore=True  }
  ]

runTestCases :: [TestCase] -> Spec
runTestCases []       = return ()
runTestCases (tc:tcs) = do
  runTestCase tc
  runTestCases tcs

runTestCase :: TestCase -> Spec
runTestCase tc = do
  describe (testName tc ++ ".coo") $ do
    runUntypedTestCase tc
    runTypedTestCase tc
    runWarnTestCase tc
    if dumpCore tc
      then runDualCoreTestCase tc
      else return ()

runUntypedTestCase :: TestCase -> Spec
runUntypedTestCase tc = do
  describe "run as a dynamically-typed program" $ do
    [wantOut, wantErr] <- runIO $ getExpected [".out", ".err"] $ testName tc
    (code, realOut, realErr) <- runIO $ runUntyped $ testName tc
    checkExitCode (runsWell tc) code
    checkOutput "output" wantOut realOut
    checkOutput "error" wantErr realErr

runTypedTestCase :: TestCase -> Spec
runTypedTestCase tc
  | wellTyped tc = do
      describe "run with strict static types enabled" $ do
        [wantOut, wantErr] <- runIO $ getExpected [".out", ".err"] $ testName tc
        (code, realOut, realErr) <- runIO $ runTyped $ testName tc
        checkExitCode (runsWell tc) code
        checkOutput "output" wantOut realOut
        checkOutput "error" wantErr realErr
  | otherwise = do
      describe "run with strict static types enabled" $ do
        let wantOut = Left $ error "no output expected on a type error"
        [wantErr] <- runIO $ getExpected [".terr"] $ testName tc
        (code, realOut, realErr) <- runIO $ runTyped $ testName tc
        checkExitCode False code
        checkOutput "output" wantOut realOut
        checkOutput "error" (onlySourceTyErr <$> wantErr) realErr

runWarnTestCase :: TestCase -> Spec
runWarnTestCase tc = do
  describe "run with static type warnings enabled" $ do
    [wantOut, wantTyErr, wantErr] <- runIO $
      getExpected [".out", ".terr", ".err"] $ testName tc
    (code, realOut, realErr) <- runIO $ runWarn $ testName tc
    checkExitCode (runsWell tc) code
    checkOutput "output" wantOut realOut
    checkOutput "error" (combineErrors wantTyErr wantErr) realErr

runDualCoreTestCase :: TestCase -> Spec
runDualCoreTestCase tc = do
  describe "generating Dual Core intermediate representation" $ do
    (code, realOut, realErr) <- runIO $ dumpDualCore $ testName tc
    [wantOut] <- runIO $ getExpected [".ir"] $ testName tc
    let wantErr = Left $ error "no errors expected when generating Dual Core"
    checkExitCode True code
    checkCore wantOut realOut
    checkOutput "error" wantErr realErr

checkExitCode :: Bool -> ExitCode -> Spec
checkExitCode True  code = do
  it "exits successfully" $ code `shouldBe` ExitSuccess
checkExitCode False code = do
  it "exits with a failure" $ code `shouldNotBe` ExitSuccess

checkOutput :: String -> Either IOException String -> String -> Spec
checkOutput channel (Left _) realOut = do
  it ("prints no " ++ channel) $ do
    linesOut realOut `shouldBe` linesOut ""
checkOutput channel (Right wantOut) realOut = do
  it ("prints the expected " ++ channel) $ do
    linesOut realOut `shouldBe` linesOut wantOut

checkCore :: Either IOException String -> String -> Spec
checkCore (Left _) realOut = do
  it "gives no Dual Core code" $ do
    tokensIR realOut `shouldBe` tokensIR ""
checkCore (Right wantOut) realOut = do
  it "gives the expected Dual Core code" $ do
    tokensIR realOut `shouldBe` tokensIR wantOut

newtype Output = Outp [String]
  deriving (Eq)

linesOut :: String -> Output
linesOut = Outp . lines

instance Show Output where
  show (Outp ls) = unlines ls

newtype Internals = IR String

instance Show Internals where
  show (IR code) = code

instance Eq Internals where
  IR x == IR y = words x == words y

tokensIR :: String -> Internals
tokensIR = IR

runScript :: String -> [String] -> IO (ExitCode, String, String)
runScript name args = readProcessWithExitCode "coo" cooArgs ""
  where cooArgs = [prefix ++ name ++ ".coo"] ++ args

runUntyped :: String -> IO (ExitCode, String, String)
runUntyped name = runScript name []

runTyped :: String -> IO (ExitCode, String, String)
runTyped name = runScript name ["--type=error"]

runWarn :: String -> IO (ExitCode, String, String)
runWarn name = runScript name ["--type=warn"]

dumpDualCore :: String -> IO (ExitCode, String, String)
dumpDualCore name = runScript name ["--dumpdc"]

getExpected :: [String] -> String -> IO [Either IOException String]
getExpected [] _ = return []
getExpected (suffix:dots) name = do
  exp <- try $ readFile $ prefix ++ name ++ suffix
  rest <- getExpected dots name
  return (exp:rest)

onlySourceTyErr :: String -> String
onlySourceTyErr = unlines
                . takeWhile (/= "----------------------------------------")
                . lines

combineErrors :: Either e String -> Either e String -> Either e String
combineErrors (Right ty) (Right run) = Right err
  where err = unlines $ lines ty ++ lines run
combineErrors (Right ty) (Left _) = Right ty
combineErrors (Left _) (Right run) = Right run
combineErrors (Left ty) (Left _) = Left ty


instance MonadFail (SpecM a) where
  fail errMsg = SpecM $ liftIO $ fail errMsg
