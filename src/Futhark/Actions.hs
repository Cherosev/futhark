{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | All (almost) compiler pipelines end with an 'Action', which does
-- something with the result of the pipeline.
module Futhark.Actions
  ( printAction,
    printAliasesAction,
    memAliasesAction,
    compareLastUseAction,
    impCodeGenAction,
    kernelImpCodeGenAction,
    multicoreImpCodeGenAction,
    memoryBlockMerging,
    metricsAction,
    compileCAction,
    compileCtoWASMAction,
    compileOpenCLAction,
    compileCUDAAction,
    compileMulticoreAction,
    compileMulticoreToWASMAction,
    compilePythonAction,
    compilePyOpenCLAction,
  )
where

import Control.Monad
import Control.Monad.IO.Class
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Futhark.Analysis.Alias
import qualified Futhark.Analysis.LastUse
import qualified Futhark.Analysis.MemAlias as MA
import Futhark.Analysis.Metrics
import qualified Futhark.CodeGen.Backends.CCUDA as CCUDA
import qualified Futhark.CodeGen.Backends.COpenCL as COpenCL
import qualified Futhark.CodeGen.Backends.MulticoreC as MulticoreC
import qualified Futhark.CodeGen.Backends.MulticoreWASM as MulticoreWASM
import qualified Futhark.CodeGen.Backends.PyOpenCL as PyOpenCL
import qualified Futhark.CodeGen.Backends.SequentialC as SequentialC
import qualified Futhark.CodeGen.Backends.SequentialPython as SequentialPy
import qualified Futhark.CodeGen.Backends.SequentialWASM as SequentialWASM
import qualified Futhark.CodeGen.ImpGen.GPU as ImpGenGPU
import qualified Futhark.CodeGen.ImpGen.Multicore as ImpGenMulticore
import qualified Futhark.CodeGen.ImpGen.Sequential as ImpGenSequential
import Futhark.Compiler.CLI
import Futhark.IR
import Futhark.IR.GPUMem (GPUMem)
import Futhark.IR.MCMem (MCMem)
import Futhark.IR.Prop.Aliases
import Futhark.IR.SeqMem (SeqMem)
import qualified Futhark.Optimise.MemBlockCoalesce as Coalesce
import qualified Futhark.Optimise.MemBlockCoalesce.LastUse
import Futhark.Util (runProgramWithExitCode, unixEnvironment)
import Futhark.Version (versionString)
import System.Directory
import System.Exit
import System.FilePath
import qualified System.Info

-- | Print the result to stdout.
printAction :: ASTRep rep => Action rep
printAction =
  Action
    { actionName = "Prettyprint",
      actionDescription = "Prettyprint the resulting internal representation on standard output.",
      actionProcedure = liftIO . putStrLn . pretty
    }

-- | Print the result to stdout, alias annotations.
printAliasesAction :: (ASTRep rep, CanBeAliased (Op rep)) => Action rep
printAliasesAction =
  Action
    { actionName = "Prettyprint",
      actionDescription = "Prettyprint the resulting internal representation on standard output.",
      actionProcedure = liftIO . putStrLn . pretty . aliasAnalysis
    }

-- | Print the result to stdout, alias annotations.
memAliasesAction :: Action GPUMem
memAliasesAction =
  Action
    { actionName = "mem alias",
      actionDescription = "Print memory aliases on standard output.",
      actionProcedure = liftIO . putStrLn . pretty . MA.analyze
    }

-- | Print metrics about AST node counts to stdout.
metricsAction :: OpMetrics (Op rep) => Action rep
metricsAction =
  Action
    { actionName = "Compute metrics",
      actionDescription = "Print metrics on the final AST.",
      actionProcedure = liftIO . putStr . show . progMetrics
    }

-- | Print the result to stdout, alias annotations.
compareLastUseAction :: Action SeqMem
compareLastUseAction =
  Action
    { actionName = "Compare Last Use",
      actionDescription = "Compare last use",
      actionProcedure = \prog -> do
        let lastuse1 = fst $ Futhark.Analysis.LastUse.analyseSeqMem prog
        let lastuse2 = mconcat $ M.elems $ Futhark.Optimise.MemBlockCoalesce.LastUse.lastUsePrg $ aliasAnalysis prog
        if lastuse1 == lastuse2
          then return ()
          else liftIO $ putStrLn ("Last uses differ:\n" <> pretty lastuse1 <> "\n" <> pretty lastuse2)

        liftIO $ putStrLn ""

        let allnames1 = mconcat $ M.elems lastuse1
        let allnames2 = mconcat $ M.elems lastuse2
        if allnames1 == allnames2
          then return ()
          else liftIO $ putStrLn ("Allnames differ:\n" <> pretty allnames1 <> "\n" <> pretty allnames2)
    }

-- | Convert the program to sequential ImpCode and print it to stdout.
impCodeGenAction :: Action SeqMem
impCodeGenAction =
  Action
    { actionName = "Compile imperative",
      actionDescription = "Translate program into imperative IL and write it on standard output.",
      actionProcedure = liftIO . putStrLn . pretty . snd <=< ImpGenSequential.compileProg
    }

-- | Convert the program to GPU ImpCode and print it to stdout.
kernelImpCodeGenAction :: Action GPUMem
kernelImpCodeGenAction =
  Action
    { actionName = "Compile imperative kernels",
      actionDescription = "Translate program into imperative IL with kernels and write it on standard output.",
      actionProcedure = liftIO . putStrLn . pretty . snd <=< ImpGenGPU.compileProgOpenCL
    }

-- | Convert the program to CPU multicore ImpCode and print it to stdout.
multicoreImpCodeGenAction :: Action MCMem
multicoreImpCodeGenAction =
  Action
    { actionName = "Compile to imperative multicore",
      actionDescription = "Translate program into imperative multicore IL and write it on standard output.",
      actionProcedure = liftIO . putStrLn . pretty . snd <=< ImpGenMulticore.compileProg
    }

memoryBlockMerging :: Action SeqMem
memoryBlockMerging =
  Action
    { actionName = "Merge memory blocks",
      actionDescription = "Perform memory block merging and print results",
      actionProcedure = liftIO . Coalesce.memoryBlockMerging
    }

-- Lines that we prepend (in comments) to generated code.
headerLines :: [T.Text]
headerLines = T.lines $ "Generated by Futhark " <> T.pack versionString

cHeaderLines :: [T.Text]
cHeaderLines = map ("// " <>) headerLines

pyHeaderLines :: [T.Text]
pyHeaderLines = map ("# " <>) headerLines

cPrependHeader :: T.Text -> T.Text
cPrependHeader = (T.unlines cHeaderLines <>)

pyPrependHeader :: T.Text -> T.Text
pyPrependHeader = (T.unlines pyHeaderLines <>)

cmdCC :: String
cmdCC = fromMaybe "cc" $ lookup "CC" unixEnvironment

cmdCFLAGS :: [String] -> [String]
cmdCFLAGS def = maybe def words $ lookup "CFLAGS" unixEnvironment

runCC :: String -> String -> [String] -> [String] -> FutharkM ()
runCC cpath outpath cflags_def ldflags = do
  ret <-
    liftIO $
      runProgramWithExitCode
        cmdCC
        ( [cpath, "-o", outpath]
            ++ cmdCFLAGS cflags_def
            ++
            -- The default LDFLAGS are always added.
            ldflags
        )
        mempty
  case ret of
    Left err ->
      externalErrorS $ "Failed to run " ++ cmdCC ++ ": " ++ show err
    Right (ExitFailure code, _, gccerr) ->
      externalErrorS $
        cmdCC ++ " failed with code "
          ++ show code
          ++ ":\n"
          ++ gccerr
    Right (ExitSuccess, _, _) ->
      return ()

-- | The @futhark c@ action.
compileCAction :: FutharkConfig -> CompilerMode -> FilePath -> Action SeqMem
compileCAction fcfg mode outpath =
  Action
    { actionName = "Compile to sequential C",
      actionDescription = "Compile to sequential C",
      actionProcedure = helper
    }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ SequentialC.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"

      case mode of
        ToLibrary -> do
          let (header, impl) = SequentialC.asLibrary cprog
          liftIO $ T.writeFile hpath $ cPrependHeader header
          liftIO $ T.writeFile cpath $ cPrependHeader impl
        ToExecutable -> do
          liftIO $ T.writeFile cpath $ SequentialC.asExecutable cprog
          runCC cpath outpath ["-O3", "-std=c99"] ["-lm"]
        ToServer -> do
          liftIO $ T.writeFile cpath $ SequentialC.asServer cprog
          runCC cpath outpath ["-O3", "-std=c99"] ["-lm"]

-- | The @futhark opencl@ action.
compileOpenCLAction :: FutharkConfig -> CompilerMode -> FilePath -> Action GPUMem
compileOpenCLAction fcfg mode outpath =
  Action
    { actionName = "Compile to OpenCL",
      actionDescription = "Compile to OpenCL",
      actionProcedure = helper
    }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ COpenCL.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"
          extra_options
            | System.Info.os == "darwin" =
              ["-framework", "OpenCL"]
            | System.Info.os == "mingw32" =
              ["-lOpenCL64"]
            | otherwise =
              ["-lOpenCL"]

      case mode of
        ToLibrary -> do
          let (header, impl) = COpenCL.asLibrary cprog
          liftIO $ T.writeFile hpath $ cPrependHeader header
          liftIO $ T.writeFile cpath $ cPrependHeader impl
        ToExecutable -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ COpenCL.asExecutable cprog
          runCC cpath outpath ["-O", "-std=c99"] ("-lm" : extra_options)
        ToServer -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ COpenCL.asServer cprog
          runCC cpath outpath ["-O", "-std=c99"] ("-lm" : extra_options)

-- | The @futhark cuda@ action.
compileCUDAAction :: FutharkConfig -> CompilerMode -> FilePath -> Action GPUMem
compileCUDAAction fcfg mode outpath =
  Action
    { actionName = "Compile to CUDA",
      actionDescription = "Compile to CUDA",
      actionProcedure = helper
    }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ CCUDA.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"
          extra_options =
            [ "-lcuda",
              "-lcudart",
              "-lnvrtc"
            ]
      case mode of
        ToLibrary -> do
          let (header, impl) = CCUDA.asLibrary cprog
          liftIO $ T.writeFile hpath $ cPrependHeader header
          liftIO $ T.writeFile cpath $ cPrependHeader impl
        ToExecutable -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ CCUDA.asExecutable cprog
          runCC cpath outpath ["-O", "-std=c99"] ("-lm" : extra_options)
        ToServer -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ CCUDA.asServer cprog
          runCC cpath outpath ["-O", "-std=c99"] ("-lm" : extra_options)

-- | The @futhark multicore@ action.
compileMulticoreAction :: FutharkConfig -> CompilerMode -> FilePath -> Action MCMem
compileMulticoreAction fcfg mode outpath =
  Action
    { actionName = "Compile to multicore",
      actionDescription = "Compile to multicore",
      actionProcedure = helper
    }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ MulticoreC.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"

      case mode of
        ToLibrary -> do
          let (header, impl) = MulticoreC.asLibrary cprog
          liftIO $ T.writeFile hpath $ cPrependHeader header
          liftIO $ T.writeFile cpath $ cPrependHeader impl
        ToExecutable -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ MulticoreC.asExecutable cprog
          runCC cpath outpath ["-O3", "-std=c99"] ["-lm", "-pthread"]
        ToServer -> do
          liftIO $ T.writeFile cpath $ cPrependHeader $ MulticoreC.asServer cprog
          runCC cpath outpath ["-O3", "-std=c99"] ["-lm", "-pthread"]

pythonCommon ::
  (CompilerMode -> String -> prog -> FutharkM (Warnings, T.Text)) ->
  FutharkConfig ->
  CompilerMode ->
  FilePath ->
  prog ->
  FutharkM ()
pythonCommon codegen fcfg mode outpath prog = do
  let class_name =
        case mode of
          ToLibrary -> takeBaseName outpath
          _ -> "internal"
  pyprog <- handleWarnings fcfg $ codegen mode class_name prog

  case mode of
    ToLibrary ->
      liftIO $ T.writeFile (outpath `addExtension` "py") $ pyPrependHeader pyprog
    _ -> liftIO $ do
      T.writeFile outpath $ "#!/usr/bin/env python3\n" <> pyPrependHeader pyprog
      perms <- liftIO $ getPermissions outpath
      setPermissions outpath $ setOwnerExecutable True perms

-- | The @futhark python@ action.
compilePythonAction :: FutharkConfig -> CompilerMode -> FilePath -> Action SeqMem
compilePythonAction fcfg mode outpath =
  Action
    { actionName = "Compile to PyOpenCL",
      actionDescription = "Compile to Python with OpenCL",
      actionProcedure = pythonCommon SequentialPy.compileProg fcfg mode outpath
    }

-- | The @futhark pyopencl@ action.
compilePyOpenCLAction :: FutharkConfig -> CompilerMode -> FilePath -> Action GPUMem
compilePyOpenCLAction fcfg mode outpath =
  Action
    { actionName = "Compile to PyOpenCL",
      actionDescription = "Compile to Python with OpenCL",
      actionProcedure = pythonCommon PyOpenCL.compileProg fcfg mode outpath
    }

cmdEMCFLAGS :: [String] -> [String]
cmdEMCFLAGS def = maybe def words $ lookup "EMCFLAGS" unixEnvironment

runEMCC :: String -> String -> FilePath -> [String] -> [String] -> [String] -> Bool -> FutharkM ()
runEMCC cpath outpath classpath cflags_def ldflags expfuns lib = do
  ret <-
    liftIO $
      runProgramWithExitCode
        "emcc"
        ( [cpath, "-o", outpath]
            ++ ["-lnodefs.js"]
            ++ ["-s", "--extern-post-js", classpath]
            ++ ( if lib
                   then
                     [ "-s",
                       "EXPORT_NAME=loadWASM",
                       "-s",
                       "MODULARIZE=1",
                       "-s",
                       "EXPORT_ES6=1"
                     ]
                   else []
               )
            ++ ["-s", "WASM_BIGINT"]
            ++ cmdCFLAGS cflags_def
            ++ cmdEMCFLAGS [""]
            ++ [ "-s",
                 "EXPORTED_FUNCTIONS=["
                   ++ intercalate "," ("'_malloc'" : "'_free'" : expfuns)
                   ++ "]"
               ]
            -- The default LDFLAGS are always added.
            ++ ldflags
        )
        mempty
  case ret of
    Left err ->
      externalErrorS $ "Failed to run emcc: " ++ show err
    Right (ExitFailure code, _, emccerr) ->
      externalErrorS $
        "emcc failed with code "
          ++ show code
          ++ ":\n"
          ++ emccerr
    Right (ExitSuccess, _, _) ->
      return ()

-- | The @futhark wasm@ action.
compileCtoWASMAction :: FutharkConfig -> CompilerMode -> FilePath -> Action SeqMem
compileCtoWASMAction fcfg mode outpath =
  Action
    { actionName = "Compile to sequential C",
      actionDescription = "Compile to sequential C",
      actionProcedure = helper
    }
  where
    helper prog = do
      (cprog, jsprog, exps) <- handleWarnings fcfg $ SequentialWASM.compileProg prog
      case mode of
        ToLibrary -> do
          writeLibs cprog jsprog
          liftIO $ T.appendFile classpath SequentialWASM.libraryExports
          runEMCC cpath mjspath classpath ["-O3", "-msimd128"] ["-lm"] exps True
        _ -> do
          -- Non-server executables are not supported.
          writeLibs cprog jsprog
          liftIO $ T.appendFile classpath SequentialWASM.runServer
          runEMCC cpath outpath classpath ["-O3", "-msimd128"] ["-lm"] exps False
    writeLibs cprog jsprog = do
      let (h, imp) = SequentialC.asLibrary cprog
      liftIO $ T.writeFile hpath h
      liftIO $ T.writeFile cpath imp
      liftIO $ T.writeFile classpath jsprog

    cpath = outpath `addExtension` "c"
    hpath = outpath `addExtension` "h"
    mjspath = outpath `addExtension` "mjs"
    classpath = outpath `addExtension` ".class.js"

-- | The @futhark wasm-multicore@ action.
compileMulticoreToWASMAction :: FutharkConfig -> CompilerMode -> FilePath -> Action MCMem
compileMulticoreToWASMAction fcfg mode outpath =
  Action
    { actionName = "Compile to sequential C",
      actionDescription = "Compile to sequential C",
      actionProcedure = helper
    }
  where
    helper prog = do
      (cprog, jsprog, exps) <- handleWarnings fcfg $ MulticoreWASM.compileProg prog

      case mode of
        ToLibrary -> do
          writeLibs cprog jsprog
          liftIO $ T.appendFile classpath MulticoreWASM.libraryExports
          runEMCC cpath mjspath classpath ["-O3", "-msimd128"] ["-lm", "-pthread"] exps True
        _ -> do
          -- Non-server executables are not supported.
          writeLibs cprog jsprog
          liftIO $ T.appendFile classpath MulticoreWASM.runServer
          runEMCC cpath outpath classpath ["-O3", "-msimd128"] ["-lm", "-pthread"] exps False

    writeLibs cprog jsprog = do
      let (h, imp) = MulticoreC.asLibrary cprog
      liftIO $ T.writeFile hpath h
      liftIO $ T.writeFile cpath imp
      liftIO $ T.writeFile classpath jsprog

    cpath = outpath `addExtension` "c"
    hpath = outpath `addExtension` "h"
    mjspath = outpath `addExtension` "mjs"
    classpath = outpath `addExtension` ".class.js"
