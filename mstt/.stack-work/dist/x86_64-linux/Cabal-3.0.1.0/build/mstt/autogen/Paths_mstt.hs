{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_mstt (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/bin"
libdir     = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/lib/x86_64-linux-ghc-8.8.4/mstt-0.1.0.0-6bZ9hRYb3LD4ewiVCnZXDU-mstt"
dynlibdir  = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/lib/x86_64-linux-ghc-8.8.4"
datadir    = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/share/x86_64-linux-ghc-8.8.4/mstt-0.1.0.0"
libexecdir = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/libexec/x86_64-linux-ghc-8.8.4/mstt-0.1.0.0"
sysconfdir = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/2bc86c3339f53373fe86c1263ec8edd7f70ca75f14305175a1b36cb3a040d0e6/8.8.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "mstt_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "mstt_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "mstt_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "mstt_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "mstt_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "mstt_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
