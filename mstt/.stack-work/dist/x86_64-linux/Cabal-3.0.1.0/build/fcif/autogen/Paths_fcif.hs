{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_fcif (
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

bindir     = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/bin"
libdir     = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/lib/x86_64-linux-ghc-8.8.3/fcif-0.1.0.0-LlTyYBUkEQQ3ktxgKKLLi3-fcif"
dynlibdir  = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/lib/x86_64-linux-ghc-8.8.3"
datadir    = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/share/x86_64-linux-ghc-8.8.3/fcif-0.1.0.0"
libexecdir = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/libexec/x86_64-linux-ghc-8.8.3/fcif-0.1.0.0"
sysconfdir = "/home/kutta/home/Dropbox/src/implicit-fun-elab/fcif/.stack-work/install/x86_64-linux/226465a220021b76112946ab905ed20fe54a135b7d435d4f668881a2dfd52da1/8.8.3/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "fcif_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "fcif_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "fcif_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "fcif_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "fcif_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "fcif_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
