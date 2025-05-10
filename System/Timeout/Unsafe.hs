
module System.Timeout.Unsafe where

import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Exception (SomeException, handle, evaluate)
import System.Timeout (timeout)
import GHC.Stack

-- Unsafe function to run a computation with a timeout
unsafeTimeout :: Int -> IO a -> IO (Maybe a)
unsafeTimeout time action =
  handle (\(_ :: SomeException) -> return Nothing) $ do
    result <- timeout time action
    return result

-- Example usage with unsafePerformIO
debugWithTimeout :: HasCallStack => Int -> String -> a -> a
debugWithTimeout timeLimit err computation = unsafePerformIO $ do
  done <- timeout timeLimit $ evaluate computation
  case done of
    Nothing -> error $ "Computation timed out!\n" ++ err
    Just value -> return value


