
-- | Top-level mutable state involved in elaboration. We use actual mutable
--   top-level references simply because it's convenient and our simple
--   program does not call for anything more sophisticated.

module ElabState where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap.Strict as IM

import Types

runIO :: IO a -> a
runIO = unsafeDupablePerformIO

--------------------------------------------------------------------------------

mcxt :: IORef MCxt
mcxt = runIO (newIORef mempty)
{-# noinline mcxt #-}

nextMId :: IORef Int
nextMId = runIO (newIORef 0)
{-# noinline nextMId #-}

lookupMeta :: MId -> IO MetaEntry
lookupMeta m = do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e -> pure e
    _      -> error "impossible"

runLookupMeta :: MId -> MetaEntry
runLookupMeta m = runIO (lookupMeta m)

alterMeta :: MId -> (Maybe MetaEntry -> Maybe MetaEntry) -> IO ()
alterMeta m f = modifyIORef' mcxt (IM.alter f m)

modifyMeta :: MId -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta m f = alterMeta m (maybe (error "impossible") (Just . f))

writeMeta :: MId -> MetaEntry -> IO ()
writeMeta m e = modifyMeta m (const e)

newMeta :: MetaEntry -> IO MId
newMeta e = do
  m <- readIORef nextMId
  writeIORef nextMId $! (m + 1)
  alterMeta m (maybe (Just e) (\_ -> error "impossible"))
  pure m

--------------------------------------------------------------------------------

nextStageId :: IORef Int
nextStageId = runIO (newIORef 0)
{-# noinline nextStageId #-}

stages :: IORef StageCxt
stages = runIO (newIORef mempty)
{-# noinline stages #-}

lookupStageVar :: StageId -> IO StageEntry
lookupStageVar s = do
  ss <- readIORef stages
  case IM.lookup s ss of
    Just e -> pure e
    _      -> error "impossible"

runLookupStageVar :: StageId -> StageEntry
runLookupStageVar m = runIO (lookupStageVar m)

alterStageVar :: StageId -> (Maybe StageEntry -> Maybe StageEntry) -> IO ()
alterStageVar m f = modifyIORef' stages (IM.alter f m)

modifyStageVar :: StageId -> (StageEntry -> StageEntry) -> IO ()
modifyStageVar m f = alterStageVar m (maybe (error "impossible") (Just . f))

writeStageVar :: StageId -> StageEntry -> IO ()
writeStageVar m e = modifyStageVar m (const e)

newStageVar :: StageEntry -> IO StageId
newStageVar e = do
  m <- readIORef nextStageId
  writeIORef nextStageId $! (m + 1)
  alterStageVar m (maybe (Just e) (\_ -> error "impossible"))
  pure m


--------------------------------------------------------------------------------

showInsertions :: IORef Bool
showInsertions = runIO (newIORef False)
{-# noinline showInsertions #-}

showingInsertions :: (Bool -> a) -> a
showingInsertions f = runIO (f <$> readIORef showInsertions)

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
  writeIORef showInsertions False
  writeIORef stages mempty
  writeIORef nextStageId 0
