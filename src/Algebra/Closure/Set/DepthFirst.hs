-- |
-- Module      : Algebra.Closure.Set.DepthFirst
-- Copyright   : (c) Joseph Abrahamson 2013
-- License     : MIT
-- 
-- Maintainer  : me@jspha.com
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Depth-first closed sets. For a particular endomorphism @(p :: a ->
-- a)@ a 'Closed' set is a set where if some element @x@ is in the set
-- then so is @p x@.

module Algebra.Closure.Set.DepthFirst (

  -- * Closed sets
  Closed, seen,

  -- ** Operations
  member,

  -- ** Creation
  empty, insert, close,
  
  ) where

import Prelude hiding (foldr)
import Data.HashSet (HashSet)
import Data.Hashable
import Data.Foldable (Foldable, foldr)
import qualified Data.HashSet as Set

-- | A closed set @Closed a@, given an endomorphism @(p :: a -> a)@,
-- is a set where if some element @x@ is in the set then so is @p x@.
data Closed a = Closed (HashSet a) (a -> a)

-- | Access the underlying set.
seen :: Closed a -> HashSet a
seen (Closed set _) = set

-- | Inserts a new element into a 'Closed' set, maintaining closure.
insert :: (Hashable a, Eq a) => a -> Closed a -> Closed a
insert a c@(Closed set iter)
  | Set.member a set = c
  | otherwise        = insert (iter a) $ Closed (Set.insert a set) iter

-- | An empty closed set under a fixed endomorphism.
empty :: (a -> a) -> Closed a
empty = Closed Set.empty

-- | Is a particular element in the closure of this set?
member :: (Hashable a, Eq a) => a -> Closed a -> Bool
member a = Set.member a . seen

-- | Converts any 'Foldable' container into the 'Closed' set of its
-- contents.
close :: (Hashable a, Eq a, Foldable t) => (a -> a) -> t a -> Closed a
close iter = foldr insert (empty iter)
