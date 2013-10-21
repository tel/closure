-- |
-- Module      : Algebra.Closure.Set.BreadthFirst
-- Copyright   : (c) Joseph Abrahamson 2013
-- License     : MIT
-- 
-- Maintainer  : me@jspha.com
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Depth-first closed sets. For a particular endomorphism @(p :: a ->
-- a)@ a 'Closed' set is a set where if some element @x@ is in the set
-- then so is @p x@. Unlike "Algebra.Closure.Set.DepthFirst", this
-- algorithm computes the closure in a depth-first manner and thus can
-- be useful for computing infinite closures.
-- 
-- It's reasonable to think of a breadth-first 'Closed' set as the
-- process of generating a depth-first
-- 'Algebra.Closure.Set.DepthFirst.Closed' set frozen in time. This
-- retains information about the number of iterations required for
-- stability and allows us to return answers that depend only upon
-- partial information even if the closure itself is unbounded.

module Algebra.Closure.Set.BreadthFirst (

  -- * Closed sets
  Closed, seenBy, seen,

  -- ** Operations
  memberWithin', memberWithin, member', member,

  -- ** Creation
  close,
  
  ) where

import Prelude hiding (foldr)
import Data.HashSet (HashSet)
import Data.Hashable
import Data.Foldable (Foldable, foldr, toList)
import qualified Data.HashSet as Set

-- | A closed set @Closed a@, given an endomorphism @(p :: a -> a)@,
-- is a set where if some element @x@ is in the set then so is @p x@.
data Closed a = Unchanging | Closed Int (a -> a) (HashSet a) (Closed a)

-- | @seenBy n@ converts a 'Closed' set into its underlying set,
-- approximated by @n@ iterations.
seenBy :: Int -> Closed a -> HashSet a
seenBy _ Unchanging = Set.empty
seenBy 0 (Closed _ _ set _)          = set
seenBy n (Closed _ _ set Unchanging) = set
seenBy n (Closed _ _ set next)       = seenBy (pred n) next

-- | Converts a 'Closed' set into its underlying set. If the 'Closed'
-- set is unbounded then this operation is undefined (see
-- 'seenBy'). It's reasonable to think of this operation as
-- 
-- @
--   let omega = succ omega in seenBy omega
-- @
seen :: Closed a -> HashSet a
seen Unchanging = Set.empty
seen (Closed _ _ set Unchanging) = set
seen (Closed _ _ set next)       = seen next

-- | @memberWithin' n a@ checks to see whether an element is within a
-- 'Closed' set after @n@ improvements. The 'Closed' set returned is a
-- compressed, memoized 'Closed' set which may be faster to query.
memberWithin' :: (Hashable a, Eq a) => Int -> a -> Closed a -> (Bool, Closed a)
memberWithin' n _ Unchanging = (False, Unchanging)
memberWithin' 0 _ set        = (False, set)
memberWithin' n a c@(Closed _ _ set next)
  | Set.member a set = (True, c)
  | otherwise        = memberWithin' (pred n) a next

-- | @memberWithin' n a@ checks to see whether an element is within a
-- 'Closed' set after @n@ improvements.
memberWithin :: (Hashable a, Eq a) => Int -> a -> Closed a -> Bool
memberWithin n a = fst . memberWithin' n a

-- | Determines whether a particular element is in the 'Closed'
-- set. If the element is in the set, this operation is always
-- defined. If it is not and the set is unbounded, this operation is
-- undefined (see 'memberWithin'). It's reasonable to think of this
-- operation as
-- 
-- @
--   let omega = succ omega in memberWithin omega
-- @
-- The 'Closed' set returned is a compressed, memoized 'Closed' set
-- which may be faster to query.
member' :: (Hashable a, Eq a) => a -> Closed a -> (Bool, Closed a)
member' _ Unchanging = (False, Unchanging)
member' a c@(Closed _ _ set next)
  | Set.member a set = (True, c)
  | otherwise        = member' a next

-- | Determines whether a particular element is in the 'Closed'
-- set. If the element is in the set, this operation is always
-- defined. If it is not and the set is unbounded, this operation is
-- undefined (see 'memberWithin'). It's reasonable to think of this
-- operation as
-- 
-- @
--   let omega = succ omega in memberWithin omega
-- @
member :: (Hashable a, Eq a) => a -> Closed a -> Bool
member a = fst . member' a

-- | Converts any 'Foldable' container into the 'Closed' set of its
-- contents.
close :: (Hashable a, Eq a, Foldable t) => (a -> a) -> t a -> Closed a
close iter = build 0 Set.empty . toList where
  inserter :: (Hashable a, Eq a) => a -> (HashSet a, [a]) -> (HashSet a, [a])
  inserter a (set, fresh) | Set.member a set = (set, fresh)
                          | otherwise        = (Set.insert a set, a:fresh)
  build n curr [] = Unchanging
  build n curr as =
    Closed n iter curr $ step n (foldr inserter (curr, []) as)
  step n (set, added) = build (succ n) set (map iter added)
