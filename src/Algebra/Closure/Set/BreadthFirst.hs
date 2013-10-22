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
-- algorithm computes the closure in a breadth-first manner and thus can
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

import Control.Applicative
import Data.HashSet (HashSet)
import Data.Hashable
import Data.Foldable (Foldable, foldr, toList)
import qualified Data.HashSet as Set

-- | A closed set @Closed a@, given an endomorphism @(p :: a -> a)@,
-- is a set where if some element @x@ is in the set then so is @p x@.
data Closed a = Closed Int (a -> a) (ClosedF a)

data ClosedF a = Unchanging (HashSet a) | ClosedF (HashSet a) (ClosedF a)

-- | (Internal) Get the immediate HashSet
setOf :: ClosedF a -> HashSet a
setOf (Unchanging set  ) = set
setOf (ClosedF    set _) = set

data Omega a = A a | O deriving ( Eq, Ord )

opred :: Enum a => Omega a -> Omega a
opred O = O
opred (A a) = A (pred a)

instance Functor Omega where
  fmap f O = O
  fmap f (A a) = A (f a)

instance Applicative Omega where
  pure = A
  O <*> _ = O
  _ <*> O = O
  A f <*> A x = A $ f x

instance Num a => Num (Omega a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  negate = fmap negate
  signum = fmap signum
  fromInteger = pure . fromInteger
  
-- | @seenBy n@ converts a 'Closed' set into its underlying set,
-- approximated by at least @n@ iterations.
seenByG :: Omega Int -> Closed a -> HashSet a
seenByG n (Closed m _ closef)
  | n - A m < 0 = setOf closef
  | otherwise   = seenByI (n - A m) closef
  where
    seenByI 0 closef = setOf closef
    seenByI n (Unchanging set) = set
    seenByI n (ClosedF _ next)  = seenByI (opred n) next

-- | @seenBy n@ converts a 'Closed' set into its underlying set,
-- approximated by at least @n@ iterations.
seenBy :: Int -> Closed a -> HashSet a
seenBy n = seenByG (A n)

-- | Converts a 'Closed' set into its underlying set. If the 'Closed'
-- set is unbounded then this operation is undefined (see
-- 'seenBy'). It's reasonable to think of this operation as
-- 
-- @
--   let omega = succ omega in seenBy omega
-- @
seen :: Closed a -> HashSet a
seen = seenByG O

memberWithinG' :: (Hashable a, Eq a) => Omega Int -> a -> Closed a -> (Bool, Closed a)
memberWithinG' n a closed@(Closed m iter closef)
  | n - A m < 0 = (Set.member a (setOf closef), closed)
  | otherwise   = memberWithinI (n - A m) 0 closef
  where
    memberWithinI 0 up closef =
      -- We KNOW that 'n' cannot be 'O' here since it was able to be
      -- decremented to 0.
      case n of
        O     -> error "Algebra.Closure.Set.BreadthFirst: Impossible"
        (A n') -> (Set.member a (setOf closef), Closed n' iter closef)

    memberWithinI dn up closef@(ClosedF set next)
      | Set.member a set = (True, Closed (m + up) iter closef)
      | otherwise        = memberWithinI (opred dn) (succ up) next

-- | @memberWithin' n a@ checks to see whether an element is within a
-- 'Closed' set after @n@ improvements (but does not guarantee the @n@
-- is the minimal number needed). The 'Closed' set returned is a
-- compressed, memoized 'Closed' set which may be faster to query.
memberWithin' :: (Hashable a, Eq a) => Int -> a -> Closed a -> (Bool, Closed a)
memberWithin' n = memberWithinG' (A n)
                           
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
member' = memberWithinG' O

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
close iter = Closed 0 iter . build Set.empty . toList where
  inserter :: (Hashable a, Eq a) => a -> (HashSet a, [a]) -> (HashSet a, [a])
  inserter a (set, fresh) | Set.member a set = (set, fresh)
                          | otherwise        = (Set.insert a set, a:fresh)
  build curr [] = Unchanging curr
  build curr as =
    ClosedF curr $ step (foldr inserter (curr, []) as)
  step (set, added) = build set (map iter added)

-- insert :: a -> Closed a -> Closed a
-- insert a Unchanging = 
-- insert a (Closed n iter set next) = 

