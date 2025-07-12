/-
Basic definitions and utilities for B+ Trees
-/

-- Key-value pair for B+ Tree entries
structure KeyValue (K V : Type) where
  key : K
  value : V

-- Make KeyValue inhabitable when K and V are inhabitable
instance [Inhabited K] [Inhabited V] : Inhabited (KeyValue K V) where
  default := ⟨default, default⟩

-- Utility functions for comparison
def KeyValue.compareByKey [LT K] [DecidableRel (α := K) (· < ·)] [DecidableEq K] 
    (kv1 kv2 : KeyValue K V) : Ordering :=
  if kv1.key < kv2.key then Ordering.lt
  else if kv1.key = kv2.key then Ordering.eq
  else Ordering.gt
