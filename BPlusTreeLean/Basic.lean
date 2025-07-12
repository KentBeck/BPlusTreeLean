/-
Basic definitions and utilities for B+ Trees
-/

-- Basic comparison and ordering utilities
def Comparable (α : Type*) : Type* := α → α → Ordering

-- Basic properties we'll need
class LinearOrder (α : Type*) extends PartialOrder α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decidable_le : DecidableRel (· ≤ · : α → α → Prop)

-- Key-value pair for B+ Tree entries
structure KeyValue (K V : Type*) where
  key : K
  value : V

-- Utility functions
def KeyValue.compareByKey [LinearOrder K] (kv1 kv2 : KeyValue K V) : Ordering :=
  if kv1.key < kv2.key then Ordering.lt
  else if kv1.key = kv2.key then Ordering.eq
  else Ordering.gt
