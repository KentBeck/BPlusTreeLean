/-
B+ Tree specification and implementation in Lean 4

A B+ Tree is a self-balancing tree data structure that maintains sorted data
and allows searches, sequential access, insertions, and deletions in logarithmic time.
-/

import «BPlusTreeLean».Basic

-- B+ Tree node types
inductive BPlusNode (K V : Type) (order : Nat) where
  | leaf : List (KeyValue K V) → BPlusNode K V order
  | internal : List K → List (BPlusNode K V order) → BPlusNode K V order

-- Make BPlusNode inhabitable
instance : Inhabited (BPlusNode K V order) where
  default := BPlusNode.leaf []

-- B+ Tree structure
structure BPlusTree (K V : Type) (order : Nat) where
  root : BPlusNode K V order
  height : Nat

-- Basic properties and invariants
namespace BPlusTree

variable {K V : Type} [LT K] [LE K] [DecidableRel (α := K) (· < ·)] [DecidableRel (α := K) (· ≤ ·)] 
         [Inhabited K] [Inhabited V] {order : Nat}

-- Invariant: minimum order must be at least 3
def validOrder (order : Nat) : Prop := order ≥ 3

-- Invariant: internal nodes have between ⌈order/2⌉ and order children
def validInternalNodeSize {α : Type} (children : List α) (order : Nat) : Prop :=
  let minChildren := (order + 1) / 2
  children.length ≥ minChildren ∧ children.length ≤ order

-- Invariant: leaf nodes have between ⌈order/2⌉-1 and order-1 key-value pairs
def validLeafNodeSize (entries : List (KeyValue K V)) (order : Nat) : Prop :=
  let minEntries := (order - 1) / 2
  entries.length ≥ minEntries ∧ entries.length ≤ order - 1

-- Invariant: keys in leaf nodes are sorted
def leafSorted (entries : List (KeyValue K V)) : Prop :=
  ∀ i j, i < j → j < entries.length → 
    (entries.get! i).key ≤ (entries.get! j).key

-- Invariant: keys in internal nodes are sorted
def internalKeysSorted (keys : List K) : Prop :=
  ∀ i j, i < j → j < keys.length → keys.get! i ≤ keys.get! j

-- Helper: check single node's local invariants
def nodeWellFormed : BPlusNode K V order → Prop
  | BPlusNode.leaf entries => 
      leafSorted entries ∧ 
      entries.length ≤ order - 1
  | BPlusNode.internal keys children =>
      internalKeysSorted keys ∧
      children.length = keys.length + 1 ∧
      validInternalNodeSize children order

-- Helper: recursively check all nodes are well-formed
def allNodesWellFormed : BPlusNode K V order → Prop
  | BPlusNode.leaf _ => True  -- Base case
  | BPlusNode.internal _ children => 
      (∀ child ∈ children, nodeWellFormed child) ∧  -- Each child satisfies local invariants
      (∀ child ∈ children, allNodesWellFormed child)  -- All children recursively well-formed

-- Helper: all leaves at same depth
def allLeavesAtDepth : BPlusNode K V order → Nat → Prop
  | BPlusNode.leaf _, 0 => True
  | BPlusNode.leaf _, _ + 1 => False  -- Leaf at wrong depth
  | BPlusNode.internal _ _, 0 => False  -- Internal at leaf depth
  | BPlusNode.internal _ children, depth + 1 => 
      ∀ child ∈ children, allLeavesAtDepth child depth

-- ✅ HEIGHT-BASED TERMINATION: Much cleaner approach!
-- Key insight: Tree height decreases monotonically, we always reach leaves

mutual
  -- Extract all keys using height-based termination  
  def allKeysInSubtree : BPlusNode K V order → List K
    | BPlusNode.leaf entries => entries.map (·.key)
    | BPlusNode.internal keys children => 
        keys ++ allKeysInChildren children
  
  -- Process children list (each child has height < parent)
  def allKeysInChildren : List (BPlusNode K V order) → List K
    | [] => []
    | child :: rest => allKeysInSubtree child ++ allKeysInChildren rest
end

-- Termination proof by well-founded recursion on tree structure:
-- 1. allKeysInSubtree(internal) → allKeysInChildren(children_list)  
-- 2. allKeysInChildren(child::rest) → allKeysInSubtree(child) + allKeysInChildren(rest)
-- 3. child has structurally smaller size than parent internal node
-- 4. rest has smaller length than original list
-- 5. Eventually reach leaves and empty lists → terminate

-- Phase 1.2: Helper functions using same height-based termination pattern

mutual
  -- Find minimum key in subtree
  def minKeyInSubtree : BPlusNode K V order → Option K
    | BPlusNode.leaf [] => none
    | BPlusNode.leaf (kv :: _) => some kv.key
    | BPlusNode.internal _ children => minKeyInChildren children
  
  -- Find maximum key in subtree  
  def maxKeyInSubtree : BPlusNode K V order → Option K
    | BPlusNode.leaf [] => none
    | BPlusNode.leaf kvs => kvs.getLast?.map (·.key)
    | BPlusNode.internal _ children => maxKeyInChildren children
  
  -- Helper: find minimum in children list
  def minKeyInChildren : List (BPlusNode K V order) → Option K
    | [] => none
    | [child] => minKeyInSubtree child
    | child :: rest => 
        match minKeyInSubtree child, minKeyInChildren rest with
        | some k1, some k2 => some (if k1 ≤ k2 then k1 else k2)
        | some k1, none => some k1
        | none, some k2 => some k2
        | none, none => none
  
  -- Helper: find maximum in children list
  def maxKeyInChildren : List (BPlusNode K V order) → Option K
    | [] => none
    | [child] => maxKeyInSubtree child
    | child :: rest =>
        match maxKeyInSubtree child, maxKeyInChildren rest with
        | some k1, some k2 => some (if k1 ≤ k2 then k2 else k1)
        | some k1, none => some k1
        | none, some k2 => some k2
        | none, none => none
end

-- Phase 1.2: Correctness properties for helper functions

-- Property: minKeyInSubtree returns actual minimum key
theorem minKeyInSubtree_correct (node : BPlusNode K V order) (k : K) :
  minKeyInSubtree node = some k → ∀ k' ∈ allKeysInSubtree node, k ≤ k' := by
  sorry

-- Property: maxKeyInSubtree returns actual maximum key  
theorem maxKeyInSubtree_correct (node : BPlusNode K V order) (k : K) :
  maxKeyInSubtree node = some k → ∀ k' ∈ allKeysInSubtree node, k' ≤ k := by
  sorry

-- Property: minKeyInSubtree returns none iff no keys exist
theorem minKeyInSubtree_none_iff_empty (node : BPlusNode K V order) :
  minKeyInSubtree node = none ↔ allKeysInSubtree node = [] := by
  sorry

-- Property: maxKeyInSubtree returns none iff no keys exist
theorem maxKeyInSubtree_none_iff_empty (node : BPlusNode K V order) :
  maxKeyInSubtree node = none ↔ allKeysInSubtree node = [] := by
  sorry

-- Helper: check if node's keys are within given bounds
def nodeInKeyRange (node : BPlusNode K V order) (lower_bound upper_bound : Option K) : Prop :=
  ∀ k ∈ allKeysInSubtree node,
    (lower_bound.isNone ∨ lower_bound.get! < k) ∧
    (upper_bound.isNone ∨ k < upper_bound.get!)

-- Helper: key ranges properly maintained with sibling ordering using min/max
def keyRangesValid : BPlusNode K V order → Prop
  | BPlusNode.leaf _ => True
  | BPlusNode.internal keys children =>
      -- Proper key separation: each routing key separates adjacent children
      (∀ i, i < keys.length → 
        -- All keys in left child ≤ routing key < all keys in right child
        (∀ k, minKeyInSubtree (children.get! i) = some k → k ≤ keys.get! i) ∧
        (∀ k, maxKeyInSubtree (children.get! i) = some k → k ≤ keys.get! i) ∧
        (∀ k, minKeyInSubtree (children.get! (i + 1)) = some k → keys.get! i < k)) ∧
      -- Recursively check all children
      ∀ child ∈ children, keyRangesValid child

-- Complete well-formed B+ Tree predicate
def wellFormed (tree : BPlusTree K V order) : Prop :=
  validOrder order ∧
  allNodesWellFormed tree.root ∧           -- 1. Recursive well-formedness
  allLeavesAtDepth tree.root tree.height ∧ -- 2. Balanced depth
  keyRangesValid tree.root                  -- 3. Key range separation

-- Basic operations (specifications)

-- Search operation
def search (tree : BPlusTree K V order) (key : K) : Option V := sorry

-- Insert operation  
def insert (tree : BPlusTree K V order) (key : K) (value : V) : BPlusTree K V order := sorry

-- Delete operation
def delete (tree : BPlusTree K V order) (key : K) : BPlusTree K V order := sorry

-- Range query operation
def rangeQuery (tree : BPlusTree K V order) (startKey endKey : K) : List (KeyValue K V) := sorry

-- Theorems to prove about our B+ Tree

-- Search correctness
theorem search_correct {tree : BPlusTree K V order} {key : K} :
  wellFormed tree →
  (search tree key).isSome ↔ ∃ value, insert tree key value = tree := by sorry

-- Insert preserves well-formedness
theorem insert_preserves_wellformed {tree : BPlusTree K V order} {key : K} {value : V} :
  wellFormed tree → wellFormed (insert tree key value) := by sorry

-- Delete preserves well-formedness  
theorem delete_preserves_wellformed {tree : BPlusTree K V order} {key : K} :
  wellFormed tree → wellFormed (delete tree key) := by sorry

-- Height bounds (simplified without log)
theorem height_bounded {tree : BPlusTree K V order} {n : Nat} :
  wellFormed tree → 
  (∃ entries, tree.root = BPlusNode.leaf entries ∧ entries.length = n) →
  tree.height ≤ n := by sorry

end BPlusTree
