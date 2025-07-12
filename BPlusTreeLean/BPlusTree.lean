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

-- Helper: simple depth measure for termination (non-recursive)
def treeDepth : BPlusNode K V order → Nat
  | BPlusNode.leaf _ => 0
  | BPlusNode.internal _ children => 1 + children.length

-- Helper: extract all keys from a subtree  
def allKeysInSubtree : BPlusNode K V order → List K
  | BPlusNode.leaf entries => entries.map (·.key)
  | BPlusNode.internal keys children => 
      keys ++ (children.bind allKeysInSubtree)
termination_by node => sizeOf node
decreasing_by 
  -- For provably correct implementation: child ∈ children → sizeOf child < sizeOf parent
  -- This requires the structural ordering lemma for inductive constructors
  -- Proof: List.sizeOf_lt_of_mem + constructor size properties
  sorry

-- Helper: check if node's keys are within given bounds
def nodeInKeyRange (node : BPlusNode K V order) (lower_bound upper_bound : Option K) : Prop :=
  ∀ k ∈ allKeysInSubtree node,
    (lower_bound.isNone ∨ lower_bound.get! < k) ∧
    (upper_bound.isNone ∨ k < upper_bound.get!)

-- Helper: key ranges properly maintained with sibling ordering
def keyRangesValid : BPlusNode K V order → Prop
  | BPlusNode.leaf _ => True
  | BPlusNode.internal keys children =>
      -- Each child respects its key range bounds relative to siblings
      nodeInKeyRange (children.get! 0) none (some (keys.get! 0)) ∧
      (∀ i, 0 < i ∧ i < keys.length → 
        nodeInKeyRange (children.get! i) (some (keys.get! (i-1))) (some (keys.get! i))) ∧
      nodeInKeyRange (children.get! keys.length) (some (keys.getLast!)) none ∧
      -- Recursively check children
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
