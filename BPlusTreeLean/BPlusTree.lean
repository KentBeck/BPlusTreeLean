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
         [DecidableEq K] [Inhabited K] [Inhabited V] {order : Nat}

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

-- Node-specific well-formedness predicates (much cleaner!)

-- Leaf node well-formedness
def leafWellFormed (entries : List (KeyValue K V)) (order : Nat) : Prop :=
  leafSorted entries ∧ 
  entries.length ≤ order - 1 ∧
  entries.length ≥ (order - 1) / 2  -- Minimum occupancy (except root)

-- Internal node well-formedness  
def internalWellFormed (keys : List K) (children : List (BPlusNode K V order)) (order : Nat) : Prop :=
  internalKeysSorted keys ∧
  children.length = keys.length + 1 ∧  -- The crucial invariant!
  validInternalNodeSize children order ∧
  children.length > 0  -- Non-empty children

-- Unified node well-formedness
def nodeWellFormed : BPlusNode K V order → Prop
  | BPlusNode.leaf entries => leafWellFormed entries order
  | BPlusNode.internal keys children => internalWellFormed keys children order

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

-- Phase 1.2: Foundational lemmas for mutual recursive helper functions

-- Key insight: These lemmas establish the basic structural relationships
-- that are needed for the main correctness proofs

-- Lemma: minKeyInChildren = none iff allKeysInChildren = []
theorem minKeyInChildren_none_iff_empty (children : List (BPlusNode K V order)) :
  minKeyInChildren children = none ↔ allKeysInChildren children = [] := by
  induction children with
  | nil => simp [minKeyInChildren, allKeysInChildren]
  | cons child rest ih =>
    simp [minKeyInChildren, allKeysInChildren]
    -- This proof requires the minKeyInSubtree_none_iff_empty theorem to be available
    -- which creates a circular dependency. For now, establish the structure
    sorry

-- Lemma: maxKeyInChildren = none iff allKeysInChildren = []  
theorem maxKeyInChildren_none_iff_empty (children : List (BPlusNode K V order)) :
  maxKeyInChildren children = none ↔ allKeysInChildren children = [] := by
  -- This follows the same pattern as minKeyInChildren_none_iff_empty
  -- but uses maxKeyInSubtree instead of minKeyInSubtree
  sorry

-- Helper lemma: list append equals empty iff both components empty
theorem list_append_eq_nil_iff {α : Type} (l1 l2 : List α) :
  l1 ++ l2 = [] ↔ l1 = [] ∧ l2 = [] := by
  constructor
  · intro h
    cases l1 with
    | nil => 
      simp at h
      exact ⟨rfl, h⟩
    | cons x xs => 
      simp at h
      -- Impossible case: non-empty list append something = []
  · intro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

-- Phase 1.2: Correctness properties for helper functions

-- ⚠️  REVISED STRATEGY: Helper proofs need wellFormed invariants!
-- These proofs require sorted leaves and key separation properties
-- Therefore: Operations first, then helper correctness proofs

-- Property: minKeyInSubtree returns actual minimum key (DEFERRED)
theorem minKeyInSubtree_correct (node : BPlusNode K V order) (k : K) :
  -- wellFormed needed for leafSorted and keyRangesValid properties
  minKeyInSubtree node = some k → ∀ k' ∈ allKeysInSubtree node, k ≤ k' := by
  intro h_min k' h_k'_in
  -- This proof requires:
  -- 1. For leaf nodes: leafSorted to show first key ≤ all other keys
  -- 2. For internal nodes: keyRangesValid + mutual induction on minKeyInChildren
  -- 3. The proper wellFormed assumptions to access these invariants
  -- The structure is correct but needs the full wellFormed context
  sorry

-- Property: maxKeyInSubtree returns actual maximum key (DEFERRED)
theorem maxKeyInSubtree_correct (node : BPlusNode K V order) (k : K) :
  maxKeyInSubtree node = some k → ∀ k' ∈ allKeysInSubtree node, k' ≤ k := by
  intro h_max k' h_k'_in
  -- This proof is analogous to minKeyInSubtree_correct but for maximum
  -- This proof requires:
  -- 1. For leaf nodes: leafSorted to show all keys ≤ last key (via getLast?)
  -- 2. For internal nodes: keyRangesValid + mutual induction on maxKeyInChildren
  -- 3. The proper wellFormed assumptions to access these invariants
  -- The structure mirrors minKeyInSubtree_correct but uses max instead of min
  sorry

-- Property: minKeyInSubtree returns none iff no keys exist 
-- NOTE: For internal nodes in well-formed trees, this is vacuously true (both sides false)
theorem minKeyInSubtree_none_iff_empty (node : BPlusNode K V order) :
  minKeyInSubtree node = none ↔ allKeysInSubtree node = [] := by
  -- This proof works by case analysis on the node structure
  cases node with
  | leaf entries =>
    cases entries with
    | nil => 
      simp [minKeyInSubtree, allKeysInSubtree]
    | cons kv rest =>
      simp [minKeyInSubtree, allKeysInSubtree]
  | internal keys children =>
    simp [minKeyInSubtree, allKeysInSubtree]
    -- Key insight: In well-formed B+ trees, internal nodes always have keys!
    -- allKeysInSubtree = keys ++ allKeysInChildren children
    -- For this to be [], we'd need keys = [] AND allKeysInChildren children = []
    -- But well-formed internal nodes have keys.length > 0 (from internalWellFormed)
    -- Therefore, this case should be impossible in well-formed trees
    constructor
    · intro h_min_none
      -- If we reach this case, the tree violates B+ tree invariants
      -- In a well-formed tree, minKeyInSubtree on internal node should never be none
      -- because either children have keys OR separator keys exist
      sorry -- This case indicates malformed tree - need wellFormed assumption
    · intro h_all_empty  
      -- Similarly, allKeysInSubtree = [] for internal node indicates malformed tree
      -- because it requires keys = [] which violates internal node invariants
      obtain ⟨h_keys_empty, h_children_empty⟩ := h_all_empty
      -- h_keys_empty : keys = [] violates wellFormed internal node invariants
      sorry -- This case indicates malformed tree - need wellFormed assumption

-- Property: maxKeyInSubtree returns none iff no keys exist
-- NOTE: For internal nodes in well-formed trees, this is vacuously true (both sides false)
theorem maxKeyInSubtree_none_iff_empty (node : BPlusNode K V order) :
  maxKeyInSubtree node = none ↔ allKeysInSubtree node = [] := by
  -- For leaf nodes: straightforward. For internal nodes: vacuously true in wellFormed trees
  cases node with
  | leaf entries =>
    cases entries with
    | nil => 
      simp [maxKeyInSubtree, allKeysInSubtree]
    | cons kv rest =>
      simp [maxKeyInSubtree, allKeysInSubtree]
  | internal keys children =>
    simp [maxKeyInSubtree, allKeysInSubtree]
    -- Same insight as minKeyInSubtree: internal nodes in well-formed trees never empty
    -- For maxKeyInSubtree = none on internal node, we'd need keys = [] AND no child keys
    -- But keys = [] violates internalWellFormed invariants
    constructor
    · intro h_max_none
      -- This case indicates malformed tree - internal nodes should always have keys
      sorry -- Need wellFormed assumption to prove this is impossible
    · intro h_all_empty
      -- Similarly, allKeysInSubtree = [] for internal node indicates malformed tree
      obtain ⟨h_keys_empty, h_children_empty⟩ := h_all_empty
      -- h_keys_empty : keys = [] violates wellFormed internal node invariants
      sorry -- Need wellFormed assumption to prove this is impossible

-- Helper: check if node's keys are within given bounds
def nodeInKeyRange (node : BPlusNode K V order) (lower_bound upper_bound : Option K) : Prop :=
  ∀ k ∈ allKeysInSubtree node,
    (lower_bound.isNone ∨ lower_bound.get! < k) ∧
    (upper_bound.isNone ∨ k < upper_bound.get!)

-- Helper: key ranges properly maintained with sibling ordering using min/max
def keyRangesValid : BPlusNode K V order → Prop
  | BPlusNode.leaf _ => True
  | BPlusNode.internal keys children => 
      -- For well-formed internal nodes: keys act as separators between children
      -- children[0] contains keys ≤ keys[0]
      -- children[i] contains keys in range (keys[i-1], keys[i]] 
      -- children[last] contains keys > keys[last]
      children.length = keys.length + 1 ∧
      (∀ i : Nat, i < keys.length → 
        (∀ k ∈ allKeysInSubtree (children.get! i), k ≤ keys.get! i) ∧
        (∀ k ∈ allKeysInSubtree (children.get! (i + 1)), keys.get! i < k))

-- Key span: the range of keys contained in a subtree
def keySpan (node : BPlusNode K V order) : Option (K × K) :=
  match minKeyInSubtree node, maxKeyInSubtree node with
  | some min_k, some max_k => some (min_k, max_k)
  | _, _ => none

-- Helper: check if one key span is contained within another
def keySpanContained (child_span parent_span : Option (K × K)) : Prop :=
  match child_span, parent_span with
  | some (c_min, c_max), some (p_min, p_max) => p_min ≤ c_min ∧ c_max ≤ p_max
  | none, _ => True  -- Empty child span is contained in any parent span
  | some _, none => False  -- Non-empty child can't be contained in empty parent

-- Helper: check if a node is a child of an internal node
def isChildOf (child : BPlusNode K V order) (parent : BPlusNode K V order) : Prop :=
  match parent with
  | BPlusNode.leaf _ => False
  | BPlusNode.internal _ children => child ∈ children

-- Core B+ Tree Property: Child key spans are contained within parent key spans
theorem child_key_span_contained (parent child : BPlusNode K V order) :
  nodeWellFormed parent →
  allNodesWellFormed parent →
  keyRangesValid parent →
  isChildOf child parent →
  keySpanContained (keySpan child) (keySpan parent) := by
  intro h_node_wf h_all_wf h_key_ranges h_child
  -- Now we can use the proper keyRangesValid invariant!
  unfold keySpanContained keySpan
  cases parent with
  | leaf _ => 
    -- Leaves have no children, contradiction
    simp [isChildOf] at h_child
  | internal keys children =>
    -- For internal nodes, keyRangesValid gives us the separator properties
    simp [isChildOf] at h_child
    -- Child is in children list, and keyRangesValid ensures proper key separation
    -- This means child's key range must be contained within parent's range
    -- The detailed proof requires showing min/max relationships
    sorry

-- Note: The key span insight suggests we should prove termination based on
-- key space narrowing rather than structural size, but that requires 
-- proper keyRangesValid implementation first

-- Key insight: We can now use keySpan to reason about containment relationships
-- between parent and child nodes, which is more semantically meaningful 
-- than structural termination for B+ tree proofs

-- Complete well-formed B+ Tree predicate
def wellFormed (tree : BPlusTree K V order) : Prop :=
  validOrder order ∧
  allNodesWellFormed tree.root ∧           -- 1. Recursive well-formedness
  allLeavesAtDepth tree.root tree.height ∧ -- 2. Balanced depth
  keyRangesValid tree.root                  -- 3. Key range separation

-- Phase 2: Implement concrete operations

-- Basic operations (specifications)

-- Helper function: find the index of the child to navigate to
def findChildIndex (keys : List K) (key : K) : Nat :=
  let rec go (idx : Nat) (remaining : List K) : Nat :=
    match remaining with
    | [] => idx
    | k :: rest => 
        if key < k then idx
        else go (idx + 1) rest
  go 0 keys

-- Phase 1: Navigate to the appropriate leaf
def findLeafForKey : BPlusNode K V order → K → List (KeyValue K V)
  | BPlusNode.leaf entries, _ => entries
  | BPlusNode.internal keys children, key =>
      -- Find the appropriate child and recursively navigate
      let childIndex := min (findChildIndex keys key) (children.length - 1)
      findLeafForKey (children.get! childIndex) key
termination_by node => sizeOf node
decreasing_by 
  -- Tree navigation terminates when we reach leaves
  simp_wf
  -- The child node has smaller sizeOf than the parent internal node
  -- This requires proving that elements of a list have smaller sizeOf than the list
  -- For now, this is a fundamental property of inductive data structures
  sorry

-- Phase 2: Search within a fixed-length leaf (simple iteration)
def searchInLeaf (entries : List (KeyValue K V)) (key : K) : Option V :=
  -- Linear search through leaf entries - no recursion, simple termination
  entries.find? (fun kv => kv.key = key) |>.map (·.value)

-- ✅ Phase 2 Correctness: Easy to prove for fixed-length list!
theorem searchInLeaf_correct (entries : List (KeyValue K V)) (key : K) (v : V) :
  searchInLeaf entries key = some v ↔ ⟨key, v⟩ ∈ entries := by
  simp [searchInLeaf]
  -- This follows from List.find? and Option.map properties
  sorry

theorem searchInLeaf_none_iff (entries : List (KeyValue K V)) (key : K) :
  searchInLeaf entries key = none ↔ ∀ v, ⟨key, v⟩ ∉ entries := by
  simp [searchInLeaf]
  -- This follows from List.find? returning none iff no element satisfies predicate
  sorry

-- Combined search operation
def searchInNode (node : BPlusNode K V order) (key : K) : Option V :=
  let leafEntries := findLeafForKey node key
  searchInLeaf leafEntries key

-- Main search operation  
def search (tree : BPlusTree K V order) (key : K) : Option V :=
  searchInNode tree.root key

-- Helper: insert key-value pair into sorted leaf entries
def insertIntoLeaf (entries : List (KeyValue K V)) (key : K) (value : V) : List (KeyValue K V) :=
  let newEntry := ⟨key, value⟩
  -- Find insertion position and insert
  let rec insertSorted (lst : List (KeyValue K V)) : List (KeyValue K V) :=
    match lst with
    | [] => [newEntry]
    | entry :: rest => 
        if key ≤ entry.key then
          if key = entry.key then
            -- Update existing key
            newEntry :: rest
          else
            -- Insert before this entry
            newEntry :: entry :: rest
        else
          -- Continue searching
          entry :: insertSorted rest
  insertSorted entries

-- Helper: insert into a specific node (original unsafe version)
def insertIntoNode : BPlusNode K V order → K → V → BPlusNode K V order
  | BPlusNode.leaf entries, key, value =>
      -- Insert into sorted position in leaf
      BPlusNode.leaf (insertIntoLeaf entries key value)
  | BPlusNode.internal keys children, key, value =>
      -- Find the appropriate child and recursively insert
      let childIndex := min (findChildIndex keys key) (children.length - 1)
      let updatedChild := insertIntoNode (children.get! childIndex) key value
      -- Replace the child in the children list
      BPlusNode.internal keys (children.set childIndex updatedChild)
termination_by node => sizeOf node
decreasing_by 
  -- Structural termination (with sorry for now)
  simp_wf
  sorry

-- Safe version with well-formedness precondition
def insertIntoNodeSafe (node : BPlusNode K V order) 
                       (h : nodeWellFormed node)  -- Contains exactly what we need!
                       (key : K) (value : V) 
                       : BPlusNode K V order :=
  match node with
  | BPlusNode.leaf entries =>
      -- For leaves, we know from h: leafWellFormed entries order
      BPlusNode.leaf (insertIntoLeaf entries key value)
  | BPlusNode.internal keys children =>
      -- For internal nodes, we know from h: internalWellFormed keys children order
      -- This gives us: children.length = keys.length + 1 and children.length > 0
      let childIndex := findChildIndex keys key
      -- Bounds safety: childIndex ≤ keys.length < children.length (from invariant)
      have h_bounds : childIndex < children.length := by
        -- findChildIndex returns ≤ keys.length
        have h_find_bound : findChildIndex keys key ≤ keys.length := by
          -- Prove that findChildIndex always returns ≤ keys.length
          -- This follows from the structure of the recursive function
          -- For now, this is a fundamental property that should hold
          sorry
        -- From internalWellFormed: children.length = keys.length + 1
        have h_struct : children.length = keys.length + 1 := by
          -- Extract from internalWellFormed 
          simp [nodeWellFormed, internalWellFormed] at h
          exact h.2.1
        omega
      let child := children.get ⟨childIndex, h_bounds⟩
      -- For now, use unsafe recursive call (would need to prove child well-formedness)
      let updatedChild := insertIntoNode child key value  
      -- Replace the child
      BPlusNode.internal keys (children.set childIndex updatedChild)

-- Insert operation  
def insert (tree : BPlusTree K V order) (key : K) (value : V) : BPlusTree K V order :=
  let newRoot := insertIntoNode tree.root key value
  { root := newRoot, height := tree.height }

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
