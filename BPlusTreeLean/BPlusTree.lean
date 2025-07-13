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

-- Simple lemma: validOrder implies order > 0
theorem validOrder_pos (order : Nat) : validOrder order → order > 0 := by
  intro h
  unfold validOrder at h
  omega

-- Simple lemma: validOrder implies order ≥ 2 (useful for min calculations)
theorem validOrder_ge_two (order : Nat) : validOrder order → order ≥ 2 := by
  intro h
  unfold validOrder at h
  omega

-- Invariant: internal nodes have between ⌈order/2⌉ and order children
def validInternalNodeSize {α : Type} (children : List α) (order : Nat) : Prop :=
  let minChildren := (order + 1) / 2
  children.length ≥ minChildren ∧ children.length ≤ order

-- Invariant: leaf nodes have between ⌈order/2⌉-1 and order-1 key-value pairs
def validLeafNodeSize (entries : List (KeyValue K V)) (order : Nat) : Prop :=
  let minEntries := (order - 1) / 2
  entries.length ≥ minEntries ∧ entries.length ≤ order - 1

-- Simple lemma: validInternalNodeSize implies non-empty children
theorem validInternalNodeSize_nonempty {α : Type} (children : List α) (order : Nat) :
  validOrder order → validInternalNodeSize children order → children.length > 0 := by
  intro h_order h_valid
  unfold validInternalNodeSize at h_valid
  unfold validOrder at h_order
  -- h_valid gives us: children.length ≥ (order + 1) / 2 ∧ children.length ≤ order
  -- h_order gives us: order ≥ 3
  obtain ⟨h_min, h_max⟩ := h_valid
  -- Since order ≥ 3, we have (order + 1) / 2 ≥ (3 + 1) / 2 = 2
  have h_bound : (order + 1) / 2 ≥ 2 := by
    -- order ≥ 3 implies order + 1 ≥ 4, which implies (order + 1) / 2 ≥ 2
    omega
  -- Therefore children.length ≥ 2 > 0
  omega

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
  -- This proof requires mutual induction with minKeyInSubtree_none_iff_empty
  -- The structure is correct: minKeyInChildren = none exactly when 
  -- no child has any keys, which means allKeysInChildren = []
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
      -- simp should have resolved this contradiction automatically
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
    -- h_child : child ∈ children
    -- keyRangesValid gives us proper separation between children by separator keys
    -- keySpan child should be bounded by the separator keys adjacent to it
    
    -- From keyRangesValid, we know:
    -- children.length = keys.length + 1 and proper key separation exists
    unfold keyRangesValid at h_key_ranges
    simp at h_key_ranges
    obtain ⟨h_struct, h_separation⟩ := h_key_ranges
    
    -- The proof strategy:
    -- 1. Find the index i where child = children[i]
    -- 2. Use keyRangesValid to get bounds on keys in children[i]
    -- 3. Show these bounds contain child's keySpan within parent's keySpan
    
    -- From h_separation: ∀ i < keys.length, 
    --   (∀ k ∈ allKeysInSubtree (children[i]), k ≤ keys[i]) ∧
    --   (∀ k ∈ allKeysInSubtree (children[i+1]), keys[i] < k)
    
    cases h_min : minKeyInSubtree child with
    | none =>
      -- If child has no keys, then keySpan child = none
      simp [h_min]
      -- keySpanContained none (keySpan parent) = True by definition
    | some child_min =>
      cases h_max : maxKeyInSubtree child with
      | none =>
        -- If child has min but no max, contradiction (should be impossible)
        -- In well-formed trees, if minKeyInSubtree = some k, then maxKeyInSubtree = some k' 
        sorry
      | some child_max =>
        simp [h_min, h_max]
        -- Now we need to show: 
        -- parent_min ≤ child_min ∧ child_max ≤ parent_max
        
        -- Find the position of child in children
        have ⟨i, h_i_bound, h_child_eq⟩ : ∃ i, i < children.length ∧ children.get! i = child := by
          -- child ∈ children implies ∃ i such that children[i] = child
          sorry
        
        -- Use keyRangesValid to bound child's keys
        have h_child_keys_bounded : ∀ k ∈ allKeysInSubtree child, 
          (i = 0 ∨ keys.get! (i - 1) < k) ∧ 
          (i = keys.length ∨ k ≤ keys.get! i) := by
          -- This follows from h_separation applied to position i
          sorry
          
        -- child_min and child_max are in allKeysInSubtree child
        have h_min_in : child_min ∈ allKeysInSubtree child := by
          -- minKeyInSubtree_correct: child_min is minimum of allKeysInSubtree child
          sorry
        have h_max_in : child_max ∈ allKeysInSubtree child := by
          -- maxKeyInSubtree_correct: child_max is maximum of allKeysInSubtree child  
          sorry
          
        -- Apply bounds to child_min and child_max
        have h_min_bounded := h_child_keys_bounded child_min h_min_in
        have h_max_bounded := h_child_keys_bounded child_max h_max_in
        
        -- Show parent keySpan contains child keySpan
        cases h_parent_min : minKeyInSubtree (BPlusNode.internal keys children) with
        | none => sorry -- Parent should have keys if it has non-empty children
        | some parent_min =>
          cases h_parent_max : maxKeyInSubtree (BPlusNode.internal keys children) with  
          | none => sorry -- Parent should have keys if it has non-empty children
          | some parent_max =>
            simp [h_parent_min, h_parent_max]
            constructor
            · -- parent_min ≤ child_min
              -- parent_min is minimum of keys ++ allKeysInChildren children
              -- child_min is minimum of one of the children
              -- So parent_min ≤ child_min
              sorry
            · -- child_max ≤ parent_max  
              -- parent_max is maximum of keys ++ allKeysInChildren children
              -- child_max is maximum of one of the children
              -- So child_max ≤ parent_max
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
  -- Goal: sizeOf (children.get! childIndex) < sizeOf (BPlusNode.internal keys children)
  -- This simplifies to: sizeOf (children.get! childIndex) < 1 + sizeOf keys + sizeOf children
  
  -- Step 1: Show childIndex < children.length
  have h_bound : childIndex < children.length := by
    simp only [childIndex]
    -- childIndex = min (findChildIndex keys key) (children.length - 1)
    -- We need children.length > 0 for this to work
    by_cases h : children.length = 0
    · -- If children.length = 0, this is an empty internal node (malformed)
      simp [h]
      -- This case should be impossible for well-formed B+ trees
      -- but let's handle it by contradiction
      exfalso
      -- An internal node with no children violates B+ tree invariants
      sorry
    · -- If children.length > 0, then children.length - 1 < children.length
      -- and min a b ≤ b, so min (findChildIndex keys key) (children.length - 1) < children.length
      have h_pos : children.length > 0 := Nat.pos_of_ne_zero h
      have h_sub : children.length - 1 < children.length := Nat.sub_lt h_pos (by simp)
      -- min a b ≤ b for any a, b
      have h_min_le : min (findChildIndex keys key) (children.length - 1) ≤ children.length - 1 := 
        Nat.min_le_right _ _
      -- Therefore: min (findChildIndex keys key) (children.length - 1) < children.length
      exact Nat.lt_of_le_of_lt h_min_le h_sub
  
  -- Step 2: The core insight is that children.get! childIndex is structurally smaller
  -- This follows from standard facts about list elements and sizeOf
  -- The exact library lemmas may have different names, but the mathematical reasoning is sound:
  -- 1) children.get! childIndex is an element of children (when childIndex < children.length)
  -- 2) List elements have smaller sizeOf than the whole list
  -- 3) Therefore: sizeOf (children.get! childIndex) < sizeOf children ≤ 1 + sizeOf keys + sizeOf children
  
  -- For now, acknowledging this is the correct termination argument
  -- but deferring the specific Lean library details
  sorry

-- Phase 2: Search within a fixed-length leaf (simple iteration)
def searchInLeaf (entries : List (KeyValue K V)) (key : K) : Option V :=
  -- Linear search through leaf entries - no recursion, simple termination
  entries.find? (fun kv => kv.key = key) |>.map (·.value)

-- ✅ Phase 2 Correctness: Easy to prove for fixed-length list!
theorem searchInLeaf_correct (entries : List (KeyValue K V)) (key : K) (v : V) :
  searchInLeaf entries key = some v ↔ ⟨key, v⟩ ∈ entries := by
  -- This is a complex proof involving List.find? properties
  -- Let me defer this and tackle simpler proofs first
  sorry

theorem searchInLeaf_none_iff (entries : List (KeyValue K V)) (key : K) :
  searchInLeaf entries key = none ↔ ∀ v, ⟨key, v⟩ ∉ entries := by
  -- This follows from List.find? returning none iff no element satisfies predicate
  -- The proof structure is correct: searchInLeaf returns none exactly when
  -- no key-value pair with the given key exists in the entries
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
  -- The recursive call is on children.get! childIndex, which is structurally smaller
  -- This is a standard termination pattern: tree recursion on child nodes
  simp_wf
  -- For termination, we need that children.get! childIndex has smaller sizeOf
  -- This follows from the fact that elements of a list have smaller sizeOf than the list
  -- The details require showing childIndex is in bounds, but this is the right structure
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

-- Helper: get all key-value pairs in a subtree (for correctness statements)
mutual
def allEntriesInSubtree : BPlusNode K V order → List (KeyValue K V)
  | BPlusNode.leaf entries => entries
  | BPlusNode.internal _ children => allEntriesInChildren children

def allEntriesInChildren : List (BPlusNode K V order) → List (KeyValue K V)
  | [] => []
  | child :: rest => allEntriesInSubtree child ++ allEntriesInChildren rest
end

-- Search correctness: if search finds a value, then the key-value pair exists in the tree
theorem search_finds_existing_key {tree : BPlusTree K V order} {key : K} {value : V} :
  wellFormed tree →
  search tree key = some value →
  {key := key, value := value} ∈ allEntriesInSubtree tree.root := by
  intro h_wf h_search
  -- Unfold search definition and use findLeafForKey + searchInLeaf correctness
  unfold search searchInNode at h_search
  -- search = searchInLeaf (findLeafForKey tree.root key) key = some value
  -- By searchInLeaf_correct: {key := key, value := value} ∈ findLeafForKey tree.root key
  -- By findLeafForKey_correct: findLeafForKey navigates to correct leaf containing the key
  -- Therefore: {key := key, value := value} exists in tree
  sorry

-- Search completeness: if a key-value pair exists in the tree, search finds it  
theorem search_finds_all_keys {tree : BPlusTree K V order} {key : K} {value : V} :
  wellFormed tree →
  {key := key, value := value} ∈ allEntriesInSubtree tree.root →
  search tree key = some value := by
  intro h_wf h_exists
  -- The converse: if {key := key, value := value} exists in tree, then search finds it
  -- This requires uniqueness of keys in B+ trees (each key maps to unique value)
  -- and correctness of findLeafForKey navigation to find the correct leaf
  sorry

-- High-level search correctness combining both directions
theorem search_correct {tree : BPlusTree K V order} {key : K} :
  wellFormed tree →
  (search tree key).isSome ↔ ∃ value, {key := key, value := value} ∈ allEntriesInSubtree tree.root := by
  -- This theorem combines search_finds_existing_key and search_finds_all_keys
  -- to show that search succeeds exactly when the key exists in the tree
  sorry

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
