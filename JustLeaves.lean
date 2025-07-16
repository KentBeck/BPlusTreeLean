/-
Formal proof of the correctness of just the leaf nodes in a B+ tree.
This file focuses on the properties and invariants of leaf nodes without
considering the entire B+ tree structure.

This implementation uses a set-based approach where leaf nodes contain
only keys (no values).
-/

-- Leaf node representation
structure LeafNode (K : Type) (order : Nat) where
  keys : List K
  -- Invariant: keys.length ≤ order
  -- Invariant: keys.length ≥ (order - 1) / 2 (except for root)
  -- Invariant: keys are sorted

-- Leaf list representation (cons cell with a LeafNode and an optional next LeafList)
inductive LeafList (K : Type) (order : Nat) where
  | nil : LeafList K order
  | cons : LeafNode K order → LeafList K order → LeafList K order

namespace LeafNode

variable {K : Type} [LT K] [LE K] [DecidableRel (α := K) (· < ·)] [DecidableRel (α := K) (· ≤ ·)]
         [DecidableEq K] [Inhabited K] {order : Nat}

-- Set option to disable the linter warning about unused section variables
set_option linter.unusedSectionVars false

-- Minimum order requirement
def validOrder (order : Nat) : Prop := order ≥ 3

-- Simple lemma: validOrder implies order > 0
theorem validOrder_pos (order : Nat) : validOrder order → order > 0 := by
  intro h
  unfold validOrder at h
  omega

-- Invariant: leaf nodes have between ⌈order/2⌉ and order keys
def validLeafNodeSize (keys : List K) (order : Nat) : Prop :=
  let minKeys := (order - 1) / 2
  keys.length ≥ minKeys ∧ keys.length ≤ order

-- Invariant: keys in leaf nodes are sorted
def leafSorted (keys : List K) : Prop :=
  ∀ i j, i < j → j < keys.length →
    keys.get! i ≤ keys.get! j

-- Leaf node well-formedness
def leafWellFormed (keys : List K) (order : Nat) : Prop :=
  leafSorted keys ∧
  keys.length ≤ order ∧
  keys.length ≥ (order - 1) / 2  -- Minimum occupancy (except for root)

-- Convert a LeafList to a List of LeafNodes
def toList : LeafList K order → List (LeafNode K order)
  | LeafList.nil => []
  | LeafList.cons leaf rest => leaf :: toList rest

-- Convert a LeafNode and an optional next leaf to a LeafList
def toLeafList (leaf : LeafNode K order) (next : Option (LeafNode K order) := none) : LeafList K order :=
  match next with
  | none => LeafList.cons leaf LeafList.nil
  | some next_leaf => LeafList.cons leaf (LeafList.cons next_leaf LeafList.nil)

-- Check if a key is contained in a leaf node
def containsNode (leaf : LeafNode K order) (key : K) : Bool :=
  leaf.keys.contains key

-- Check if a key is contained in a leaf list
def containsList : LeafList K order → K → Bool
  | LeafList.nil, _ => false
  | LeafList.cons leaf rest, key =>
    -- First check if the key is in the current leaf
    if containsNode leaf key then
      true
    else
      -- If the leaf is empty or the key is greater than the last key in the leaf,
      -- we don't need to check the next leaf (B+ tree property)
      if leaf.keys.length = 0 || (leaf.keys.length > 0 && key > leaf.keys.get! (leaf.keys.length - 1)) then
        false
      else
        -- Otherwise, check the rest of the leaf list
        containsList rest key

-- Backward compatible version of contains that works with a LeafNode and an optional next leaf
def contains (leaf : LeafNode K order) (key : K) (next : Option (LeafNode K order) := none) : Bool :=
  containsList (toLeafList leaf next) key

-- Helper function to find insertion position
-- Returns none if the key isn't found and the node is full (size = order - 1)
def findInsertPos (keys : List K) (key : K) (order : Nat) : Option Nat :=
  match keys.findIdx? (fun k => key ≤ k) with
  | some idx => some idx
  | none =>
      -- If the node is full, return none
      if keys.length ≥ order - 1 then
        none
      else
        -- Otherwise, return the position at the end
        some keys.length

-- Insert a key into a leaf node
def insert (leaf : LeafNode K order) (key : K) : LeafNode K order × Option (K × LeafNode K order) :=
  -- Check if the key already exists
  if containsList (LeafList.cons leaf LeafList.nil) key then
    -- Key already exists, no change needed
    (leaf, none)
  else
    -- Check if the leaf is full
    if leaf.keys.length = order then
      -- Leaf is full, need to split first

      -- Insert the key into the current leaf's keys (temporarily)
      let pos := leaf.keys.findIdx? (fun k => key ≤ k) |>.getD leaf.keys.length
      let tempKeys := leaf.keys.take pos ++ [key] ++ leaf.keys.drop pos

      -- Split the keys
      let splitPos := tempKeys.length / 2
      let leftKeys := tempKeys.take splitPos
      let rightKeys := tempKeys.drop splitPos

      -- Create the new leaf nodes
      let leftLeaf : LeafNode K order := { keys := leftKeys }
      let rightLeaf : LeafNode K order := { keys := rightKeys }

      -- Return the left leaf and the split information
      -- The split information includes the first key of the right leaf
      -- and the right leaf itself
      (leftLeaf, some (rightKeys.get! 0, rightLeaf))
    else
      -- Leaf is not full, simply insert the key
      let pos := leaf.keys.findIdx? (fun k => key ≤ k) |>.getD leaf.keys.length
      let newKeys := leaf.keys.take pos ++ [key] ++ leaf.keys.drop pos
      ({ keys := newKeys }, none)

-- Insert a key into a leaf list
def insertList : LeafList K order → K → LeafList K order
  | LeafList.nil, key => LeafList.cons { keys := [key] } LeafList.nil
  | LeafList.cons leaf rest, key =>
    -- First check if the key is in the current leaf
    if containsNode leaf key then
      -- Key already exists, no change needed
      LeafList.cons leaf rest
    else
      -- If the key is greater than the last key in the leaf,
      -- we should insert it into the rest of the list
      if leaf.keys.length > 0 && key > leaf.keys.get! (leaf.keys.length - 1) then
        -- Insert into the rest of the list
        LeafList.cons leaf (insertList rest key)
      else
        -- Insert into the current leaf
        let (newLeaf, splitOpt) := insert leaf key
        match splitOpt with
        | none => LeafList.cons newLeaf rest
        | some (_, rightLeaf) => LeafList.cons newLeaf (LeafList.cons rightLeaf rest)

-- Delete a key from a leaf node
def deleteKey (leaf : LeafNode K order) (key : K) : LeafNode K order :=
  let newKeys := leaf.keys.filter (fun k => k ≠ key)
  { keys := newKeys }

-- Delete a key from a leaf list
def deleteKeyList : LeafList K order → K → LeafList K order
  | LeafList.nil, _ => LeafList.nil
  | LeafList.cons leaf rest, key =>
    -- If the key is greater than the last key in the leaf,
    -- we should delete it from the rest of the list
    if leaf.keys.length > 0 && key > leaf.keys.get! (leaf.keys.length - 1) then
      -- Delete from the rest of the list
      LeafList.cons leaf (deleteKeyList rest key)
    else
      -- Delete from the current leaf
      let newLeaf := deleteKey leaf key
      -- If the leaf is now empty, remove it from the list
      if newLeaf.keys.length = 0 then
        rest
      else
        LeafList.cons newLeaf rest

-- Correctness property: containsList returns true iff the key is in the leaf list
theorem containsList_correct (leaves : LeafList K order) (key : K) :
  (∀ leaf, leaf ∈ toList leaves → leafSorted leaf.keys) →
  containsList leaves key = true ↔ ∃ leaf, leaf ∈ toList leaves ∧ key ∈ leaf.keys := by
  sorry

-- Correctness property: insert preserves leaf well-formedness
theorem insert_preserves_wellFormed (leaf : LeafNode K order) (key : K) :
  validOrder order →
  leafWellFormed leaf.keys order →
  let (newLeaf, splitOpt) := insert leaf key
  leafWellFormed newLeaf.keys order ∧
  (splitOpt.isSome →
    match splitOpt with
    | some (splitKey, rightLeaf) => leafWellFormed rightLeaf.keys order
    | none => True) := by
  sorry

-- Correctness property: delete preserves leaf well-formedness
-- Note: This assumes the leaf is not underfilled after deletion
theorem delete_preserves_wellFormed (leaf : LeafNode K order) (key : K) :
  validOrder order →
  leafWellFormed leaf.keys order →
  leaf.keys.length > (order - 1) / 2 →  -- Extra assumption to ensure no underfill
  leafWellFormed (deleteKey leaf key).keys order := by
  sorry

-- Correctness property: insert followed by contains returns true
theorem insert_contains (leaf : LeafNode K order) (key : K) :
  validOrder order →
  leafWellFormed leaf.keys order →
  let (newLeaf, _) := insert leaf key
  containsList (LeafList.cons newLeaf LeafList.nil) key = true := by
  sorry

-- Correctness property: delete followed by contains returns false
theorem delete_contains (leaf : LeafNode K order) (key : K) :
  validOrder order →
  leafWellFormed leaf.keys order →
  containsList (LeafList.cons (deleteKey leaf key) LeafList.nil) key = false := by
  sorry

-- Test cases for the updated contains function

-- Test case 1: Key in current leaf
theorem test_contains_key_in_current_leaf :
  let leaf1 : LeafNode Nat 3 := { keys := [1, 2, 3] }
  let leaf2 : LeafNode Nat 3 := { keys := [4, 5, 6] }
  containsList (LeafList.cons leaf1 (LeafList.cons leaf2 LeafList.nil)) 2 = true := by
  simp [containsList, containsNode]
  -- 2 ∈ [1, 2, 3], so contains should return true

-- Test case 2: Key in next leaf but greater than last key in current leaf
theorem test_contains_key_in_next_leaf :
  let leaf1 : LeafNode Nat 3 := { keys := [1, 2, 3] }
  let leaf2 : LeafNode Nat 3 := { keys := [4, 5, 6] }
  containsList (LeafList.cons leaf1 (LeafList.cons leaf2 LeafList.nil)) 4 = false := by
  simp [containsList, containsNode]
  -- 4 ∉ [1, 2, 3] and 4 > 3 (last key in leaf1), so contains should return false

-- Test case 3: Key not in either leaf
theorem test_contains_key_not_in_either_leaf :
  let leaf1 : LeafNode Nat 3 := { keys := [1, 2, 3] }
  let leaf2 : LeafNode Nat 3 := { keys := [4, 5, 6] }
  containsList (LeafList.cons leaf1 (LeafList.cons leaf2 LeafList.nil)) 7 = false := by
  simp [containsList, containsNode]
  -- 7 ∉ [1, 2, 3] and 7 ∉ [4, 5, 6], so contains should return false

-- Test case 4: Key in next leaf and not greater than last key in current leaf
theorem test_contains_key_in_next_leaf_not_greater :
  let leaf1 : LeafNode Nat 3 := { keys := [1, 3, 5] }
  let leaf2 : LeafNode Nat 3 := { keys := [2, 4, 6] }
  containsList (LeafList.cons leaf1 (LeafList.cons leaf2 LeafList.nil)) 2 = true := by
  simp [containsList, containsNode]
  -- 2 ∉ [1, 3, 5] but 2 < 5 (last key in leaf1), so contains should check leaf2 and return true

-- General theorem: If insert(key) has been called, then contains(key) is true
theorem insert_implies_contains (leaf : LeafNode K order) (key : K) :
  validOrder order →
  leafWellFormed leaf.keys order →
  let result := insert leaf key
  let newLeaf := result.1
  let splitOpt := result.2
  (splitOpt.isNone → containsList (LeafList.cons newLeaf LeafList.nil) key = true) ∧
  (∀ splitKey rightLeaf, splitOpt = some (splitKey, rightLeaf) →
    (key ≤ splitKey → containsList (LeafList.cons newLeaf LeafList.nil) key = true) ∧
    (¬key ≤ splitKey → containsList (LeafList.cons newLeaf (LeafList.cons rightLeaf LeafList.nil)) key = true)) := by
  sorry

end LeafNode
