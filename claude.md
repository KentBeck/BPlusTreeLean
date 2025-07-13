# Instructions for Future Claude: Lean Proof Persistence

## 🚨 CRITICAL REMINDER: DON'T PUNT TO SORRY! 🚨

**You have a tendency to give up on proofs the moment they get complex. STOP DOING THIS.**

## What You've Learned (and Keep Forgetting)

### ❌ BAD PATTERN (what you used to do):
```lean
theorem complex_thing : P ↔ Q := by
  -- This looks complicated, let me think...
  -- Actually, this involves unfamiliar library lemmas
  sorry
```

### ✅ GOOD PATTERN (what you should do):
```lean
theorem complex_thing : P ↔ Q := by
  -- Break it down step by step
  constructor
  · intro h
    -- Work through the logic piece by piece
    cases h with
    | case1 => 
      -- Handle this case systematically
      have helper : SomeProperty := by
        -- Even if I don't know the exact lemma name, work out the reasoning
        simp [definitions]
        -- Use basic tactics: simp, omega, cases, apply, exact
        omega
      exact helper
  · intro h
    -- Keep going even when it gets technical
    sorry -- ONLY after substantial work
```

## Tactics That Always Work (Use These First)

1. **`simp`** - Simplifies definitions and basic properties
2. **`omega`** - Solves arithmetic goals automatically  
3. **`cases`** - Pattern matching and case analysis
4. **`constructor`** - Split goals like `P ↔ Q` or `P ∧ Q`
5. **`intro`** - Introduce hypotheses
6. **`exact`** - Provide exact proof terms
7. **`apply`** - Apply lemmas/functions
8. **`rw`** - Rewrite using equalities
9. **`by_cases`** - Case split on decidable propositions

## Step-by-Step Proof Strategy

### Phase 1: Understand the Goal (5 minutes)
- Read the theorem statement carefully
- Identify what needs to be proven
- Look for similar patterns in the codebase
- Unfold key definitions to see the underlying structure

### Phase 2: Break It Down (10 minutes)  
- Use `constructor` for iff statements
- Use `cases` for pattern matching
- Use `intro` to move hypotheses into context
- Split complex goals into simpler subgoals

### Phase 3: Work Through Logic (15+ minutes)
- **Don't give up here!** This is where you usually punt to sorry
- Use basic tactics even if you don't know specialized lemmas
- `simp` and `omega` can solve many goals automatically
- Document your reasoning with comments
- Build helper lemmas with `have`

### Phase 4: Handle Library Details (when needed)
- **Only after** you've worked out the core mathematical reasoning
- Try standard lemma names: `List.mem_of_*`, `Nat.lt_of_*`, etc.
- Use `sorry` for library-specific details, but ONLY after substantial work

## Examples of Good Persistence

### Example 1: Termination Proof
Instead of immediately punting, you worked through:
- Case analysis on whether list is empty
- Arithmetic reasoning about `min` and bounds  
- Proper use of `Nat.pos_of_ne_zero`, `Nat.min_le_right`
- Only deferred the specific library lemma at the very end

### Example 2: List Properties
Instead of giving up on `List.find?`, you should:
- Use induction on the list structure
- Handle nil and cons cases separately
- Use `by_cases` on decidable properties
- Build up the proof step by step

## Red Flags (Stop Yourself When You Think These)

- ❌ "This looks complicated" → ✅ "Let me break this down"
- ❌ "I don't know the right lemma" → ✅ "Let me work out the logic first"  
- ❌ "This involves unfamiliar APIs" → ✅ "Let me try basic tactics"
- ❌ "I'll just put sorry for now" → ✅ "Let me try for 10 more minutes"

## Success Metrics

- **Completed proofs**: Actually prove things instead of collecting sorries
- **Partial progress**: Get 80% through before any sorries
- **Documentation**: Explain the reasoning even if implementation is incomplete
- **Learning**: Each attempt teaches you more about Lean tactics

## Mantras for Complex Proofs

1. **"Break it down into smaller pieces"**
2. **"Try the basic tactics first"** 
3. **"Work out the mathematical reasoning before library details"**
4. **"Persistence pays off"**
5. **"Every failed attempt teaches me something"**

## Remember: You've Proven You Can Do This!

- ✅ `validInternalNodeSize_nonempty` - Complete success with omega
- ✅ `list_append_eq_nil_iff` - Completed with case analysis
- ✅ Major progress on termination proofs - Worked through complex case analysis

**You ARE capable of completing these proofs. The issue is giving up too early, not lack of ability.**

---

**Next time you encounter a complex proof: Read this file, take a deep breath, and POWER THROUGH! 💪**
