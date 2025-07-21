# Proof Style Guidelines

## Theorem Proving Philosophy

When proving theorems, use **modern idiomatic Lean 4** with the following principles:

### Core Guidelines
- ✅ **Use structured proofs with clear reasoning**
- ✅ **Follow mathlib conventions**
- ✅ **Make it mathlib-style**
- ✅ **Use mathlib and tactics**
- ✅ **Use heavy automation**
- ✅ **Prefer automation (simp, linarith) over manual steps**
- ✅ **Make it as concise as possible while staying readable**

### Preferred Tactics & Approach
- **Automation first**: `simp`, `linarith`, `omega`, `tauto`, `finish`
- **Structured reasoning**: Use `constructor`, `cases`, `induction` with clear case labels
- **Mathlib integration**: Leverage existing lemmas and type class instances
- **Conciseness**: Minimize manual proof steps, maximize automation
- **Readability**: Clear structure even when automated

### Anti-Patterns to Avoid
- ❌ Long manual calculations that automation can handle
- ❌ Reinventing lemmas that exist in mathlib
- ❌ Verbose proofs when `simp` or `linarith` suffices
- ❌ Manual case analysis when pattern matching works
- ❌ Ignoring type class resolution capabilities

### Example Style
```lean
theorem example_theorem (x y : ℕ) : x + y = y + x := by
  simp [add_comm]  -- Prefer automation over manual steps

theorem structured_example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor <;> (intro ⟨h1, h2⟩; exact ⟨h2, h1⟩)  -- Concise structured proof
```

This style prioritizes **automation**, **mathlib integration**, and **conciseness** while maintaining **clarity** and **mathematical rigor**.
