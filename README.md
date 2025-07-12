# B+ Tree in Lean 4

A formal specification and implementation of B+ Trees using the Lean 4 theorem prover.

## Project Structure

- `BPlusTreeLean/Basic.lean` - Basic definitions and utilities
- `BPlusTreeLean/BPlusTree.lean` - B+ Tree specification with invariants and theorems
- `lakefile.lean` - Lake build configuration
- `lean-toolchain` - Lean version specification

## Getting Started

1. Install Lean 4 and Lake: https://leanprover.github.io/lean4/doc/quickstart.html
2. Build the project: `lake build`
3. Open in VS Code with the Lean 4 extension

## Learning Resources

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

## B+ Tree Properties Specified

- Node size invariants
- Key ordering requirements  
- Tree height bounds
- Operation correctness theorems

Use `sorry` placeholders to incrementally prove theorems as you learn Lean.
