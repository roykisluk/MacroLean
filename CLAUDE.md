# MacroLean

Public template for checking economic models in Lean 4 + Mathlib. Workflow and pitfalls: `README.md`.
Working copy and builds on tbox (`~/projects/MacroLean`); Lean is not installed on the Mac.

## Rules
- Public repo: only textbook or published material here. Unpublished coauthor models stay in the
  private `ModelLean`.
- Toolchain is pinned to Mathlib's `v4.35.0` tag (`lean-toolchain`, `lakefile.toml`).
- Before every push: `lake build` passes and `lake env lean checks/ces_axioms.lean` lists only
  propext, Classical.choice, Quot.sound.

## Lesson log
- 2026-11-13 — Created from ModelLean's layout. Started fast by copying ModelLean's
  `.lake/packages` (minus matheconlib), then `lake update`: no download, no rebuild. The CES example
  depends on Mathlib only. Build warns that Mathlib "is designed for use with the module system";
  harmless.
- 2026-11-13 — Claude's auto mode refuses `gh repo create --public` (public upload); repo was created
  private and Roy flips it public himself.
