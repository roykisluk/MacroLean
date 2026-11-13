# MacroLean

A template for checking economic models in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4). You write a model's
definitions and results as Lean theorems, and Lean checks every step of every proof.

Why bother: a formal check finds what a careful reading misses. In private model notes,
this workflow found an assumption the results needed but the notes never stated, an
equilibrium that does not exist for some parameter values, and a weak inequality that
was really strict.

The repo ships one small worked example, `CES/Demand.lean` (textbook CES demand: shares
sum to one, demand exhausts the budget, indirect utility is `y / P`).

## Quick start

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # installs Lean's version manager
git clone https://github.com/roykisluk/MacroLean && cd MacroLean
lake exe cache get        # downloads a prebuilt Mathlib (a few GB); skip this and the build takes hours
lake build                # checks every proof
lake env lean checks/ces_axioms.lean
```

## The workflow

1. **One folder per model.** A model `Foo` lives in `Foo/`, with a root file `Foo.lean`
   that imports its files, and a `[[lean_lib]] name = "Foo"` entry in `lakefile.toml`
   (add it to `defaultTargets`). All models share one Mathlib build, so a new model
   costs no extra build time.
2. **Header first.** Each model file opens with a doc comment that names the source
   (paper, notes, version) and lists **what is checked** and **what is not**, with the
   reason. Results proved only in a weaker form are listed as such. This makes the limits
   of the check visible to anyone reading it.
3. **Prove the results.** One theorem per lemma, proposition or equation of the source.
   Keep the names close to the source (`share_sum`, `budget`, ...).
4. **The axiom check.** `checks/<model>_axioms.lean` has one `#print axioms` line per
   result. Run `lake env lean checks/<model>_axioms.lean`: every line must list only
   `propext`, `Classical.choice` and `Quot.sound`. A `sorryAx` means a proof was skipped.
   This is the one command a coauthor or referee needs to trust the whole file.
5. **Log what you find.** Keep a dated log (e.g. in `CLAUDE.md`) of slips in the source,
   missing assumptions, and anything left unformalized. Findings are the point.

## Pitfalls

- Definitions on `ℝ` need `noncomputable section`.
- `rw [← hab]` with `hab : a + b = 1` rewrites *every* `1` in the goal; use
  `linear_combination k * hab` instead.
- An equality with one division: `rw [eq_div_iff h]; linear_combination ...`.
- Comparing two ratios: `rw [div_lt_iff₀ h, div_mul_eq_mul_div, lt_div_iff₀ h']`, then
  `linarith` with a `ring` identity.
- `field_simp` sometimes closes the goal and sometimes leaves a `ring` goal. Try
  `field_simp <;> ring`, then keep what the linter says.
- Real powers (`x ^ (y : ℝ)`) need `0 ≤ x` for most rewrite lemmas (`rpow_add`,
  `mul_rpow`, `div_rpow`); carry positivity facts as hypotheses.
- `push_neg` is deprecated in recent Mathlib (`push Not`); `Classical.not_imp` avoids it.
- [MathEconLib](https://github.com/matheconlib/matheconlib) adds economics definitions,
  but (as of late 2026) has no search/matching, Bellman-equation or Nash-bargaining
  module, and ships no prebuilt cache: its first build compiles it. To use it, add it as
  a `[[require]]` pinned by commit and set `lean-toolchain` to its toolchain.

## License

MIT
