# Phase 6 brief (AI for Math / Neil standing order)

Baseline: continue PR #22 / branch `lean/phase5-lemma59-section3` from current tip.
Model: gpt-6.1-sol
Scope: `lean/`; CI one-liner allowed: `.github/workflows/lean.yml` `build-dir: lean` → `lake-package-directory: lean` (done if present).
P0: `theorem_3_6`
P1: `lemma_4_1` → `theorem_4_2` → `corollary_4_4_mass` → `corollary_4_5`
Out of scope: `lemma_5_2`, `lemma_5_4`, `theorem_5_5`, `theorem_5_6_noniso`, `theorem_5_6`, `theorem_5_7`, `theorem_5_10`, `theorem_5_11`
Constraints: Lean 4.35.0 + Mathlib v4.35; no new handwritten axioms; keep the 5 external axioms; GenK/Rad remain open; `lake build` green; honestly update `lean/README` sorry inventory; do not merge; do not claim Lean verified.
Attention answer: YES — change `lean.yml` as above (already applied if this note exists after the CI commit).
