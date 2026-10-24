# data/ (pointer)

The manuscript `paper/main.tex` refers to a computational supplement under `data/` (Lean formalisation of GEN₃, stand-alone Python checkers for early rounds, lane reports, referee verdicts, etc.).

**This public snapshot does not ship the full `data/` tree** (lane scratch directories, Codex/Astra session logs, and large context dumps are intentionally excluded).

What *is* published here:

- `../certificates/` — round certificates `ROUND_BRANCH_R1`–`R40` with SHA-256 sidecars
- `../paper/main.pdf` — compiled draft incorporating accepted R35–R40 results (Theorem G / Appendix)
- `../notes/RESULTS_TO_2026-10-24.md` — bilingual window summary

To reproduce a referee check for an early round, see the private work tree checkers named in the paper’s data section, or open an issue on this repository requesting a specific certificate payload.
