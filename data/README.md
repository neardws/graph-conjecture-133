# data/ (pointer)

The manuscript `paper/main.tex` refers to a computational supplement under `data/` (Lean formalisation of GEN₃, stand-alone Python checkers for early rounds, lane reports, referee verdicts, etc.).

**This public snapshot does not ship the full `data/` tree** (lane scratch directories, Codex/Astra session logs, and large context dumps are intentionally excluded).

What *is* published here:

- `../certificates/` — round certificates `ROUND_BRANCH_R1`–`R40` and `R46`–`R53` with SHA-256 sidecars (no R41–R45 files and no R54 certificate in this snapshot)
- `../paper/main.pdf` — website preprint (JGT R12–R14, 20 pages). Theorem 5.9 is REAL-133 for every connected graph with \(\ell\le 4\). The real-valued conjecture for \(\ell>4\) is open. Certificate JSON and the round notes are the archive of earlier rounds.
- `../notes/RESULTS_TO_2026-10-24.md` — bilingual window summary through R40
- `../notes/RESULTS_TO_2026-11-01.md` — bilingual summary of the R46–R53 scaffolding certificates
- `../notes/DISTANCE_ASSESS_R54.md` — non-theorem strategy note (not a certificate)

To reproduce a referee check for an early round, see the private work tree checkers named in the paper’s data section, or open an issue on this repository requesting a specific certificate payload.
