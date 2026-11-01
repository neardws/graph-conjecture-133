# Graph Conjecture 133

Research on **Conjecture 133** of *Written on the Wall II* (Graffiti.pc / REAL-133): for every connected graph \(G\) on at least two vertices with no \(C_4\) subgraph,
\[
p(G)\ge r(G)+\ell(G),
\]
where \(p(G)\) is the largest order of an induced path, \(r(G)\) is the radius, and \(\ell(G)=S(G)/n\) is the average over vertices \(v\) of \(\alpha(G[N(v)])\).

This repository is a **public snapshot** of accepted computer-assisted results and a paper draft. It is not a claim that REAL-133 is proved.

## Status (as of 2026-11-01 Asia/Shanghai)

Continuous proving is stopped. This snapshot is not a claim that REAL-133 is proved.

| Result | Status |
|--------|--------|
| Conjecture for \(\ell(G)\le 5\) | Proved (paper Theorems A–F lineage) |
| \(\mathrm{GEN}_3\) | Proved + Lean 4 formalisation (supplement) |
| \(\mathrm{GEN}_4\) | Proved with finite certificate |
| \(\mathrm{ROOT}(q)\) for \(3\le q\le 8\), \(\mathrm{RAD}(r)\) for \(4\le r\le 10\) | Proved (sharp forms as in paper) |
| Continuous window **R35–R40** partial mass theorems toward \(\mathrm{EB}_6\) / triangle-free \(\mathrm{GEN}_6\) | **Accepted** only as referee CORRECT / CORRECT_WITH_FIXES → paper **Theorem G** |
| Rounds **R46–R53** | Sealed certificates under `certificates/`. Partial CORRECT_WITH_FIXES scaffolding only. Not a proof of the six gates. Summary: `notes/RESULTS_TO_2026-11-01.md` |
| Last sealed round | **R53** (`b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`): 5/6 CORRECT_WITH_FIXES; STAR **INCORRECT**. No R54 certificate |
| Six universal gates: EB6/A38, unrestricted TF GEN6, TF-STAR-PRODUCTION6, universal T6, GEN_K/HYBRID, funded RAD → unconditional REAL-133 | **Open**. R49–R53 did not shrink this list |
| **REAL-133** | **Open** (research-open). Non-theorem note: `notes/DISTANCE_ASSESS_R54.md` |

Window protocol: Astra prover → separate fresh Astra referee; certificates under `certificates/`. UNVERIFIED claims are **not** theorems. An INCORRECT session is not a theorem. Do not auto-chain a further round from this snapshot. If work resumes later, the distance note says to attack A38/EB6 class-forcing first.

## Layout

```
paper/           main.tex + main.pdf (draft; Neil Xu email REDACTED; Xingchen Wang name only)
certificates/    ROUND_BRANCH_R1 … R40 and R46 … R53 JSON + SHA-256 sidecars
notes/           RESULTS_TO_2026-10-24.md (unchanged); RESULTS_TO_2026-11-01.md;
                 DISTANCE_ASSESS_R54.md (non-theorem); excerpted PROGRESS / PROOF_NOTES
data/            pointer README only (full computational supplement not shipped)
PUBLISH_MANIFEST.md
```

## Paper

- Source: [`paper/main.tex`](paper/main.tex)
- PDF: [`paper/main.pdf`](paper/main.pdf)

Compile (needs a TeX engine that can fetch AMS packages), e.g.:

```bash
cd paper && tectonic -X compile main.tex
# or: latexmk -pdf main.tex
```

## Referee protocol (high level)

1. A prover session writes claims + finite certificates / reports.
2. A **fresh** referee session (separate Astra/Codex lane) recomputes or audits and emits `verdict.json` with per-claim statuses.
3. Round certificates (`ROUND_BRANCH_R*_CERTIFICATE.json`) are built **only** from referee verdicts.
4. The paper and this archive treat a claim as accepted iff the referee mark is `CORRECT` or `CORRECT_WITH_FIXES`.

To check integrity of a certificate file:

```bash
cd certificates
sha256sum -c ROUND_BRANCH_R40_CERTIFICATE.sha256
sha256sum -c ROUND_BRANCH_R53_CERTIFICATE.sha256
```

R40 certificate (end of the 2026-10-24 window):

- SHA-256: `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`
- Sessions: `r40_a38_empty` (29C+1CWF+3U), `r40_tf_dfree` (22C+5CWF+4U); overall CWF
- See `notes/RESULTS_TO_2026-10-24.md` for the R35–R40 bilingual summary

Last sealed certificate (R53, 2026-11-01 snapshot):

- SHA-256: `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`
- Five sessions CORRECT_WITH_FIXES; STAR INCORRECT. The six universal gates stay open
- R46–R53 hashes and the scaffolding-versus-open split: `notes/RESULTS_TO_2026-11-01.md`
- Strategy note, not a theorem: `notes/DISTANCE_ASSESS_R54.md` (`ce156ef7fe942b391cd41fd88e29db404cc660a6b7cd2070968acce4f69f4dde`)

## Intentionally excluded

- Astra/Codex session logs, huge context dumps, lane `scratch/` trees
- Private email addresses (kept as `[REDACTED]` in the public draft)
- Full `data/` computational supplement (Lean build, nauty censuses, lane reports) — see `data/README.md`

## License

No license file is published in this snapshot (upstream repo had none at packaging time). All rights reserved by the authors unless a license is added later.

## Citation / contact

Authors: Xingchen Wang (first; name only), Neil Xu (second; email redacted in the public draft). Please open a GitHub issue for questions about certificates or reproduction requests.
