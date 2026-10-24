# Graph Conjecture 133

Research on **Conjecture 133** of *Written on the Wall II* (Graffiti.pc / REAL-133): for every connected graph \(G\) on at least two vertices with no \(C_4\) subgraph,
\[
p(G)\ge r(G)+\ell(G),
\]
where \(p(G)\) is the largest order of an induced path, \(r(G)\) is the radius, and \(\ell(G)=S(G)/n\) is the average over vertices \(v\) of \(\alpha(G[N(v)])\).

This repository is a **public snapshot** of accepted computer-assisted results and a paper draft. It is not a claim that REAL-133 is proved.

## Status (as of 2026-10-24 18:00 Asia/Shanghai)

| Result | Status |
|--------|--------|
| Conjecture for \(\ell(G)\le 5\) | Proved (paper Theorems A–F lineage) |
| \(\mathrm{GEN}_3\) | Proved + Lean 4 formalisation (supplement) |
| \(\mathrm{GEN}_4\) | Proved with finite certificate |
| \(\mathrm{ROOT}(q)\) for \(3\le q\le 8\), \(\mathrm{RAD}(r)\) for \(4\le r\le 10\) | Proved (sharp forms as in paper) |
| Continuous window **R35–R40** partial mass theorems toward \(\mathrm{EB}_6\) / triangle-free \(\mathrm{GEN}_6\) | **Accepted** only as referee CORRECT / CORRECT_WITH_FIXES → paper **Theorem G** + Appendix |
| Universal \(\mathrm{EB}_6\), unrestricted triangle-free \(\mathrm{GEN}_6\), \(T_6\), F42, general \(\mathrm{GEN}_K\), \(\mathrm{RAD}(r)\) for \(r\ge 11\), **REAL-133** | **Open** |

Window protocol: Astra prover → separate fresh Astra referee; concurrent Codex cap 2; certificates under `certificates/`. UNVERIFIED claims are **not** theorems.

## Layout

```
paper/           main.tex + main.pdf (draft; author email REDACTED)
certificates/    ROUND_BRANCH_R1 … R40 JSON + SHA-256 sidecars
notes/           RESULTS_TO_2026-10-24.md; excerpted PROGRESS / PROOF_NOTES
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
```

Latest window certificate (R40):

- SHA-256: `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`
- Sessions: `r40_a38_empty` (29C+1CWF+3U), `r40_tf_dfree` (22C+5CWF+4U); overall CWF
- See `notes/RESULTS_TO_2026-10-24.md` for the full R35–R40 bilingual summary

## Intentionally excluded

- Astra/Codex session logs, huge context dumps, lane `scratch/` trees
- Private email addresses (kept as `[REDACTED]` in the public draft)
- Full `data/` computational supplement (Lean build, nauty censuses, lane reports) — see `data/README.md`

## License

No license file is published in this snapshot (upstream repo had none at packaging time). All rights reserved by the author unless a license is added later.

## Citation / contact

Author: Neil Xu (email redacted in the public draft). Please open a GitHub issue for questions about certificates or reproduction requests.
