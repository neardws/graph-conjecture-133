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
| Exact \(M(n)\) for connected strong-\(C_4\)-free \(P_6\)-free graphs | Proved in `paper/main.tex`. Values \(16/7\), \(5/2\), \(8/3\), \(3\), and \(2+2/n\) for \(n\ge 11\), with the extremal graphs unique |
| Structure at \(r=4\), \(p=7\) | Proved: \(C_8\) or the \(C_6\)-extension in the structure theorem; \(S=2n-b-m\), with equality for \(C_8\) and the leafed \(C_6\) |
| Triangle-free \(\mathrm{GEN}_3\), and exactly one triangle | Proved: \(2e\le 3n\), equality only for the Petersen graph. For \(n\ge 10\) the maximum of \(2e\) is \(f(n)=3n-\min\{n-10,\,5+\mathbf{1}_{n\text{ even}}\}\). A graph in the same class with exactly one triangle still satisfies \(S\le 3n\). \(\mathrm{GEN}_3\) with two or more triangles is open |
| REAL-133 for \(\ell\le 3\); for \(r\le 2\) and \(\ell\le 4\); for \(r=4\) and \(\ell\le 4\); for \(r\ge 5\) and \(\ell\le 4\) | Proved (Theorem A). The case \(r=4\), \(p=7\) gives \(\ell\le 2\) |
| The cell \(r=3\), \(p=6\), \(T\ge 2\), \(n\ge 17\), \(3<\ell\le 4-16/n\) | Open. Any counterexample of REAL-133 with \(\ell\le 4\) falls in this cell |
| \(\mathrm{GEN}_4\), \(\mathrm{ROOT}(q)\) for \(q\ge 5\) outside the block class, \(\mathrm{RAD}(r)\) for \(r\ge 5\), unrestricted \(\mathrm{GEN}_6\) | Not theorems of the manuscript. A minimum counterexample to \(\mathrm{GEN}_4\), if one exists, is 2-connected. Certificate JSON is not a checker archive |
| \(\mathrm{ROOT}(3)\), \(\mathrm{ROOT}(4)\), and \(\mathrm{ROOT}(q)\) for every \(q\) when every block is bipartite or a cycle | Proved in `paper/supplement.tex` |
| Continuous window **R35–R40** partial mass theorems toward \(\mathrm{EB}_6\) / triangle-free \(\mathrm{GEN}_6\) | **Accepted** only as referee CORRECT / CORRECT_WITH_FIXES. Not a theorem of the article |
| Rounds **R46–R53** | Sealed certificates under `certificates/`. Partial CORRECT_WITH_FIXES scaffolding only. Not a proof of the six gates. Summary: `notes/RESULTS_TO_2026-11-01.md` |
| Last sealed round | **R53** (`b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`): 5/6 CORRECT_WITH_FIXES; STAR **INCORRECT**. No R54 certificate |
| Six universal gates: EB6/A38, unrestricted TF GEN6, TF-STAR-PRODUCTION6, universal T6, GEN_K/HYBRID, funded RAD → unconditional REAL-133 | **Open**. R49–R53 did not shrink this list |
| **REAL-133** | **Open** (research-open). Non-theorem note: `notes/DISTANCE_ASSESS_R54.md` |

Window protocol: Astra prover → separate fresh Astra referee; certificates under `certificates/`. UNVERIFIED claims are **not** theorems. An INCORRECT session is not a theorem. Do not auto-chain a further round from this snapshot. If work resumes later, the distance note says to attack A38/EB6 class-forcing first.

## Layout

```
paper/           main.tex + main.pdf; supplement.tex + supplement.pdf
                 (JGT/Wiley layout, website preprint)
certificates/    ROUND_BRANCH_R1 … R40 and R46 … R53 JSON + SHA-256 sidecars
notes/           RESULTS_TO_2026-10-24.md (unchanged); RESULTS_TO_2026-11-01.md;
                 DISTANCE_ASSESS_R54.md (non-theorem); excerpted PROGRESS / PROOF_NOTES
data/            pointer README only (full computational supplement not shipped)
PUBLISH_MANIFEST.md
```

## Paper

Revised against the external referee reports of 1 November 2026, including the major restructuring of the extremal function \(M(n)\), the radius-four structure theorem, the exact triangle-free function \(f(n)\), and the one-triangle bound. The title is *Induced Paths, Radius, and Extremal Neighborhood Independence in Graphs without 4-Cycles*. Rooted bounds, endpoint obstructions, high-radius constructions, and the conditional \(\mathrm{GEN}_3\) reduction are in the supplement. REAL-133, \(\mathrm{GEN}_3\) for graphs with two or more triangles, and unrestricted \(\mathrm{GEN}_6\) stay open.

- Article: [`paper/main.tex`](paper/main.tex), [`paper/main.pdf`](paper/main.pdf)
- Supplement: [`paper/supplement.tex`](paper/supplement.tex), [`paper/supplement.pdf`](paper/supplement.pdf)

Both files use the Wiley USG class (Journal of Graph Theory layout) as a website preprint. There is no separate `wiley-jgt` deliverable. The article and the supplement cite each other, so build the article, then the supplement, then the article again:

```bash
cd paper
SP=(-Z search-path=templates/wiley-njd -Z search-path=templates/wiley-njd/images)
tectonic -X compile --keep-intermediates "${SP[@]}" main.tex
tectonic -X compile --keep-intermediates "${SP[@]}" supplement.tex
tectonic -X compile --keep-intermediates "${SP[@]}" main.tex
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
- Private session logs and earlier draft addresses that are not the correspondence line of the preprint
- Full `data/` computational supplement (Lean build, nauty censuses, lane reports) — see `data/README.md`

## License

No license file is published in this snapshot (upstream repo had none at packaging time). All rights reserved by the authors unless a license is added later.

## Citation / contact

Authors: Xingchen Wang (Independent Researcher) and Xincao Xu. Corresponding author: Xincao Xu, Shenzhen Institute for Advanced Study, University of Electronic Science and Technology of China, xc.xu@uestc.edu.cn. Please open a GitHub issue for questions about certificates or reproduction requests.
