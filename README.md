# Induced Paths, Radius, and Extremal Neighbourhood Independence in Graphs without 4-Cycles

Xingchen Wang (Independent Researcher, skywalkerwang98@gmail.com) and Xincao Xu (corresponding author; Shenzhen Institute for Advanced Study, University of Electronic Science and Technology of China, xc.xu@uestc.edu.cn). Credit for technical checking and for drafting assistance is in the Acknowledgments of the preprint.

This repository is the website preprint of that paper, set in the Journal of Graph Theory layout (Wiley USG class). The deliverable is [`paper/main.pdf`](paper/main.pdf) (25 pages). There is no separate supplement: the one-triangle bound is proved by hand in the article, and the two-triangle search is Appendix A.

For a graph \(G\) on \(n\ge 2\) vertices, \(p(G)\) is the largest order of an induced path, \(r(G)\) is the radius, and
\[
\ell(G)=\frac1n\sum_{v\in V(G)}\alpha\bigl(G[N(v)]\bigr),
\]
where \(S(G)\) is the sum in the numerator. Write \(P_k\) for the path on \(k\) vertices. A graph is *strong \(C_4\)-free* when it contains no 4-cycle as a subgraph. Conjecture 133 of *Written on the Wall II* (Graffiti.pc), entry 133 dated July 12, 2005, in the real-valued form called REAL-133, says that every connected graph on at least two vertices satisfies \(p(G)\ge r(G)+\ell(G)^{c_{C_4}(G)}\). That list is the primary source. A secondary record is the Formal Conjectures file at commit `5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e`, the merge of pull request [#5727](https://github.com/google-deepmind/formal-conjectures/pull/5727), which removed the floor function. Formalization of any of these statements is separate from the mathematical status in the table below. Nothing in this repository is claimed to be Lean-verified from an empty axiom set. [`lean/`](lean/) is a Lean 4 and Mathlib development of the numbered lemmas and theorems: the numbered inventory has **0** `sorry` and **0** `admit`, five literature axioms remain in [`lean/AXIOMS.md`](lean/AXIOMS.md), and finite certificates use `native_decide`, which trusts the Lean compiler and runtime. `cd lean && lake build` typechecks the package on Lean 4.35.0 with Mathlib v4.35.0. The inventory is in [`lean/README.md`](lean/README.md).

Every connected strong \(C_4\)-free graph with no induced path on seven vertices satisfies \(S\le 3n\), with equality only for the Petersen graph. Combined with the classification of the connected strong \(C_4\)-free graphs of radius 4 and induced-path order 7, this bound yields REAL-133 for every connected graph with \(\ell\le 4\), at every radius. When the graph contains at least two triangles, the argument uses the finite certificate below. The same arguments determine the maximum of \(\ell\) over connected strong \(C_4\)-free graphs with no induced path on six vertices, with a unique extremal graph for every order \(n\ge 7\); classify the connected strong \(C_4\)-free graphs of radius 4 and induced-path order 7; and determine, for every \(n\ge 10\), the maximum number of edges in a connected triangle-free strong \(C_4\)-free graph with no induced path on seven vertices, together with all extremal graphs. REAL-133 remains open for \(\ell>4\). No structural classification for radius \(r\ge 5\) is proved.

## Results

The boundary in the preprint is the concluding section (Section 6 of `paper/main.pdf`).

| Statement | Reference | Status |
|-----------|-----------|--------|
| Exact \(M(n)\) and a unique extremal graph for every connected strong \(C_4\)-free \(P_6\)-free graph of order \(n\ge 7\) | Theorem 3.6 | Proved |
| Structure of connected strong \(C_4\)-free graphs with radius 4 and induced-path order 7; the formula \(S=2n-b-m\); the equality cases | Theorem 4.2, Corollaries 4.4 and 4.5 | Proved |
| \(2e\le 3n\) for connected triangle-free strong \(C_4\)-free \(P_7\)-free graphs, with equality only for the Petersen graph | Theorem 5.5 | Proved |
| Exact maximum of \(2e\), and all extremal graphs, in that triangle-free class, for every \(n\ge 10\) | Theorem 5.6 | Proved |
| \(S\le 3n\) for every connected strong \(C_4\)-free \(P_7\)-free graph, with equality only for the Petersen graph. At most one triangle is the hand proof in Theorem 5.7; at least two triangles uses the closed search in Lemma 5.9 | Theorems 5.7 and 5.10, Lemma 5.9 | Proved |
| Induced-path order 6 forces \(S\le 3n-1\) and \(\ell<3\). On each of \((r,p)=(2,6)\) and \((3,6)\) the supremum of \(\ell\) is 3 and is unattained | Corollary 6.3 | Proved |
| REAL-133 for every connected graph with \(\ell\le 4\), at every radius. The floor form holds for every connected graph with \(\ell<5\) | Theorem 5.11, Remark 5.12 | Proved |
| Real-valued REAL-133 for \(\ell>4\), and REAL-133 with no restriction on \(\ell\). No structural classification for radius \(r\ge 5\) | Section 6 | Open |
| For every \(n\ge 10\), the maximum of \(S\) over connected strong \(C_4\)-free \(P_7\)-free graphs equals \(f(n)\), attained only by the extremal graphs of Theorem 5.6 | Conjecture 6.4 | Open |

**Theorem 3.6.** For connected strong \(C_4\)-free \(P_6\)-free graphs,
\[
M(n)=\begin{cases}
16/7 & \text{if }n=7,\\
5/2 & \text{if }n=8,\\
8/3 & \text{if }n=9,\\
3 & \text{if }n=10,\\
2+2/n & \text{if }n\ge 11.
\end{cases}
\]
The extremal graph is unique for every \(n\ge 7\): the Petersen graph \(P\) when \(n=10\), \(P-v\) when \(n=9\), the graph \(H_8\) when \(n=8\), and the graph \(\Gamma_{n-7}\) when \(n=7\) and when \(n\ge 11\) (a 6-cycle, a vertex adjacent to exactly one antipodal pair, and \(n-7\) leaves at that vertex). The same theorem gives \(S\le 3n\) for every connected strong \(C_4\)-free \(P_6\)-free graph of order \(n\ge 2\), with equality only for the Petersen graph.

**Theorem 4.2 and Corollaries 4.4–4.5.** A connected strong \(C_4\)-free graph with radius 4 and induced-path order 7 is \(C_8\), or it is built from a 6-cycle by the extension in Theorem 4.2 and by no further vertices or edges. If \(b\) is the number of vertices added on edges of that 6-cycle and \(m\) is the number of matching edges in the sets \(C_i\), then \(S=2n-b-m\). In particular \(S\le 2n\) and \(\ell\le 2\). Equality \(S=2n\) holds exactly for \(C_8\) and for the 6-cycle with at least one leaf at each cycle vertex.

**Theorem 5.6.** Over connected triangle-free strong \(C_4\)-free \(P_7\)-free graphs of order \(n\ge 10\),
\[
f(n)=3n-\min\bigl\{n-10,\ 5+\mathbf{1}_{\{n\text{ even}\}}\bigr\}
\]
is the maximum of \(2e\). For \(10\le n\le 14\) the extremal graphs are the isomorphism classes obtained from the Petersen graph by placing \(n-10\) leaves on a single vertex or on the two endpoints of a single edge. For \(n=15\) those classes are joined by \(F_2\) (four classes in all). For \(n=16\) they are joined by \(F'_0\) and by the two graphs obtained from the order-15 graph \(F_2\) by adding a leaf at a hub or at the midpoint of its unique 2-edge branch (seven classes in all). For odd \(n\ge 17\) the unique extremal graph is \(F_2\). For even \(n\ge 18\) there are exactly three: \(F'_0\) and the same two one-leaf extensions of the order-\((n-1)\) graph \(F_2\).

**Theorems 5.7 and 5.10, and Lemma 5.9.** Theorem 5.5 is the triangle-free case of \(S\le 3n\), since then \(S=2e\), with equality only for the Petersen graph. Theorem 5.7 is the same inequality when the graph has at most one triangle; that argument is a hand proof. Lemma 5.9 is the case of at least two triangles: a finite search on four seeds visits 118 nodes, every branch ends at a leaf, and no node is unrestricted. Theorem 5.10 extends \(S\le 3n\), equality only for the Petersen graph, to every connected strong \(C_4\)-free \(P_7\)-free graph. The search in Lemma 5.9 is the certificate checked by `certificates/gen3/verify_gen3.py`. An independent C implementation of that search is `referee_checks/lemma57b.c`.

**Theorem 5.11.** Every connected graph on at least two vertices with \(\ell\le 4\) satisfies REAL-133. The proof covers every radius, including \(r\ge 5\), where the Erdős–Saks–Sós bound \(p\ge 2r-1\) is already at least \(r+4\). Remark 5.12 records the floor form for every connected graph with \(\ell<5\). The real-valued statement for \(\ell>4\) stays open.

Section 6 records the next reduction and four constructions on that boundary. A counterexample of REAL-133 has \(\ell>4\) and, by Corollary 6.1, violates \(\mathrm{GEN}_K\) for some \(K\ge 4\) or \(\mathrm{RAD}(r)\) for some \(r\ge 5\).

Continuous proving has stopped. Earlier round write-ups live in [`notes/`](notes/).

## Formalization status

The mathematical status in the table above is unchanged. Separately, [`lean/`](lean/) formalizes the main theorems and selected supporting statements; the precise coverage is listed in [`lean/README.md`](lean/README.md). Phases 1–7 leave that numbered inventory at **0** `sorry` and **0** `admit`. Five literature axioms remain, listed in [`lean/AXIOMS.md`](lean/AXIOMS.md). Phases 2–7 added no handwritten axioms. Finite certificates, including the Appendix A replay, use `native_decide` and therefore trust the Lean compiler and runtime. This is **not** a verification of the paper from an empty axiom set, and it is not a claim that the proofs are kernel-checked with no axioms. `cd lean && lake build` typechecks the package on Lean 4.35.0 with Mathlib v4.35.0. The inventory is in [`lean/README.md`](lean/README.md).

## Layout

```
paper/main.pdf            website preprint (JGT/Wiley layout); page count below
paper/main.tex            article source
paper/response-english-major.md
                          draft answers to the 2026 English report, Q1–Q3
certificates/             archival round JSON (R1–R40 and R46–R53) with SHA-256 sidecars
certificates/gen3/        pinned checker verify_gen3.py (authors' certificate)
referee_checks/           separate C/Python implementation for computational cross-checking (written by Claude; see Independent checks)
lean/                     numbered lemmas and theorems; sorry/admit inventory 0; five axioms (lean/README.md)
notes/                    historical round notes
data/                     pointer only; the full computational supplement is not shipped
```

## Paper

- Article: [`paper/main.pdf`](paper/main.pdf), source [`paper/main.tex`](paper/main.tex)

```bash
cd paper
SP=(-Z search-path=templates/wiley-njd -Z search-path=templates/wiley-njd/images)
tectonic -X compile --keep-intermediates "${SP[@]}" main.tex
```

The PDF digest of this preprint is:

```text
a1df6e1495d80f3ccd5c544dfacfe1a78fe5d5ced037e2c1fdbe39b3aaba7e9d  paper/main.pdf
```

## How to verify the GEN3 certificate

Lemma 5.9 and Theorem 5.10 use `certificates/gen3/verify_gen3.py`. The file in this tree has SHA-256 `f1b6718941f9cf3e6b0917cf25ab9093810b07f6d35a11fb7cc539fb546e6fd0`. It is a Python 3.10+ program, uses only the standard library, embeds the decision certificate, and takes no arguments. It checks the four two-triangle rows and rejects an unrestricted node on those rows. The retired one-triangle search is not in this file; `referee_checks/lemma57` still reproduces that older count. From the repository root:

```bash
sha256sum -c <<'EOF'
a1df6e1495d80f3ccd5c544dfacfe1a78fe5d5ced037e2c1fdbe39b3aaba7e9d  paper/main.pdf
f1b6718941f9cf3e6b0917cf25ab9093810b07f6d35a11fb7cc539fb546e6fd0  certificates/gen3/verify_gen3.py
EOF
python3 certificates/gen3/verify_gen3.py
```

A successful run prints the four distance rows and ends with `PASS. All branches and all decision entries verified.` That sentence means the embedded decision arrays were replayed. It is not a second implementation. Lemma 5.9 uses those four rows, which together visit 118 nodes and 37 leaves, with unrestricted count 0 on each row. Appendix A prints the 118 decisions and records this replay. The separate cross-check is `referee_checks/lemma57b.c`.

## Independent checks

A separate implementation is provided in [`referee_checks/`](referee_checks/) and was used for computational cross-checking. Claude (Anthropic), an AI system, wrote it during pre-submission reviews that the authors requested. It worked from the manuscript's description of the search and did not use the authors' code.

Build and run instructions, the translation from pre-R15 numbering to the current article, and the claim-to-script map are in [`referee_checks/README.md`](referee_checks/README.md).

The authors' checker for Lemma 5.9 is `certificates/gen3/verify_gen3.py`. An independent C implementation (`lemma57b.c`) written for cross-verification is in `referee_checks/`, run with `DEFONLY=1` on the four seeds named in that README. Re-running the authors' checker is a replay of one certificate. The second implementation reproduces the search counts and confirms closure of all four trees, using its own vertex labelling and traversal order.

Round JSON under `certificates/` is an archive of earlier internal and AI review rounds, through R53, not a journal referee report. Each `ROUND_BRANCH_R*_CERTIFICATE.sha256` sidecar checks the matching JSON file:

```bash
cd certificates
sha256sum -c ROUND_BRANCH_R53_CERTIFICATE.sha256
```

The R53 digest is `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`. Those files, and the summaries in `notes/`, are the record of the stopped rounds. The theorems of this preprint are the rows in the table above. [`PUBLISH_MANIFEST.md`](PUBLISH_MANIFEST.md) is the 2026-11-01 packaging record of that archive.

## Left out of this snapshot

- Astra session logs, context dumps, and lane scratch trees
- The full `data/` computational supplement (see `data/README.md`)
- Round files R41–R45, and any round after R53

## License

The code and other materials in this repository are released under the MIT License. See [`LICENSE`](LICENSE).

## Citation

Xingchen Wang and Xincao Xu, *Induced Paths, Radius, and Extremal Neighbourhood Independence in Graphs without 4-Cycles*, website preprint. Corresponding author: Xincao Xu, xc.xu@uestc.edu.cn. Questions about the certificate or about reproduction can be opened as a GitHub issue.
