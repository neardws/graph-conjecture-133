# Induced Paths, Radius, and Extremal Neighbourhood Independence in Graphs without 4-Cycles

Xingchen Wang (Independent Researcher, skywalkerwang98@gmail.com) and Xincao Xu (corresponding author; Shenzhen Institute for Advanced Study, University of Electronic Science and Technology of China, xc.xu@uestc.edu.cn). Credit for technical checking and for drafting assistance is in the Acknowledgments of the preprint.

This repository is the website preprint of that paper, set in the Journal of Graph Theory layout (Wiley USG class). The deliverable is [`paper/main.pdf`](paper/main.pdf) (22 pages). There is no separate supplement: the one-triangle bound is proved by hand in the article, and the two-triangle search is Appendix A.

For a graph \(G\) on \(n\ge 2\) vertices, \(p(G)\) is the largest order of an induced path, \(r(G)\) is the radius, and
\[
\ell(G)=\frac1n\sum_{v\in V(G)}\alpha\bigl(G[N(v)]\bigr),
\]
where \(S(G)\) is the sum in the numerator. Write \(P_k\) for the path on \(k\) vertices. A graph is *strong \(C_4\)-free* when it contains no 4-cycle as a subgraph. Conjecture 133 of *Written on the Wall II* (Graffiti.pc), in the real-valued form called REAL-133, says that every connected graph on at least two vertices satisfies \(p(G)\ge r(G)+\ell(G)^{c_{C_4}(G)}\). The formal statement is the Formal Conjectures file at commit `5faef0c4dc3d226f8f9a9fc8f581b6221283eb6e`, the merge of pull request [#5727](https://github.com/google-deepmind/formal-conjectures/pull/5727), which removed the floor function.

Every connected strong \(C_4\)-free graph with no induced path on seven vertices satisfies \(S\le 3n\), with equality only for the Petersen graph. Every connected graph with \(\ell\le 4\) therefore satisfies REAL-133, at every radius; when the graph contains a triangle the argument uses the finite certificate below. The same arguments determine the maximum of \(\ell\) over connected strong \(C_4\)-free graphs with no induced path on six vertices, with a unique extremal graph for every order \(n\ge 7\); classify the connected strong \(C_4\)-free graphs of radius 4 and induced-path order 7; and determine, for every \(n\ge 10\), the maximum number of edges in a connected triangle-free strong \(C_4\)-free graph with no induced path on seven vertices, together with all extremal graphs. REAL-133 remains open for \(\ell>4\). No structural classification for radius \(r\ge 5\) is proved.

## Results

The boundary in the preprint is the Discussion (Section 7 of `paper/main.pdf`).

| Statement | Reference | Status |
|-----------|-----------|--------|
| Exact \(M(n)\) and a unique extremal graph for every connected strong \(C_4\)-free \(P_6\)-free graph of order \(n\ge 7\) | Theorem 3.6 | Proved |
| Structure of connected strong \(C_4\)-free graphs with radius 4 and induced-path order 7; the formula \(S=2n-b-m\); the equality cases | Theorem 4.2, Corollaries 4.4 and 4.5 | Proved |
| \(2e\le 3n\) for connected triangle-free strong \(C_4\)-free \(P_7\)-free graphs, with equality only for the Petersen graph | Theorem 5.5 | Proved |
| Exact maximum of \(2e\), and all extremal graphs, in that triangle-free class, for every \(n\ge 10\) | Theorem 5.6 | Proved |
| \(S\le 3n\) for every connected strong \(C_4\)-free \(P_7\)-free graph, with equality only for the Petersen graph. At most one triangle is the hand proof in Theorem 5.7; at least two triangles uses the closed search in Lemma 5.9 | Theorems 5.7 and 5.10, Lemma 5.9 | Proved |
| Induced-path order 6 forces \(S\le 3n-1\) and \(\ell<3\). On each of \((r,p)=(2,6)\) and \((3,6)\) the supremum of \(\ell\) is 3 and is unattained | Corollary 6.3 | Proved |
| REAL-133 for every connected graph with \(\ell\le 4\), at every radius. The floor form holds for every connected graph with \(\ell<5\) | Theorem 5.11, Remark 5.12 | Proved |
| Real-valued REAL-133 for \(\ell>4\), and REAL-133 with no restriction on \(\ell\). No structural classification for radius \(r\ge 5\) | Section 7 | Open |

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

**Theorems 5.7 and 5.10, and Lemma 5.9.** Theorem 5.5 is the triangle-free case of \(S\le 3n\), since then \(S=2e\), with equality only for the Petersen graph. Theorem 5.7 is the same inequality when the graph has at most one triangle; that argument is a hand proof. Lemma 5.9 is the case of at least two triangles: a finite search on four seeds visits 118 nodes, every branch closes, and no node is unrestricted. Theorem 5.10 extends \(S\le 3n\), equality only for the Petersen graph, to every connected strong \(C_4\)-free \(P_7\)-free graph. The search in Lemma 5.9 is the certificate checked by `certificates/gen3/verify_gen3.py`.

**Theorem 5.11.** Every connected graph on at least two vertices with \(\ell\le 4\) satisfies REAL-133. The proof covers every radius, including \(r\ge 5\), where the Erdős–Saks–Sós bound \(p\ge 2r-1\) is already at least \(r+4\). Remark 5.12 records the floor form for every connected graph with \(\ell<5\). The real-valued statement for \(\ell>4\) stays open.

Section 6 records the next reduction. A counterexample of REAL-133 has \(\ell>4\) and, by Corollary 6.1, violates \(\mathrm{GEN}_K\) for some \(K\ge 4\) or \(\mathrm{RAD}(r)\) for some \(r\ge 5\). Section 7 gives four constructions on that boundary.

Continuous proving has stopped. Earlier round write-ups live in [`notes/`](notes/).

## Formalization status

The mathematical status in the table above is unchanged. Separately, `lean/` is a Phase 1 Lean 4 scaffold for those statements. It is **not** a Lean verification of the paper: most proofs are `sorry`, and five cited theorems are axioms listed in [`lean/AXIOMS.md`](lean/AXIOMS.md).

What Phase 1 contains is the definitions (`S`, `ℓ`, `c_{C₄}`, induced-path order, radius, triangles, deletion loss), a Lean statement for each named result through Section 6 and Appendix A, proofs of the strong `C₄`-free counting identities in Lemma 2.1 (except the component-count sentence), and a total checker interface for the four-seed search. `lake build` in `lean/` typechecks the scaffold. The toolchain is Lean 4.35.0 with Mathlib v4.35.0. Details, the `sorry` list, and the build command are in [`lean/README.md`](lean/README.md).

## Layout

```
paper/main.pdf            website preprint, 22 pages (JGT/Wiley layout)
paper/main.tex            article source
certificates/             archival round JSON (R1–R40 and R46–R53) with SHA-256 sidecars
certificates/gen3/        pinned checker verify_gen3.py
lean/                     Phase 1 Lean scaffold (not a verification; see lean/README.md)
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
56d8eccd034b19ef248fa38a6bcde9ede502fd50a7a271e04c0b1e2df8f1a23f  paper/main.pdf
```

## How to verify the GEN3 certificate

Lemma 5.9 and Theorem 5.10 use `certificates/gen3/verify_gen3.py` at commit `dd555d305b4a69076cafb845087f00b4144f07cc`. That blob has SHA-256 `6be3852172aa401387b498c7e5a8a0efbbdde72aabb1e7fad0db9085b89eb86c`. The file in this tree has the same digest. It is a Python 3.10+ program, uses only the standard library, embeds the decision certificate, and takes no arguments. From the repository root:

```bash
sha256sum -c <<'EOF'
56d8eccd034b19ef248fa38a6bcde9ede502fd50a7a271e04c0b1e2df8f1a23f  paper/main.pdf
6be3852172aa401387b498c7e5a8a0efbbdde72aabb1e7fad0db9085b89eb86c  certificates/gen3/verify_gen3.py
EOF
python3 certificates/gen3/verify_gen3.py
```

A successful run ends with `PASS. All branches and all decision entries verified.` Lemma 5.9 uses the four distance rows, which together visit 118 nodes and 37 leaves, with unrestricted count 0 on each row. The opening line of the same run is an older one-triangle search (`nodes=169`, maximum order 17, `leaves=52`, `unrestricted=4`). Theorem 5.7 replaces that search, and the article does not cite it. Appendix A of the article records an independent execution of the same command. The checker file itself is unchanged.

Round JSON under `certificates/` is an archive of earlier referee rounds, through R53. Each `ROUND_BRANCH_R*_CERTIFICATE.sha256` sidecar checks the matching JSON file:

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

No license file is published in this snapshot. All rights reserved by the authors unless a license is added later.

## Citation

Xingchen Wang and Xincao Xu, *Induced Paths, Radius, and Extremal Neighbourhood Independence in Graphs without 4-Cycles*, website preprint. Corresponding author: Xincao Xu, xc.xu@uestc.edu.cn. Questions about the certificate or about reproduction can be opened as a GitHub issue.
