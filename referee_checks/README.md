# Independent checks for the WOWII-133 manuscript

Independent checks provided with a JGT referee report (2026); reproduced here for archival cross-verification.

These scripts are the anonymous referee's own re-implementation. They are not the authors' code, and this repository does not claim authorship of them. None of them calls the authors' programs. The C and Python sources are unchanged from the copy supplied with that report. This README adds attribution, the claim map, and the note on numbering after the authors' revision R15.

They need nauty (`geng` and `labelg`; on macOS, `brew install nauty`), a C compiler and Python 3.

A Zenodo DOI for this directory is **pending**. Do not invent one. Software Heritage and Zenodo deposits can be attached here when a persistent identifier is minted.

## Build

```bash
cd referee_checks && for f in gstat extend lemma57 lemma57b real133 rootq; do cc -O3 -o $f $f.c; done
```

## What each program does

The descriptions below are the referee's. Program comments use the numbering of the pre-R15 manuscript (20-page article plus 15-page supplement). The translation to the current article is the table in the next section.

| Program | Checks |
|---|---|
| `gstat [pmax]` | Reads graph6 on stdin. Prints `g6 n e T S p r diam hasC4 minL adjdeg2 minDeg`, skipping graphs whose longest induced path has more than `pmax` vertices. |
| `extend K [t]` | Prints every one-vertex extension that has no 4-cycle subgraph and no induced P_K; with `t`, also triangle-free. Iterate with `labelg -q \| sort -u` to enumerate a hereditary class level by level. |
| `lemma57 [g6] [outfile]` | Independent version of the pre-R15 Lemma 5.7 search, starting from a triangle by default. Prints node, leaf and unrestricted counts, and writes every unrestricted node to `outfile`. |
| `lemma57b` | The same search. With `DEFONLY=1` it uses only deficient-vertex decisions, as in the two-triangle searches. |
| `real133` | Checks the real-valued Conjecture 133 under both C4 readings (subgraph and induced). |
| `rootq` | Checks the pre-R15 supplement's rooted bounds: ROOT(q), the terminal bound, and the radius part of Conj. S4.4. |
| `check_*.py` | Comparisons with the named graphs (Theorems 3.6, 4.3, 5.6, 5.8 in the pre-R15 numbering, the examples, and the Chen–Xu family). |

## Numbering after R15

R15 folded the one-triangle hand proof into the article and removed the supplement. Theorem and lemma numbers below are those of `paper/main.tex` on the current article. The pre-R15 numbers in the referee's comments are in parentheses.

| Current article | Pre-R15 report | What it is |
|---|---|---|
| Theorem 3.6 | Theorem 3.6 | Exact \(M(n)\) for connected strong-\(C_4\)-free \(P_6\)-free graphs |
| Theorem 4.2, Corollaries 4.4 and 4.5 | Theorem 4.3 and the following corollaries | Radius 4 and induced-path order 7; \(S=2n-b-m\) |
| Lemma 2.10 | Lemma 2.10 | No clique cutset in the 2-connected triangle-free class |
| Theorem 5.5 | Theorem 5.5 | \(2e\le 3n\) in the connected triangle-free strong-\(C_4\)-free \(P_7\)-free class |
| Theorem 5.6 | Theorem 5.6 | Exact maximum \(f(n)\) of \(2e\), and the extremal graphs, for \(n\ge 10\) |
| Theorem 5.7 | Supplement, hand bound for one triangle | \(S\le 3n\) with at most one triangle. Proved by hand. Not a search |
| Lemma 5.8 | Part of the two-triangle setup | How two triangles meet in a strong-\(C_4\)-free graph |
| Lemma 5.9 | Supplement Lemma S5.3; the report discusses it next to old Lemma 5.7 | The 118-node two-triangle search |
| Theorem 5.10 | Theorem 5.8 | \(S\le 3n\) for every connected strong-\(C_4\)-free \(P_7\)-free graph |
| Theorem 5.11, Remark 5.12 | Theorem 5.9, Remark 5.10 | REAL-133 for \(\ell\le 4\); floor form for \(\ell<5\) |
| (not a hypothesis) | Lemma 5.7 | One-triangle search: 169 nodes, 52 leaves, 4 unrestricted nodes, all isomorphic to \(H_{3,2}\). Theorem 5.7 replaces it. `certificates/gen3/verify_gen3.py` no longer contains this row; `lemma57` still reproduces the count |
| (removed) | Supplement examples, ROOT(\(q\)), Lemmas S5.6 and S5.7 | Not claims of the current article |

## Claim map

Author scripts live in this repository and were not written by the referee. Referee scripts are the files in this directory.

| Claim in the current article | Author script | Referee script |
|---|---|---|
| Theorem 3.6 | No separate checker is cited. The proof is by hand | `check_p7.py` on `geng` output passed through `gstat` (rows with induced-path order at most 5). `check_named.py` compares canonical forms of the named extremal graphs |
| Lemmas 3.3 and 3.5 | Hand proofs | `check_p7.py` (the \(P_5\)-free count at the end of that file) |
| Theorem 4.2, Corollaries 4.4 and 4.5 | Hand proofs. `paper/scripts/c8_configurations.py` enumerates a dominating-\(C_8\) count from an earlier draft; the current article does not use that count | `check_rad4.py` (the file's header still says Theorem 4.3) |
| Lemma 2.10, the family \(\mathfrak F\), Theorems 5.5 and 5.6 | Hand proofs from the Chen–Xu list | `extend` with the triangle-free flag, then `check_tf.py`. `check_examples.py` checks canonical forms of the extremal graphs of Theorem 5.6 |
| Theorem 5.7 | Hand proof in the article. No script | The one-triangle search is not this theorem. `lemma57` is the retired search. `certificates/gen3/verify_gen3.py` no longer contains that row |
| Lemmas 5.8 and 5.9, Theorem 5.10 | `certificates/gen3/verify_gen3.py` embeds the four decision arrays of Lemma 5.9 (36, 31, 46 and 5 entries) and rejects an unrestricted node on those rows | `lemma57b` with `DEFONLY=1` on the four seeds below. Fail-first selection reproduces the authors' four arrays. `check_p7.py` checks \(S\le 3n\) on enumerated graphs, which is Theorem 5.10 (header text: Theorem 5.8) |
| Theorem 5.11 | Hand proof | `real133` |
| Corollary 6.3 | Hand proof | `check_p7.py` (the block labelled Corollary 6.3) |
| Retired one-triangle search and \(H_{3,2}\) | Not in `certificates/gen3/verify_gen3.py`. Theorem 5.7 is the hand proof | `lemma57`, then `labelg` on the unrestricted output. `check_named.py` recognises \(H_{3,2}\) |
| Pre-R15 supplement only | `paper/scripts/check_ep9.py` checks an adjacency list that is not in the current article | `rootq`, `check_examples.py` (example block), and the supplement blocks in `check_p7.py` |

`certificates/gen3/verify_gen3.py` is the authors' certificate checker. Re-running it replays that certificate. It is not an independent verification. The independent re-implementation is `lemma57` / `lemma57b`.

## Main runs

```bash
# Retired one-triangle search (pre-R15 Lemma 5.7): expect nodes=169 leaves=52 unrestricted=4 maxorder=17
./lemma57 - unrestricted.g6 && labelg -q < unrestricted.g6 | sort | uniq -c
```

```bash
# Lemma 5.9 of the current article (pre-R15 Lemma S5.3).
# Seeds: shared vertex D{c, distance 1 E{CW, distance 2 FwC[_, distance 3 GwC[?c
# Expect 36/31/46/5 nodes, maximum orders 17/15/11/10, and 7/6/21/3 leaves, with no unrestricted node.
for g in 'D{c' 'E{CW' 'FwC[_' 'GwC[?c'; do DEFONLY=1 ./lemma57b "$g" /dev/null; done
```

```bash
# All connected C4-subgraph-free P7-free graphs, level by level (n=20 takes about 20 minutes)
mkdir -p lev && echo "@" > lev/c4p7_1.txt && for n in $(seq 1 19); do ./extend 7 < lev/c4p7_$n.txt | labelg -q 2>/dev/null | sort -u > lev/c4p7_$((n+1)).txt; done
```

```bash
# The same for the triangle-free class (Theorem 5.6), up to n=30
echo "@" > lev/g5p7_1.txt && for n in $(seq 1 29); do ./extend 7 t < lev/g5p7_$n.txt | labelg -q 2>/dev/null | sort -u > lev/g5p7_$((n+1)).txt; done
```

```bash
# Conjecture 133 on all C4-free graphs of order 13
geng -cf 13 | ./real133
```

The Python checkers expect `geng`-based files in `res/` (`res/p7free_N.txt` comes from `geng -cf N | ./gstat 6`, and `res/p8free_N.txt` from `geng -cf N | ./gstat 7 | awk '$6==7 && $7==4'`) and the generated levels in `lev/`. Run them with the folder name as an argument, e.g. `python3 check_tf.py lev 25`.

Generated binaries, `lev/` and `res/` are local run output. They are not part of the archival tree.
