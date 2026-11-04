# Response to the English major-revision report

Draft answers to three English major-revision questions about Section 6. Numbering is that of the article after R15. This note does not add theorems.

## Q1. A computer-free proof of the triangle case?

The case of at most one triangle is a hand proof: Theorem 5.7. The retired one-triangle search (pre-R15 Lemma 5.7, 169 nodes, 52 leaves, 4 unrestricted nodes) is not used. Theorem 5.7 replaces it.

What blocks the same deletion argument for two or more triangles is that deleting one vertex can leave a triangle. The Chen–Xu classification and the strip decomposition apply to triangle-free graphs, so they do not apply to \(G-v\) in that case. Lemma 5.9 produces a vertex of deletion loss at most 3 by a finite search on four seeds (118 nodes). Once such a vertex exists, the minimal-counterexample argument in the proof of Theorem 5.10 is by hand. No computer-free proof of Lemma 5.9 is claimed.

## Q2. Can Theorem 3.6 be derived from Karthick–Maffray?

It is not derived here. Karthick and Maffray describe square-free \((P_6,C_4)\)-free graphs in the induced sense, by clique cutsets and atoms. The exact value of \(M(n)\) and the uniqueness statement use the prohibition of a \(C_4\) subgraph: the antipodal traces and the second-layer count. Blow-ups and joins allowed by the induced-\(C_4\) theory contain \(C_4\) subgraphs and lie outside the strong-\(C_4\)-free class. Lemma 2.9 is only the emptiness list on an induced 5-cycle. It is proved directly from the absence of an induced \(P_6\), an induced \(C_4\) and an induced \(C_6\). That list is not Theorem 3.6. Case 2 of Theorem 3.6 uses the first two assertions of the list; the third is part of the Karthick–Maffray list and is not required there.

## Q3. Should \(S\le f(n)\) hold for the whole class?

The expected statement is recorded as an open conjecture in the Discussion. For every \(n\ge 10\), the maximum of \(S\) over connected strong-\(C_4\)-free \(P_7\)-free graphs of order \(n\) equals \(f(n)\) from Theorem 5.6, and every graph that attains it is one of the extremal graphs of that theorem, hence triangle-free. The article does not claim a proof of the conjecture.

## Notes on two minor points

**The core \(K_1\).** It is the whole graph only when \(n=1\). It is also the core of every \(P_7\)-free tree, of any order: the strip deletion removes leaves until one vertex remains. The article states both facts. The sentence “\(K_1\) occurs only when \(n=1\)” is not the whole story.

**Equality on at most 13 vertices.** The article records equality for \(K_2\), \(K_3\), \(C_5\), the Petersen graph and \(C_6\). It does not claim these are the only equality cases on at most 13 vertices, and it does not characterise equality cases in general. The program `real133.c` reports minimum slack. It does not print a classified list of every equality graph.

## Left open on purpose

- The Discussion conjecture is not proved.
- Formalization, including any Lean development, is a separate project. It is not claimed as a verification of these proofs. Re-running `certificates/gen3/verify_gen3.py` replays the authors’ certificate. The second implementation is `referee_checks/lemma57b.c`.
