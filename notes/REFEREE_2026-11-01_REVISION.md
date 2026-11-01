# Revision against the external report of 1 November 2026

This note is not part of the article. The article is `paper/main.tex`. The previous manuscript text is kept at `notes/manuscript_before_referee_2026-11-01.tex` so that round language and undefined predicates removed from the article remain in the repository. Certificate files under `certificates/` are unchanged. A hash of a certificate authenticates stored JSON. It is not a checker, an input list, or a completeness argument, and the article does not treat it as a proof.

REAL-133 and unrestricted GEN6 stay open. No proving pipeline was resumed.

## Must-fix items

1. **Radius four.** Lemma on a dominating induced 8-cycle in a connected strong \(C_4\)-free \(P_8\)-free graph of radius at least 4 is now a hand proof that the graph is \(C_8\). The mass count \(n=6+a+b\), \(e=6+a+2b+m\), \(T=b+m\), \(S=2n-b-m\) is the written trace argument, and it is a theorem: \(r=4\), \(p=7\) implies \(\ell\le 2\). If \(r=4\) and \(p\ge 8\), then \(p\ge r+\ell\) whenever \(\ell\le 4\). Theorem A includes these radius cases. An independent labelled count (32 traces, 790 configurations, orders \(1,32,262,384,107,4\), 73 unrooted classes, only the bare cycle of radius at least 4) is a remark and is not a hypothesis.
2. **Rooted display.** \(\mathrm{ROOT}(q)\) is stated with the hypothesis \(p_s(F)\le q\). Without that hypothesis the inequality is false for \(q=3\) and \(F=C_5\) (\(S=10\), \(m=0\), right-hand side \(8\)).
3. **Oriented and rooted endpoint inequalities.** For \(q\ge 4\), \(\mathrm{EP}(q)\) and \(\mathrm{EP}^+(q-1)\) are equivalent by the deletion-loss comparison \(D_G(E)\le D_H(E)+2|E|\) in one direction and \(D_G(E)=D_H(E)+2|E|\) for the vertex-attachment construction in the other. The explicit failure of \(\mathrm{EP}(9)\) and \(\mathrm{EP}^+(8)\) is unchanged and was rechecked from the adjacency lists (\(D=20\) and \(D=16\)).
4. **Cactus path claim.** The old Appendix E sentence that a vertex off a cycle of length at least 9 in a cactus lies on an induced path of order 10 is deleted. It is false for ordinary cacti: attach one leaf to \(C_9\). The ten vertices contain a cycle, so they do not induce \(P_{10}\). The path order is 9, given by the leaf followed by eight consecutive cycle vertices. The extra hypotheses that sentence may have needed are not in the archive, so the sentence was not repaired by adding hypotheses.
5. **Cells and the core count.** The old appendix heading “Verified partial closures”, and the assertion that both cells \((r,p)=(4,9)\) and \((5,10)\) are closed, are not in the article. Those cells are open, including for bipartite graphs. Arguments that used the unproved bipartite form of \(\mathrm{GEN}_5\), an absent census of 2-connected \(P_6\)-free blocks, or an absent trace list are not proofs. The Petersen graph (\(\ell=3\)) refutes the unrestricted dominating-core budget. The article does not report a count of eligible cores and does not use any such count to justify the cutoff \(\ell>5\).

## Optional item

The gap below the Petersen graph is Proposition (near the \(P_6\)-free mass bound): a connected strong \(C_4\)-free \(P_6\)-free graph of order at least 2 with \(\ell>5/2\) is the Petersen graph or the graph obtained by deleting one vertex, with values 3 and \(8/3\). Every other graph in the class has \(\ell\le 8/3\), with equality only for the one-vertex deletion. The three cases are an induced 6-cycle, an induced 5-cycle and no 6-cycle, and the chordal case. Karthick–Maffray is cited only as a comparison of scope. No priority claim is made. Erdős–Saks–Sós and Camby–Schaudt are the same external theorems as in the previous manuscript.

## What left the article

Verdict history, model names, round identifiers, and undefined predicates (endpoint-reducing deletions of unnamed weight, one-vertex Robertson punctures, and the graphs named only inside those records) are not in the article. The conditional deletion lemmas whose hypotheses are written in full remain, and they do not prove that the class \(\mathcal F_0\) is free of positive graphs.

Computer-dependent inequalities stay unproved. There is still no versioned public archive here of a checker, its inputs, and a completeness argument for \(\mathrm{GEN}_3\), \(\mathrm{GEN}_4\), \(\mathrm{ROOT}(q)\) with \(q\ge 4\) outside the block class, \(\mathrm{RAD}(r)\) for \(r\ge 5\), bipartite \(\mathrm{GEN}_5\), or a structure theorem at radius at least 5.
