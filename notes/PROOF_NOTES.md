# PROOF_NOTES (excerpt for public archive)

Computer-assisted proof notes. Full file is large; this public copy is an excerpt focused on the continuous window R35–R40 (ending 2026-10-24 18:00 Asia/Shanghai). Only CORRECT / CORRECT_WITH_FIXES claims are treated as proved in the paper.


---

## Recent entries (tail excerpt)

- The r26_search GAP comes only from C27. The local-search attempt totals (60,624 / 2,624 out of 240,000) cannot be replayed, because no trace or deterministic RNG specification was saved. These totals are execution metadata, not a premise of any theorem.
- The referee found no mathematical or certificate mismatch.
- Claims are accepted per claim (C or CWF).

**Fixes adopted**
- **rootlemma C25:** six nonpositive controls had singleton_critical=false although they satisfy min L ≥ K+ε; the flag also required positivity. Rename the field or correct it. No positive-domain result changes.
- **search C03:** the spare-arm converse (report line 42) must also require y ∈ B_v, i.e. yv ∉ E. Counterexample to the incomplete wording: edges 01,02,12,23,34,45,56. The checker specification was already correct.
- **search C28:** the M15 kill-tests refute only uncapped all-K universal-root variants. M15 has K=3 and p=9, so it does not refute capped K ≥ 6 statements.
- **search C27:** treat the local-search totals as unreplayed metadata. The 95 saved states and 27 saved outputs were validated.

**VERIFIED — r26_rootlemma**
1. **Exact root-star contraction.** Contract N[v] into one bag and repair the new 4-cycles by deleting a set X ⊆ B_v.
   - Surplus gain before repair: σ_v = (K−2)d_v + t_v − 3π_v, where π_v is the number of pentagons through v.
   - The report gives the exact loss hierarchy, the safety conditions (3)–(5), the strict budget condition, and the necessary inequalities under irreducibility, e.g. ε(|X|−1) + 3π_v(G−X) ≤ (K−2)d_v + t_v − 1.
   - Pentagons through a root correspond exactly to cross-class edges.
2. **Moore block theorem, K ≥ 3.** Let M be K-regular with girth ≥ 5 and order K²+1. Every nonempty proper admissible model J of M, with any bags, has S(J) − K|J| ≤ −K.
3. **Irreducible amalgam theorem.** Two such Moore blocks identified at one vertex give a graph that is irreducible, has ε = K, and has n = 2K²+1, for every K ≥ 3.
   - The two-Petersen amalgam is therefore irreducible: it has a cut vertex and bad minimum-degree roots, so irreducibility does not imply 2-connectivity.
   - Within block trees of Moore blocks and edges, the positive irreducibles are exactly these two-block amalgams.
4. **Conditional rooted theorem on this family.** If each anchor starts an induced P_{2K−1} in its block (for example, vertex-transitive blocks plus GEN_{K−1}), then every F-maximiser starts P_{2K+1}. This is a genuine use of GEN_{K−1}.
5. **Why the K=2 mechanism fails at K=3.**
   - At K=2, a bad root forces Z = ∅ and B a union of K2/K3 components with distinct labels, hence f_v = 0.
   - At K=3: H21's bad root has f=12; M15's bad root has f=6 and M15 is irreducible.
6. **H21 and M15 under the new selector R⋆ = argmax_lex (f_v, σ_v).**
   - H21: R⋆ = {20} (the centre: σ=2 versus −15 elsewhere). Its star contraction is safe and gives surplus 3, so the model alternative holds there.
   - M15: R⋆ = {1,…,6}, all of which start P7, so the bad root 7 (π=3, σ=−7) is excluded.
   - M15 has 4,096 root-star repairs at root 7; 2,041 are safe, with maximum 3-surplus −3. So "every F-maximiser has a rooted P7 or a positive repaired star model" is false (uncapped).
7. **Conditional implication.** STAR-LEX_cap(K) + GEN_{K−1} ⇒ ROOT-U on irreducibles. If STAR-LEX_cap holds for all K ≥ 6, then GEN_K holds for all K, by induction from GEN_5.
   - STAR-LEX_cap(K): in a positive, fully induced-critical, strongly C4-free graph with p ≤ 2K (assuming GEN_{K−1}), some v ∈ R⋆ has either a clean P_{2K−1} in B_v or a safe repair set X meeting the strict budget.
8. **Certificates.** 191,181 selected-root path witnesses over 127,307 catalogue records; complete rooted trees for 4 obstructions; all 7,553 M15 models rechecked. Catalogue completeness is COMPUTED.

**VERIFIED — r26_search**
1. **Sharp mass thresholds** (no other hypotheses): |G| ≤ 12 ⇒ S ≤ 3|G|, and |G| ≤ 19 ⇒ S ≤ 4|G|.
   - Contracted Heawood (n=13) and Robertson+1 (n=20) attain the first positive orders.
   - Every positive graph at those first orders is automatically fully critical and irreducible.
2. **Component selector C** (maximise c_v, the largest component surplus of B_v). AR(K) ⇒ max_v c_v > 0. C and CF avoid the centre of the regular-block kill-test.
3. **Catalogues at K=3** (critical-graph completeness is COMPUTED; irreducibility classifications are certified):

   | Slice | Critical graphs | Irreducible |
   |---|---|---|
   | n=17, δ ≥ 3, triangles allowed | 30,172 | 702 |
   | n=18, triangle-free | 20,903 | 68 |
   | n=17, triangle-free | 4,658,166 | only the failed-root subdomain classified |
   | n=18, triangular | interrupted search | none claimed |

4. **Four new irreducible spare-arm obstructions** at K=3 (triangle-free, fully critical, n=17, e=26, ε=1): A17, B17, S17, D17.
   - Certificates: 68 edge-charge assignments for criticality and 372,491 model rejections for irreducibility.
   - S17 (`P???C@?K@O@aDAo_?[Aq?hG?`): every selector (F, D, C, L, ROOT-U, FC, CF) is {6}, with d=2, f=c=12. Vertex 6 has no spare-arm P7 (root in position 3), yet it starts the endpoint P7 6,13,0,7,15,3,9.
   - These refute only the uncapped spare-arm-at-selector variants. They are order-minimal relative to the catalogues through n=16.
5. **Robertson+1** (minimum positive K=4 order, 20) defeats the minimum-degree / minimum-L spare-arm rule.
6. **Endpoint selectors survive everywhere.** On all tested data no existential endpoint selector fails: ROOT-U, F, C, FC and CF all survive. In total, 163,564,801 positive path witnesses were checked, and all 745 negative entries on 675 graphs were matched to complete negative forests.
7. **Conditional implications** (K ≥ 6, assuming GEN_{K−1}):
   - "some CF root has a clean P_{2K−1}" ⇒ GEN_K;
   - mixed rule: "some minimum-degree root has an endpoint P_{2K+1} or a spare-arm P_{2K+1}" (with GEN_{K−2}) is also sufficient.

**Open after R26**
- The root-selection lemma in any of its sufficient forms: STAR-LEX_cap, CF endpoint, mixed minimum-degree endpoint-or-spare-arm, or "simultaneous endpoint failure at all CF roots forces a positive proper model".
- GEN_K for K ≥ 6; NB(6) (42 profiles); FP42; REAL-133.

## §4ab Round 27 — STAR-LEX_cap(K) attack + kill-tests (2026-10-22/23)
Neil said "继续" at 22:11. Briefing: data/r27/BRIEFING.md; the star safety and budget conditions are in ctx/STARLEX_CONDITIONS.md.
Two provers ran, r27_starlex and r27_killtest. Each was followed by its own fresh Astra referee, which received every file in the prover's manifest. No session was relaunched.

**Verdicts**

| Session | Overall | Claims | C | CWF | UNV | Incorrect |
|---|---|---|---|---|---|---|
| r27_starlex | CORRECT_WITH_FIXES | 38 | 33 | 3 | 2 | 0 |
| r27_killtest | CORRECT | 31 | 30 | 0 | 1 | 0 |

The UNVERIFIED claims are the labelled open conjectures, plus execution history in starlex.

**Fixes adopted (starlex)**
- **FIX-A.** Lemma A needs |V(H)| ≥ 2. With H = {o} the statement is false as literally written; every application already satisfies the condition.
- **FIX-DEF.** Full induced criticality must be defined for positive graphs; two isolated vertices (2K1) show why.
- **FIX-SUMMARY.** The cut-vertex claim holds only for K ≥ 3: at K=1, P3 is a positive singleton-critical graph with a cut vertex and p=3. Make the summary links relative.

**R26 C27 is resolved.** r27_killtest withdraws the unreplayable local-search totals (file r27_r26_c27_fix.md), and the referee accepted the withdrawal as claim C28 (CORRECT). No theorem or catalogue result depended on those totals.

**VERIFIED — r27_starlex**
1. **Lemma A (rooted terminal bound).**
   - Hypotheses: H connected and strongly C4-free; |V(H)| ≥ 2; λ_H(x) = d−t ≥ m ≥ 2 for every x ≠ o.
   - Conclusion: o starts an induced path on ≥ m+2 vertices.
   - No positivity, criticality, induction or cap is needed.
2. **Theorem B (cut vertex).**
   - Setting: o is a cut vertex with branches D_i, and m_i = min over D_i of λ_G ≥ 2.
   - Then p(G) ≥ m_i + m_j + 3 for any two branches i ≠ j.
   - **B1 (K ≥ 3; positive and singleton-critical).** p ≥ 2⌈(K+ε)/2⌉ + 3.
   - **B2 (uniform part of STAR-LEX_cap).** No positive singleton-critical graph has a cut vertex, p ≤ 2K and ε ≥ K−3.
     - The capped cut-vertex case is therefore excluded for K=3 and K=4, including graphs with triangles.
     - At general K ≥ 5, only 1 ≤ ε ≤ K−4 remains.
   - Two Moore blocks sharing a vertex have p ≥ 2K+3. This drops R26's anchored-path assumption and does not need GEN_{K−1}.
3. **Theorem C1 (exact irreducibility criterion at a cut vertex).** Irreducibility composes exactly across an articulation point via branch models; the report gives the two-part iff. Applied to Moore blocks, it re-derives the irreducible amalgam and classifies block trees of Moore blocks and edges.
4. **Theorem D (star capacity in C and Z).**
   - A repaired star is admissible exactly when G[C_0] has maximum degree ≤ 1 and the retained C vertices give a packing condition on Z_0.
   - Its surplus separates over the components of B_v (κ_v(D)).
   - A positive proper repaired star exists ⇔ the sum of the component optima exceeds the explicit threshold.
5. **Lemma E (K ≥ 2).** If every induced subgraph of G[Z] has nonpositive (K−2)-surplus, then every repaired star has surplus ≤ −K. Under GEN_{K−2}, a positive repaired star therefore needs an induced P_{2K−3} inside Z.
6. **Theorem E1 (remote-mass obstruction, full criticality).** A positive repaired star forces remote mass S(G[Z]) above an explicit bound, with a numerical order consequence. This gives a short counting proof of M15's bad-root repair obstruction.
7. **Certificates.** 369,152 repair sets, 93 path witnesses, 7 negative forests, 156 criticality certificates.

**VERIFIED — r27_killtest**
1. **K=4, n=20.** Every positive strongly C4-free graph on 20 vertices is fully critical and irreducible (by the n ≤ 19 mass threshold) and has 3 ≤ δ ≤ Δ ≤ 5, with an exact profile split. The complete catalogue gives Robertson+1 as the unique such graph; that completeness rests on the generator and is COMPUTED.
2. **Petersen block trees, K=3.**
   - The positive critical ones are classified.
   - H21 is the unique critical R⋆-endpoint obstruction in this class, and its star gives a positive proper model.
   - J19 (the two-Petersen amalgam) is irreducible. J20 is reducible through a safe bridge contraction.
3. **Regular-block stars, all K ≥ 3.** With m = ⌊K/2⌋+1 blocks the graph is positive and fully critical, and the safe positive star at the centre z exists. This is a uniform safe-star alternative.
4. **New K=3 irreducible catalogues.**
   - Every irreducibility claim comes with a complete model-rejection certificate: 194,450,834 rejections for the 202 graphs at n=18 with T=1, and 282,073,459 for the 45 at n=19 with T=0.
   - Catalogue completeness is COMPUTED (geng -cf with the stated degree restrictions).

   | n | T | Restriction | Critical graphs | Irreducible |
   |---|---|---|---|---|
   | 18 | 1 | 3 ≤ d ≤ 4, e=29, complete | 30,520 | 202 |
   | 18 | 2 | e=31, first 2,048 of 154,302 classified | — | 5 |
   | 19 | 0 | 3 ≤ d ≤ 4, e=29, complete | 18,837 | 45 |
   | 19 | 1 | interrupted prefix of 3,435 | — | none claimed |

5. **Kill-test results.**
   - Test set: 148,682 inherited K=3 graphs, the new catalogues, 850 structured or planted records, and the extra families (two-HS amalgam at K=7, n=99; four-HS star, n=201; Petersen block stars).
   - **No irreducible graph fails the existential endpoint rule for R⋆ or for CF.**
   - All 30 failed records (29 graphs) are explained:
     - 28 are fully critical but reducible copies of H21; they fail R⋆ and pass CF.
     - The two-Petersen amalgam plus a leaf is noncritical; it fails R⋆ and passes CF.
     - Three Petersens on one anchor plus an isolated vertex is noncritical and fails both rules.
   - Every failure has a negative tree and a positive proper model.

**Open after R27**
- STAR-LEX_cap(K) / CF-endpoint in general: the 2-connected case, and the cut-vertex case with 1 ≤ ε ≤ K−4 when K ≥ 5.
- GEN_K for K ≥ 6; NB(6); FP42; REAL-133.

**Recommended next target (R28).** Prove STAR-LEX_cap (or CF) for 2-connected irreducible graphs. Tools:
- Theorem D's component separation;
- Lemma E and E1 (a positive star needs P_{2K−3} and remote mass in Z);
- Lemma A applied around the root.

Also close the cut-vertex range 1 ≤ ε ≤ K−4 using C1 and Lemma A.

## §4ac — Round 28 (2026-10-23 Asia/Shanghai)

**Protocol.** Same as R26/R27: Astra proves; fresh Astra referee per prover (claim+report+manifest data only); accept CORRECT/CORRECT_WITH_FIXES only; certificate from referee `verdict.json` only. Cap=2 + capguard. Mid-run box fork/reboot killed both provers; resumed with original session ids (`codex exec resume`): twoconnected=`01a165e9-08ae-7363-84bd-a9d8104c50f7`, side=`01a165e9-35d1-72b0-a710-63cf979bedcf`. Gated chains died after prover EXIT before mkver; referees launched via `:REF` only (no prover relaunch).

**Sessions.**
| Session | Overall | Claims | C | CWF | UNV | Incorrect | Fixes |
|---|---|---|---|---|---|---|---|
| r28_twoconnected / v_r28_twoconnected | CORRECT | 39 | 35 | 0 | 4 | 0 | none |
| r28_side / v_r28_side | CORRECT | 32 | 28 | 0 | 4 | 0 | none |
| **Total** | | **71** | **63** | **0** | **8** | **0** | |

UNVERIFIED entries are the report's own CONJECTURED/open items (general 2-connected STAR-LEX_cap, general residual cut-vertex / RB_K / K=6 geometries, GEN_6+/REAL-133, historical/scheduling notes) — not failures.

### Verified mathematical progress

1. **Independent GEN_3 via finite loss certificates (r28_twoconnected).** Complete acyclic expansion certificates for q=4,5,6 prove: every nonempty strongly C₄-free G with p≤6 has nonempty U with |U|≤10 and D_G(U)≤3|U|; hence by induction S≤3|G|. No appeal to accepted GEN_3. Sharpness: T11 (`JhCMIOQcCO?`, p=6, ε₃=−4, cheap triple) and Petersen (p=5, forces |U|≤10). Triangle-free p=6 admits |U|≤2. **Consequence:** the capped K=3 2-connected irreducible domain for STAR-LEX_cap / CF-endpoint is empty, so those base assertions hold vacuously on that domain. The proof is a deletion-loss argument; it does **not** establish the proposed general root-star / A+D+E repair mechanism.

2. **Cut-vertex residual closed through K=8 (both sessions; twoconnected primary).** For positive fully induced-critical strongly C₄-free G, every branch at a cut vertex has order ≥K². Relative to accepted ROOT(3)..ROOT(8): no such G with p≤2K has a cut vertex for **3≤K≤8**. In particular residual strips 1≤ε≤K−4 at K=5,6,7,8 are excluded (no GEN_K used). At K=9, accepted finite ROOT(9) forces any capped cut-vertex example to have order ≥271.

3. **Side structural refinements (r28_side, VERIFIED).** T28.1 (K-free rooted lemma with b_H), residual block-geometry reductions T28.2–T28.6, short-root gluing T28.7, even-K tree augmentation T28.8. **ASSEMBLY (conditional):** RB_K + a capped 2-connected irreducible endpoint/model theorem ⇒ GEN_K. RB_K itself remains CONJECTURED (UNVERIFIED).

4. **Kill-tests COMPLETE (r28_side).** No irreducible R⋆/CF endpoint failure in any completed domain.
   - K=3, n=18, T=2, 3≤d≤4: 154302 classes, **65 irreducible**, 0 R⋆ / 0 CF failures.
   - K=3, n=19, T=1, 3≤d≤4: 947028 canonical critical graphs, **40 irreducible**, 0 R⋆ / 0 CF failures.
   - K=4 Robertson/tree extension family: n=21 **48 irr** (0 fail); n=22 **564 irr** / 588 records (0 fail); all 2-connected.
   - H21 remains the unique critical R⋆-endpoint obstruction in the accepted Petersen-block-tree class, and is reducible (positive star model).

### Still open (honest)
- STAR-LEX_cap(K) / CF-endpoint for **general 2-connected** irreducibles (K≥4, esp. K=6): A+D+E/E1 give necessary distal-mass conditions, not a sufficient safe-repair existence proof.
- General residual cut-vertex for K≥9; conjectural RB_K and small K=6 residual geometries.
- GEN_K (K≥6), NB(6), FP42, RAD(r≥11), REAL-133.

### Certificate
`ROUND_BRANCH_R28_CERTIFICATE.json` sha256 `e17c42d95cd2a195962d8e45e50b067db58807121c43a2a2d9faf67b8f369dea` (built from the two referee `verdict.json` only).

### Recommended next step (R29)
1. Attack the missing capacity/attachment implication that would turn E/E1 distal-mass into a **sufficient** safe root-star repair for 2-connected irreducibles at general K (start K=4 or K=6), or find the strongest weakened selector/budget that still closes STAR-LEX_cap ⇒ GEN_K.
2. Prove or refute RB_K (rank-1 rooted endblock charge) to finish the cut-vertex residual for K≥9 via ASSEMBLY.
3. Optional: extend kill-tests (K=3 n=19 T=2; K=4 beyond the Robertson/tree family; K=5 small n) — no failure expected given R28.


## §4ad — Round 29 (2026-10-23 Asia/Shanghai)

**Protocol.** Same as R26–R28: Astra proves; fresh Astra referee per prover (claim+report+manifest data only); accept CORRECT/CORRECT_WITH_FIXES only; certificate from referee `verdict.json` only. Cap=2 + capguard. Neil "继续" 09:07 → launch. Both provers EXIT 0 under original gated chains; referees auto-started. Neil interrupt-continue 09:58: v_r29_rb already EXIT 0; v_r29_repair still LIVE — monitored only (no relaunch / resume / `:REF`).

**Sessions.**
| Session | Overall | Claims | C | CWF | UNV | Incorrect | Fixes |
|---|---|---|---|---|---|---|---|
| r29_repair / v_r29_repair | CORRECT_WITH_FIXES | 36 | 32 | 1 | 3 | 0 | ring reducible; scope; relative links |
| r29_rb / v_r29_rb | CORRECT_WITH_FIXES | 25 | 22 | 1 | 2 | 0 | L2 nonempty |
| **Total** | | **61** | **54** | **2** | **5** | **0** | |

UNVERIFIED entries are the report's own CONJECTURED/open items (general T_K/T′_K, RB_K/Z_K/C_K for K≥9, GEN_6+/REAL-133, historical/runtime notes, exact global p for F121/F91/G151) — not failures.

**Session ids.** repair prover=`01a1664e-0665-7db2-83b6-38382b8bfb3c`, referee=`01a16672-22f4-7c20-a706-10c7a8ef4e4c`; rb prover=`01a1664d-d7e2-7651-a5e4-7d14d2019951`, referee=`01a16667-e842-70a2-9d7d-c343a6fb6d20`.

**Fixes adopted**
- **FIX-RING.** Every ring graph G_L (L≥2) is **reducible**: contracting one joining edge (no pentagon) yields a positive proper admissible model of surplus 4. Replace the report's "arbitrary-model irreducibility unresolved" with reducible. Mass-obstruction theorem is retained but restricted to the stated 2-connected fully induced-critical domain; it does **not** establish cap necessity inside the irreducible domain, and does not refute fully qualified STAR-LEX_cap.
- **FIX-L2.** Lemma L2 requires H nonempty (or |H|≥2): literally a_K(∅)=K>0. Every downstream application already concerns a nonempty graph; main theorems and certificates unchanged. Aligns with accepted T28.3 (h≥2).
- Packaging: prefer relative links in claim summaries.

### Verified mathematical progress

1. **Constructive fixed-boundary min-cut criterion (r29_repair, VERIFIED).** For K≥2 with G[B_v] triangle-free and fixed C₀⊆C, Δ(G[C₀])≤1: build a network on safe distal vertices D; the exact maximum surplus of safe repairs retaining exactly C₀ is −K−(K−2)|C₀|−e(G[C₀])+P−μ. A cut below the explicit integer threshold constructs a safe positive repair. Both directions; no positivity, criticality, path cap, or GEN required for the criterion.

2. **K=4 infinite no-positive-whole-star family (r29_repair, VERIFIED + FIX-RING).** Ring graphs G_L (Robertson modules + cyclic joins + w): ε₄=2, 2-connected, fully induced-critical, triangle-free strongly C₄-free; every root has max safe whole-star surplus ≤0 while selected roots have unbounded S(Z) (exceeding E/E1) and P9s. Finite feasible-flow base L=2..5 (270 roots) + proved insertion/flow-extension for L≥6. **Adopted:** every G_L is reducible via joining-edge contraction. Consequence: no scalar distal-mass threshold reverses E/E1 under full-criticality alone; the global path cap (and/or arbitrary-model irreducibility) remains indispensable for any sufficiency argument toward STAR-LEX_cap.

3. **Control all-star audit (r29_repair, VERIFIED).** 687 roots / 16 controls: only H21 root 20 has a positive whole-star repair. Exact selected-root maxima S17=−3 (S(Z)=28), F121/F91/G151=−6 (S(Z)=432/272/620 ≫ Q₆=167). Certificate totals: 961 root certs, 1207 tree nodes, 1083 feasible-flow leaves, 0 open proof leaves. S17 and M15 retain accepted irreducibility; ring G₂ is induced-minimal for positivity among the family but reducible.

4. **RB_K ≡ C_K ≡ Z_K reduction (r29_rb, VERIFIED).** For K≥5 the standalone RB_K structural assertion is equivalent to residual irreducible cut-vertex exclusion C_K and to the reduced minimal-rooted-charge statement Z_K. Diagonal α=ε with zero proper rooted charge suffices for full RB_K. Normalization to a 2-connected minimal positive rooted-charge block; identical-endblock amplification is irreducible against every admissible model (T29.1–T29.5). No GEN_(K−1) used for the reduction. **ASSEMBLY:** GEN_(K−1)+T_K+Z_K ⇒ GEN_K (Z_K replaceable by RB_K or C_K). Closed for 5≤K≤8 relative to accepted ROOT. First K=9 normal form: q=9, h≥191, β=1..5 with amplified-order bounds 1901,…,381.

5. **A40 / A157 certified (r29_rb, VERIFIED).** A40: K=6, n=40, e=118, S=236, α=2, ε=−4, nonregular δ=5, p=q(0)=20; minimal rooted charge (39 rooted edge-charge certs + pentagon matchings c≥4 on all 118 edges ⇒ every contracting model ≤35 < 36). Not an RB_6 counterexample (cap absent). A157: four A40 copies at common root; n=157, e=472, ε₆=2, four endblocks, irreducible, exact p=39. Kill-tests: β≥K−3, regularity, unconditional ≤2 blocks all fail. Incomplete K=9 rooted-loss snapshots prove no exclusion.

### Still open (honest)
- STAR-LEX_cap(K) / CF / T_K / T′_K for general 2-connected irreducibles (K≥6): min-cut gives a constructive tool when B is triangle-free; the ring family shows E/E1 distal-mass is **not** sufficient under full-criticality alone.
- RB_K / Z_K / C_K for K≥9 (no counterexample found).
- GEN_K (K≥6), NB(6), FP42, RAD(r≥11), REAL-133.

### Certificate
`ROUND_BRANCH_R29_CERTIFICATE.json` sha256 `5d61db5b9d2f66b694674888cacb067b413cc8739806bdb58435cc977f7919a5` (built from the two referee `verdict.json` only).

### Recommended next step (R30)
1. Attack T_K / T′_K on the capped 2-connected irreducible domain using the new min-cut criterion plus the path cap (ring family shows why the cap cannot be dropped); prefer K=6.
2. Attack Z_K / diagonal RB at the first K=9 normal form (q=9, h≥191, β=1..5), using zero root-star capacities (T29.4) and GEN_8 ⇒ P₁₇ in A−a (T29.5).
3. Optional kill-tests only if they do not dilute the main attack.

## §4ae — Round 30 (2026-10-23 Asia/Shanghai)

**Protocol.** Same as R26–R29: Astra proves; fresh Astra referee per prover (claim+report+manifest data only); accept CORRECT/CORRECT_WITH_FIXES only; certificate from referee `verdict.json` only. Cap=2 + capguard. Neil "继续" 12:04 → launch r30_tk6 + r30_zk9. Neil interrupt-continue 12:54: both provers START with ncodex=0 (killed mid-run), no referees yet — resumed via `resume_then_ref.sh` with original session ids; referees auto-launched after prover EXIT 0. Monitored to completion (no relaunch of live/finished sessions).

**Sessions.**
| Session | Overall | Claims | C | CWF | UNV | Incorrect | Fixes |
|---|---|---|---|---|---|---|---|
| r30_tk6 / v_r30_tk6 | CORRECT_WITH_FIXES | 29 | 25 | 1 | 3 | 0 | portable relative links in CLAIM_SUMMARY / report |
| r30_zk9 / v_r30_zk9 | CORRECT | 28 | 27 | 0 | 1 | 0 | (none) |
| **Total** | | **57** | **52** | **1** | **4** | **0** | |

UNVERIFIED entries are the report's own CONJECTURED/open items (T_6/T′_6/STAR-LEX_cap(6), GEN_6/REAL-133, Z_9/GEN_8/T_9/GEN_9, historical search notes) — not failures.

**Session ids.** tk6 prover=`01a166f0-09b7-7bd2-b041-5dddbb148899`, referee=`01a16729-c2fc-7183-88ec-d220e6709705`; zk9 prover=`01a166ef-db40-79b1-87b5-82334d157e79`, referee=`01a16726-3b3b-72d0-ac80-90fb4527c086`.

**Fixes adopted**
- **FIX-PATHS (tk6 packaging only).** Replace obsolete absolute producer-workspace links in `claim/CLAIM_SUMMARY.md` with portable references to `PROOF_REPORT.md` and `../data/{r30_manifest.json,r30_Q50.g6,r30_Q50.json.gz}`; make bare data-file references in the report explicitly relative to `../data/`. No mathematical gap; no change to any proved statement.

### Verified mathematical progress

1. **Second-moment + distal floor at K=6 (r30_tk6, VERIFIED).** Triangle-inclusive integer second-moment inequality (R30.M) together with smallest-positive-repair constraints (R30.N) imply every smallest positive repaired star at K=6 retains at least **33 distal vertices** (R30.Z33). Relative to accepted order-40/41 theorems, a positive whole-star repair in a fully induced-critical positive K=6 graph requires ambient order **≥50** (R30.F50); no such repair through order 49.

2. **Sharp witness Q50 (r30_tk6, VERIFIED).** Explicit 2-connected triangle-free strongly C₄-free graph Q50 (n=50) attains both Z33 and F50: unique R_⋆ admits a zero-cut repair returning G41 with surplus 2; every vertex has a certified rooted P₁₃; fully induced-critical but **reducible**. Does not refute STAR-LEX_cap(6). Controls, ring FIX-RING, A40/A157, and 59,183 safe retained sets across 277 small graphs independently recomputed.

3. **Capped first distal form (r30_tk6, VERIFIED as necessary).** Under p(G)≤12 and |Z|=33, a smallest positive repair must have (c,m)=(8,30..33) (order 42) or (9,32..33) (order 43), with contracted-root path cap 10 (R30.C33). Neither class excluded. **ASSEMBLY:** GEN_5+T_6 (or T′_6) ⇒ GEN_6. GEN_6 counterexample-order lower bound remains **42**.

4. **Z_9 normal-form sharpening (r30_zk9, VERIFIED).** Every Z_9 counterexample must satisfy q_A(a)=9, |A|≥**254**, β∈{1,2,3} (R30.4a) — improves R29 (|A|≥191, β∈{1..5}). Supporting lemmas verified: saturated-fan dichotomy (R30.2), β≤K−6 (R30.3), mass envelope S≤12n−768 excluding positive charge through order 253 (R30.4), cheap-terminal types (R30.5), β=3 zero-block normal form with four attachment lists (R30.7), degree-six 2-degeneracy / degree-five independence (R30.8). Amplification / original-order bound 334. **Z_9 itself remains CONJECTURED** (no CE, no full proof).

5. **Conditional assembly retained (both, VERIFIED).** GEN_8+T_9+Z_9^res ⇒ GEN_9; general GEN_(K−1)+T_K+Z_K ⇒ GEN_K (Z replaceable by RB/C). RB≡C≡Z inheritance from R29 replayed.

### Still open (honest)
- T_6 / T′_6 / STAR-LEX_cap(6) as universal assertions; Q50 shows Z33/F50 sharpness for whole-star repair but is reducible; capped forms (8,30..33)/(9,32..33) not excluded.
- Z_9 / RB_9 / C_9 under the sharpened normal form (q=9, n≥254, β∈{1,2,3}); residual unbounded class open.
- GEN_K (K≥6); GEN_6 order lower bound still 42.
- NB(6), FP42, RAD(r≥11), REAL-133.

### Certificate
`ROUND_BRANCH_R30_CERTIFICATE.json` sha256 `3f3b111a9bcb7a9b11831d55e6a0786a85ff67551e620375b6c82d7627239bbb` (built from the two referee `verdict.json` only).

### Recommended next step (R31)
1. Force a clean selected endpoint or a successful safe repair under the capped irreducible hypotheses at the R30.C33 forms (orders 42/43, |Z|=33); alternatively exclude those two integer classes.
2. Attack the sharpened Z_9 window (q=9, n≥254, β∈{1,2,3}) via the β=3 zero-block normal form and saturated-fan catalogue; seek CE or further finite reduction.
3. Optional light kill-tests only if non-diluting.

## §4af — Round 31 (2026-10-23 Asia/Shanghai)

Protocol: 4 Astra provers (gpt-6-astra, xhigh) → 4 fresh Astra referees (claim+report+data via mkver.sh). Continuous window (Neil 17:00, cap 6). Three orchestrator interrupts (17:54, 18:45, 19:35): all sessions survived; nothing relaunched. Accepted 128/138 claims (10 UNVERIFIED = explicitly open conjectures / execution history; 0 GAP/INCORRECT).

### Verified mathematical progress
1. **Z_9 = RB_9 = C_9 PROVED (r31_zk9, referee CORRECT, 35C+2UNV).** Stronger statement R31.M9: for every nontrivial connected strongly C4-free graph H and root a, q_H(a)≤9 ⇒ S(H)<9(|H|−1); affine S≤9n−197. Proof: R31.A/B terminal bounds and connected singleton/adjacent-pair deletion (exact loss 18), six terminal types, R31.E9 universal endpoint-pair alternative, exhaustive closed-neighbourhood completion certificate (147 templates, 46,061 records, 0 open leaves; independently recomputed). Also R31.CV9 (fully critical capped cut-vertex exclusion at K=9), R31.B3 (no multiple zero-charge blocks), R31.L. **Conditional:** GEN_8 + T_9 ⇒ GEN_9 (Z_9 premise discharged). Nonnegative K-charge ⇒ rooted P10 for K≥9.
2. **R31.D42 (r31_c33_42, CWF).** Every strongly C4-free graph on 42 vertices with S>252 has Δ≤7. Hence all order-42 C33 classes (c,m)=(8,30..33) are empty (triangles included); R31.I42 such graphs are irreducible against all models. Fixes (wording): "any vertex **of W**"; B_0(0)=D_0(0)=0 base case; final cases are 3/3/2 ("the other five").
3. **R31.D8/B9 (r31_c33_43, CWF).** Positive singleton-critical graphs of order 43 have Δ **at most** 8; the order-43 class (9,32..33) is empty; (8,30) excluded by R31.C30. ⇒ **All R30.C33 necessary forms are excluded**: a positive safe whole-star repair needs |Z|≥34 (conditionally ambient order ≥51). This raises the repair threshold only.
4. **R31 t6_irred (CWF, packaging only).** R31.C33-I (C33 quotients automatically irreducible); R31.2 safe edge contraction (pentagon criterion + surplus identity); R31.3 minimum-order lemma; R31.5 spoke obstruction; R31.7 exact constrained min-cut theorem for star-then-spoke contraction (triangle-free B); R31.8 path lifts (+3/+2 ⇒ rooted caps 9/10); H42 (induced-nonpositive), S44 (two-stage optimum 2, order 44 sharp). Scope: C33 is a necessary form only after a positive repair exists.

### Still open (honest)
- T_6 / T′_6 / STAR-LEX_cap(6): missing **endpoint-failure ⇒ positive proper model (or deletion-loss) existence**. GEN_6 CE-order lower bound still **42**.
- GEN_7, GEN_8, T_9, GEN_9; Z_K for K≥10. NB(6), FP42, RAD, REAL-133.
- Brainstorm (unrefereed): unrestricted degree bound for positive critical graphs is false (Δ=8 n=152, Δ=9 n=153 controls with P13).

### Certificate
`ROUND_BRANCH_R31_CERTIFICATE.json` sha256 `fa0b2e093e8721345a0bbe452949f547405182a6515837bbfebbd451c8708764`. Verdict sha256: c33_42 6d02e254be29…, c33_43 a4632a0e9f12…, zk9 f547c0ad7c06…, t6_irred 3a9bd098b420….

### Recommended next step (R32; wave 1 already running since 19:27)
1. r32_t6_loss: all-order cap-aware deletion-loss lemma L_6 (Δ≤7 / order-42 prototype).
2. r32_t6_model: M_6 near-positive safe star ⇒ positive model via R31.7 spoke min-cut; orders 42–46 by path contradiction.
3. r32_f42: finite capped slice F42 (positive order 42 ⇒ P13), raising GEN_6 CE lower bound to 43.
4. With Z_9 done: Z_K for K≥10 (generalise R31.E9/M9 template method), then T_9/GEN_8 chain.

## §4ag — Round 32 (2026-10-23 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT / CORRECT_WITH_FIXES only. Certificate: `ROUND_BRANCH_R32_CERTIFICATE.json` sha256 `46340d86df9ee4792c9f4c799ed8c0308387d3cdca17c4ec926134188e2e8a21` (created ~21:10 CST). Briefing `data/r32/BRIEFING.md` sha256 `a47b21f2d9b41064416fa289d92c1f347910f64e66b2a844326ed41a66a0dca5`. Four claim sessions + unrefereed brainstorm `bs_r33_t6`.

### Accepted claims (referee verdicts)

| Session | Overall | Breakdown | Headline |
|---|---|---|---|
| r32_zk10 | CWF | 34C+2CWF+2UNV | **Z₁₀=RB₁₀=C₁₀**: q_H(a)≤10 ⇒ S(H)<10(\|H\|−1); 772 states, 0 open leaves. GEN₉+T₁₀⇒GEN₁₀. Fixes: U4 radical n≥1; packaging. |
| r32_t6_model | CWF | 26C+1CWF+4UNV | Star+spoke (ordinary / one-pivot) positive model needs n≥51. M₆/GEN₆ open. Packaging fixes. |
| r32_t6_loss | CWF | 26C+1CWF+4UNV | L_K⇔GEN_K; κ_G degree-4 forest compression; 3 live terminal-contact completions. Cut-vertex open: K≥10 (K=9 closed R31). |
| r32_f42 | CWF | 32C+3CWF+6UNV | n=42 positive fully induced-critical ⇒ ε+T∈{2,4}; deg-7 root distal z≤7 (≤4 if ε+T=4). F42/F43 open; CE lower bound still 42. |

Total accepted claim atoms: 118 CORRECT + 7 CWF of 141 (16 UNVERIFIED = open/history/packaging).

### Adopted fixes (do not re-introduce)
- t6_loss report: missing cut-vertex range is K≥10, not K≥9.
- f42 summary: qualify with positivity + full induced criticality; escape `\` in `r32_f42_encoding.json` line 26.
- zk10 U4: radical form requires n≥1.
- All four: package-relative CLAIM_SUMMARY links.

### Still open after R32
- T₆ / STAR-LEX_cap(6) / GEN₆ (CE order ≥42). Brainstorm `bs_r33_t6` (unrefereed) claims the 3 terminal-contact survivors force a cheap singleton in every capped extension (252-trace certificate).
- Z_K for K≥11; T₁₀, GEN₁₀.
- F42, F43, high-degree model existence for Δ≥8.

### R33 (already launched 20:46)
Mandates from brainstorm §4: A=r33_f42, B=r33_kernel7 (Δ≤7 deletion kernel), C=r33_highdeg, Z=r33_zk11. data/r33 BRIEFING sha256 `18aec11199a1115b1d40c4c369780b517bf703f1ab510d19a277ec9a9d06740b`.

## §4ah — Round 33 (2026-10-23 Asia/Shanghai)

Protocol: fresh Astra referee; accept CORRECT/CWF. Certificate `ROUND_BRANCH_R33_CERTIFICATE.json` (see sha256 file). Briefing `data/r33/BRIEFING.md` sha256 `18aec11199a1115b1d40c4c369780b517bf703f1ab510d19a277ec9a9d06740b`. Strategy brainstorm `bs_strategy_review` (unrefereed) → R34.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r33_zk11 | CWF 37C+1CWF+2UNV | **Z₁₁=RB₁₁=C₁₁**; E11/M11; pendant-root-path kills M10 dep. |
| r33_kernel7 | CORRECT 27C+2UNV | Longest P11/P12 terminals (4,0)/(5,1) or ≥3-contact outside nbr; J-close+. Full Δ≤7 kernel open. |
| r33_highdeg | CWF 25C+1CWF+3UNV | Triangle-free + longest-path endpoint deg≥8 ⇒ positive proper deletion model (323 cases). Full mandate open. |
| r33_f42 | CORRECT 27C+3UNV | 1543 positive triangle-free capped n=42 patterns excluded (incl. G42 bad skeleton). F42 open; CE≥42. |

### Still open / R34 target
T₆/GEN₆. Strategy: single next lemma = triangle-free endpoint-bounded deletion (all longest-path endpoints deg≤7 ⇒ cheap U); assemble with highdeg E8-LOSS ⇒ triangle-free GEN₆.

## §4ai — Round 34 (2026-10-24 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Certificate `ROUND_BRANCH_R34_CERTIFICATE.json` sha256 `8d29038b7bb95d90c21d2bea517dcb28302d60242367becb8d589c254fa3aa4f` (created ~01:05 CST). Briefing `data/r34/BRIEFING.md` sha256 `0767d1aba08bbe11e239b9e01ed297a3247236068b8d5694fff23aee72de1d40`. Two claim sessions from bs_strategy_review (endpoint-bounded deletion + one triangle bridge). Window cutoff 01:00; no R35.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r34_endpoint | CWF 37C+1CWF+2UNV | **R34.A11/A12/R/C**: P11 common-nbr deg-4 family closed (low deg or deg-4 cycle 5–12); P12 with ≤6 interior contacts closed; R33 D1–D3/D2 restored without interior Δ bound; residual: capped longest P11/P12 in no-cheap domain has deg-4 end or ≥3-contact end-nbr. Packaging link fixes only. **EB6 / Δ-free GEN₆ open.** |
| r34_tri_one | CWF 22C+1CWF+4UNV | Triangle-aware loss class + exact elim of (4,0)/(5,1); under p≤12 defects ⇒ cheap \|U\|≤27. New B46/B156 positive critical triangular controls (rooted P13s). Count fix positive_models 4→7. **F42/GEN₆ open; CE≥42.** |

### Still open after R34
- Universal EB6 (all longest-path endpoints deg≤7 ⇒ cheap U) and triangle-free GEN₆; T₆ / GEN₆ inclusive; F42.
- Residual cases: multi-contact both ends ≥5; mixed 4+(5..7); two deg-4 ends w/o common nbr; common nbr ≥3 path contacts; q=12 with ≥7 interior contacts; forest nonempty-W existence.
- Z_K (K≥12), T₁₀, GEN₁₀, RAD, REAL-133.

## §4aj — Round 35 (2026-10-24 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Certificate `ROUND_BRANCH_R35_CERTIFICATE.json` sha256 `132f7ecaba1663f20811bb8930e71f55ac481aa55003d638ca2ad3c0841eb0af` (created ~09:07 CST). Briefing `data/r35/BRIEFING.md` sha256 `59f0c1a0784f075058a9413a2a470d94db90a8dba2219fecec185acebc6a67b7`. Two claim sessions (EB6 residuals + TF GEN₆ assembly). Cap=2; no R36.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r35_eb6_resid | CWF 38C+1CWF+3UNV | **P11 EB6 closed** without endpoint-degree cap (single7/6/5 + shared + separate; 56,852 roots). **R35.A12-full**: entire P12 common-two-contact-neighbor family closed (18,561 roots). Deg-7 P12: **1,463 certified / 122 unresolved** (51 six-contact + 71 seven-contact; all 710 eight-contact and 350 nine-contact certified). Packaging link fixes only. **Universal EB6 still open** at residual P12. |
| r35_tf_gen6 | CWF 37C+2CWF+3UNV | **TF strongly C₄-free mass:** \(S(G)\le 6|V|\) for \(p\le 11\) (R35.P11/M11/CORE); also for \(p\le 12\) when every edge lies in at most one pentagon (R35.PLANE / C1-GEN6). Written **R35.GIRTH7** (K=6) and **R35.GIRTH8** (general K). Doc fix: omission allocations 1,164 + 3 whole-graph. **Unrestricted TF GEN₆ still open** (residual: \(p=12\) with an edge in two pentagons). |

### Still open after R35
- Universal EB6 (all longest-path endpoints deg≤7 ⇒ cheap U) — residual 122 deg-7 P12 patterns; triangle-free GEN₆ unrestricted; T₆ / GEN₆ inclusive; F42 (CE≥42).
- Assembly gap for TF GEN₆: p=12 with an edge shared by two pentagons (needs full EB6 or further residual closure).
- Z_K (K≥12), T₁₀, GEN₁₀, RAD, REAL-133.

## §4ak — Round 36 (2026-10-24 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Certificate `ROUND_BRANCH_R36_CERTIFICATE.json` sha256 `410e10c00646bc3cba711a601b826b83a2078c4fec0b474ab0340e2c91137b34` (created ~10:54 CST). Briefing `data/r36/BRIEFING.md` sha256 `e94181217d08bff68ce01f2377cc1506b6d69f99e06d7bd4173dc59fdd951c43`. Two claim sessions (122 deg-7 P12 residuals + TF GEN₆ double-pentagon residual). Cap=2; no R37.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r36_eb6_d7p12 | CWF 39C+5CWF+6UNV | **All 122 deg-7 P12 residuals closed** (R36.E7-12; with R35 completes all 1,585 deg-7 P12 systems). Unrestricted interior degrees; data-only replay 6,658 states / 2,779,236 path witnesses. Presentation fixes (stored vs extension order; D3 independence; zero-surplus wording; terminal-split; summary links). **Universal EB6 still open** at endpoint degrees 4–6. |
| r36_tf_gen6 | CWF 35C+2CWF+3UNV | **TF strongly C₄-free mass:** \(S(G)\le 6|V|\) when \(p\le 12\) and every edge lies in at most **three** pentagons (extends R35’s ≤1-pentagon bound), with exact δ≥4 classification and weighted deletion. 122 deg-7 closures frozen. Doc fixes: max displayed order 29 stored / 30 leaf-extension; package links. **Unrestricted TF GEN₆ still open** (residual: edge in ≥4 pentagons and longest-path endpoints deg≤6). |

### Still open after R36
- Universal EB6 (all longest-path endpoints deg≤7 ⇒ cheap U) — deg-7 P12 closed; residual endpoint degrees 4–6.
- Unrestricted triangle-free GEN₆; T₆ / GEN₆ inclusive; F42 (CE≥42).
- Assembly gap for TF GEN₆: \(p=12\) with an edge in ≥4 pentagons (and endpoints deg≤6).
- Z_K (K≥12), T₁₀, GEN₁₀, RAD, REAL-133.

## §4al — Round 37 (2026-10-24 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Certificate `ROUND_BRANCH_R37_CERTIFICATE.json` sha256 `27894d51a027f033ec005b94f6ff57f75c1a4bdb866eb926af207324b6683758` (created ~12:58 CST). Briefing `data/r37/BRIEFING.md` sha256 `21ce4592f4f5bd5d276f38fa70883777e2777f1d7fc0570f45ac5236770dc054`. Two claim sessions (endpoint deg 4–6 / universal EB6 + TF GEN₆ ≥4-pentagon residual). Cap=2; continuous window until 18:00; parent may chain R38.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r37_eb6_d46 | CWF 37C+2CWF+2UNV | **R37.M11-28** \(S\le6n-28\) for TF strongly C₄-free \(p\le11,\,n\ge8\) + transversal closures; **all 301** deg-6 nine-contact P12 systems (R37.E6-9); **all 63** deg-5 nine-contact under endpoint cap five (R37.E5-9); one explicit deg-4 family under endpoint cap four. 713-root replay. Packaging/notation fixes. **Universal EB6 still open** (avoiding class A37 / surviving deg-4 nine-contact). |
| r37_tf_gen6 | CWF 34C+2CWF+3UNV | **TF mass with common-adjacent spine:** \(S(G)\le6|V|\) when \(p\le12\) and all pentagons through any edge of multiplicity ≥4 share a common adjacent edge (multiplicity unbounded; B-CLASSIFICATION / B-MASS / cover). 145 completion roots + 28 minimal B-obstructions. Scope wording + packaging fixes. **Unrestricted TF GEN₆ still open** (without the common-adjacent-edge hypothesis). |

### Still open after R37
- Universal EB6 (exact remaining avoiding class A37 / surviving degree-four nine-contact; endpoint degrees 4–6 not fully closed).
- Unrestricted triangle-free GEN₆; T₆ / GEN₆ inclusive; F42 (CE≥42).
- Assembly residual: ≥4-pentagon edges without common-adjacent-edge spine (and endpoints deg≤6).
- Z_K (K≥12), T₁₀, GEN₁₀, RAD, REAL-133.

## §4am — Round 38 (2026-10-24 Asia/Shanghai)

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Certificate `ROUND_BRANCH_R38_CERTIFICATE.json` sha256 `0f199e4ec5681d92467b04bd0747029235edba3341ef7b3f3f13feeec2ee2bd5` (created ~14:42 CST). Briefing `data/r38/BRIEFING.md` sha256 `160c4ca00524afe61ca368a5102aac8b92c16e6f86810c1c2ac6457db4590af7`. Two claim sessions (A37 / surviving deg-4 nine-contact / endpoint deg 4–6 residual ⇒ universal EB6 + unrestricted TF GEN₆ residual). Cap=2; continuous window until 18:00; parent may chain R39.

### Accepted
| Session | Overall | Headline |
|---|---|---|
| r38_eb6_a37 | CWF 30C+1CWF+3UNV | **R38.M4** entire endpoint-cap-four branch: all **2177** deg-4 P12 systems including survivor **2176**; **R38.M4-MASS**; **R38.E6-8** all **1140** deg-6 eight-contact (+ accepted E6-9); **R38.E5-8** all **494** deg-5 eight-contact under endpoint cap five (+ accepted E5-9); **154** additional deg-6 seven-return systems (partial slice); exact remaining avoiding class **A38**. Replay 1,668,068 states / 57,501,752 path witnesses. Packaging-link fixes. **Universal EB6 still open** (lower-contact deg-5/6 residuals). |
| r38_tf_gen6 | CWF 39C+1CWF+3UNV | **TF SM/SMP mass:** \(S\le6n\) for triangle-free strongly C₄-free \(p\le12\) when every ≥4-pentagon edge has a common adjacent edge, **or** disjoint pentagon interiors, **or** exactly four pentagons inducing Petersen; for \(n\ge14\), \(S\le6n-38\). Exactly **22** minimal SM + **21** minimal SMP obstructions; E14/E16 edge bounds; DELETE19/COVER19. Packaging-link fixes. **Unrestricted TF GEN₆ still open**. |

### Still open after R38
- Universal EB6 (lower-contact degree-five/six residuals under cap5/cap6; A38 nonempty as a restriction, not emptied).
- Unrestricted triangle-free GEN₆; T₆ / GEN₆ inclusive; F42 (CE≥42).
- Z_K (K≥12), T₁₀, GEN₁₀, RAD, REAL-133.

## §4an — Round 39 (2026-10-24 Asia/Shanghai) — STARTED

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Briefing `data/r39/BRIEFING.md` sha256 `d7ca765d3daef4463a359a44d9d6bbbedb5903263afdde36d990e10f1c777852`. Two claim sessions (lower-contact deg-5/6 / A38 ⇒ universal EB6 + unrestricted TF GEN₆ drop SM/SMP). Cap=2; continuous window until 18:00; parent may chain further rounds before 18:00. **No accepted theorems yet this round** (sessions launching). Prior accepted baseline: R38 certificate sha256 `0f199e4ec5681d92467b04bd0747029235edba3341ef7b3f3f13feeec2ee2bd5`.

### Targets entering R39
- Universal EB6 via lower-contact deg-5/6 residual families / kill A38.
- Unrestricted TF GEN₆ (remove SM/SMP hypotheses).
- Side (deprioritized): T₆/GEN₆ inclusive; F42.

### STRATEGY REDIRECT (Neil t183u, ~14:53 Asia/Shanghai)
Stopped contact-sweep sessions `r39_eb6_low` / `r39_tf_gen6`. Relabeled mandate: structural kill of avoiding class **A38** in one argument (`r39_a38_kill`); unrestricted TF GEN₆ by **dropping** SM/SMP hypotheses (`r39_tf_drop`); secondary general-K lemma entrance only if primary finishes early. Catalogues in `r38_remaining.json.gz` are kill-tests/sanity only — not the proof plan. Briefing re-bumped sha256 `678048331fb382a52a30682c3430644f5551252b55ebe1f80260fe1a2754377e`. Cap=2; window until 18:00; no paper/push/R40. Structural sessions START 14:54:22 / 14:54:34 CST (sids `01a16cb0-6923-7ba3-92a0-2d33586704c2` / `01a16cb0-979d-7ab0-8932-9da00bf1ce8b`). **No accepted theorems yet this round**.

### R39 CLOSED (~16:32 Asia/Shanghai)
Both referees CWF; accept **60/65**. Certificate sha256 . Proved H31-EB/H35-CAP5/H28+C106/ROOT7/NO-CUT/PAIR/A39 + Robertson/D framework; A38 not emptied; unrestricted TF GEN₆ reduced to D-free residual. See .


## §4ao — Round 40 (2026-10-24 Asia/Shanghai) — STARTED

Protocol: fresh Astra referee per claim (mkver.sh); accept CORRECT/CWF. Briefing  sha256 . Two structural claim sessions (empty A38 ⇒ universal EB6 + discharge Robertson/D-free residual ⇒ unrestricted TF GEN₆). Cap=2; continuous window until 18:00; **no R41** this window. **No accepted theorems yet this round** (sessions launching). Prior accepted baseline: R39 certificate sha256 .

### Targets entering R40
- Universal EB6 via structural empty-A38 (cite R39 H31-EB/H35-CAP5/A39/ROOT7/NO-CUT/PAIR).
- Unrestricted TF GEN₆ via discharging Robertson/D-free residual (cite R39 D-framework).
- Secondary (if primary finishes early): one usable general-K lemma entrance (CP(K)/path-cap).
- Forbidden as main claim: contact-catalog sweeping.

## §4ap — Round 40 closed (2026-10-24 18:15 CST)

Window ended 18:00 Asia/Shanghai (Neil t184u packaging). Sessions `r40_a38_empty` / `r40_tf_dfree` both CWF. Certificate sha256 `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`.

Headline accepted (CORRECT/CWF only):
- A38 lane: MIN4-P11; C4-D36; END18; H32-MASS; H36-CAP5-MASS; forest/support identities; BOUNDARY rows; C112; residual-reduction equivalence (conditional); fixed-cap transfer.
- TF lane: puncture classification R/X21/X22/X23; sharp 7-cheap; puncture-free residual reduction; residual equivalence to unrestricted TF GEN6 (conditional).

Open unchanged at top level: universal EB6 / A38 emptiness; unrestricted TF GEN6; T6; F42; GEN_K / RAD / REAL-133.

