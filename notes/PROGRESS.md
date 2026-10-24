# PROGRESS (excerpt for public archive)

Full working log lives in the private work tree. This excerpt keeps the header and R35–R40 / window-close entries through 2026-10-24 18:00 Asia/Shanghai.

# round_branch progress (started 2026-10-18 08:06 UTC+8)
Goal: BRANCH-BOUND / TWO-HUB / GEN_3 via Astra (codex exec -m gpt-6-astra xhigh), independent verification.
- launch.sh <dir> runs codex detached -> dir/codex.log, dir/report.md, dir/status.txt
- R1 launched: astra_r1/A (skeleton bound / direct GEN_3) launcher pid 899462, session 01a14c53-fd25-7862-b94f-62323d72287e; astra_r1/B (two-hub) launcher pid 899463.
- M3 check (min deg>=3 connected P7-free strong C4-free): n<=19 only Petersen (single-thread runs, m3/d3_n*.g6). n=20 launched via m3/run_d3.sh pid 925644 (log m3/d3_progress.log).
- R1 finished: B exit 08:24, A exit 08:37 (reports astra_r1/{A,B}/report.md).
- R1 verification: all proofs hand-checked; finite checks re-implemented independently (verify/indep_local.py, own code) -> all counts match.
  Deliverables: PROOF_NOTES.md, ROUND_BRANCH_R1_CERTIFICATE.json (payload 028b1961...), verify_round_branch_r1.py -> OVERALL PASS (verify_r1.log, ~5 min).
- OUTCOME R1: GEN_3 proved (computer-assisted, Astra track A, verified) => REAL-133 cell r=3, 3<ell<4 closed. Track B: dominating-pair lemmas, n<=588 reduction.
- Still running (detached): m3/run_d3.sh 20 (pid 925644; slice 0 genp7 pid 925654; 7/8 slices finished with 0 graphs). Not needed any more (superseded by GEN_3).
- NEXT (R2 plan, not started): (1) fresh adversarial Astra/Codex audit of the GEN_3 proof; (2) attack GEN_4 / cells ell>4 (r=3,K>=4 via PHI_K; r>=4) by generalising admissible-graph local charging (L>=K+1, ears) to K=4; (3) C reimplementation of local checks.
- R2 launched 08:50: astra_r2/audit (adversarial referee of GEN_3, launcher pid 952310, session 01a14c7c-c62b-7450-bd06-b4d0724876ce); astra_r2/gen4 (GEN_4 attack, launcher pid 952311, session 01a14c7c-c647-7902-a47a-6a898edeb27d). C reimplementation: verify/local_c.c (in progress).
- m3 n=20 finished 08:48: count=0 (min-degree>=3 connected strong C4-free P7-free graphs: only Petersen for n<=20). Recorded; superseded by GEN_3.
- C reimplementation verify/local_c.c (all subsets of free pairs, matchings NOT imposed, two-fork cross pairs free): counts identical (log verify/local_c.log).
- R2 audit finished 08:59: verdict CORRECT; 3 presentational fixes applied to PROOF_NOTES.md.
- R2 gen4 finished 09:14: Astra claims GEN_4 via star certificate (L>=5 & P9-free => no induced K_{1,5} => lambda<=4).
  Verified: hand steps checked; my C verifier gen4/vcert.c PASS (identical counts; P9 routine validated vs brute force); stdlib checker verify_round_branch_r2.py OVERALL PASS (verify_r2.log). Certificate copied to data/GEN4_star_certificate_p9.json.
  ROUND_BRANCH_R2_CERTIFICATE.json written. PROOF_NOTES.md §4b added. Own sanity: admissible4 graphs n<=17 all have lambda<=4 (gen4/adm4*.out).
- R2 DONE. No detached jobs running.
- NEXT (R3 plan): GEN_5 via star certificate (P11-free, L>=6, exclude K_{1,6}) — try Astra generator; RAD r=5 (p=9) layering; Lean formalisation of GEN_3 (plan in report).
- R3 launched 09:37: astra_r3/audit4 (GEN_4 adversarial audit, pid 990413), astra_r3/genK (K-uniform STAR_K / GEN_K, pid 990414), astra_r3/rad5 (RAD r=5, pid 990415). Correction recorded: RAD cells (r=K+1,p=2r-1) are NOT closed by GEN_K; r=5,p=9,4<ell<=5 open.
- 09:38 K=5 star search genK/starK (pid 992424) started; KILLED 09:58 (STAR_5 shown false, search could only find hits; no output yet, <2000 records).
- R3 Astra results (all exited ~09:51-09:55):
  audit4: GEN_4 CORRECT (own verifier reproduces all counts); presentational fixes adopted in PROOF_NOTES §4c.
  genK: STAR_5 FALSE (Petersen amalgams, verified verify/star5_cex.py); rooted-path lemma + low-unit structure (hand-checked).
  rad5: RAD*(5) radius 5 & P10-free => e=n+T (ell<=2). Hand-checked; finite classifications reproduced by my own verify/rad5_mine.py. => REAL-133 holds for all ell<=5 (Cor 15).
  radK/radtest.c: all connected C4-free n<=14 with r>=4, p=2r-1 satisfy e=n+T (sanity).
- R3 deliverables: ROUND_BRANCH_R3_CERTIFICATE.json + verify_round_branch_r3.py -> verify_r3.log OVERALL PASS (~2 s).
- R3b launched 10:02 (follow-up discussion round): astra_r3b/radK (uniform RAD*(r), launcher pid 1020340, session 01a14cbe-ac6b-7803-b5bf-c6dae8f5fd69);
  astra_r3b/genK2 (K-uniform GEN_K with set-loss + GEN_5, launcher pid 1020341, session 01a14cbe-ac77-7c31-8b0b-0e5d8d2218dd).
- 10:16 radK finished: strong identity RAD*(r) (e=n+T) FALSE for all r>=6 (C6 + pendant paths length r-3 + pentagonal ears c0-x-z-y-c1; r=6,n=27,e=28,T=0,p=11). Verified verify/radstar_cex.py. Weak RAD(r) (ell<=r-1, what Thm B needs) still open for r>=6; examples have ell<8/3.
- 10:17 radK2 launched (weak RAD(r) via core+rooted-mass decomposition, ROOT(q) lemma): launcher pid 1034875, session 01a14ccc-b21d-7d73-8231-fbef193a3203.
- ROOT(q) sanity (radK/roottest.c): S <= (q-1)(n-1) for root with max rooted induced path q>=3 holds for all connected C4-free n<=13 (q=2 fails trivially: stars).
- radtest n=15: 93 graphs with r>=4,p=2r-1, all e=n+T (r=4 only). n=16 running (bash pid 1023495).
- 10:29 resumed after interruption: genK2 (pid 1020341) and radK2 (pid 1034875) still running; waiting.
- 10:39 radK2 finished: claims RAD(6) (radius 6, P12-free => S <= 5n-36), computer-assisted, plus ROOT(4) hand proof (S <= 3(n-1)-d(s), sharp). Hand-checked reduction + mass lemma (1) + accounting.
  Independent check verify/rad6_mine.py running (own code): F_{10,1} all counts reproduced (31 traces, 11 pairs, (3) 0, (4) 0/39680); F_{8,2}, F_{6,3} in progress (log verify/rad6_mine.log).
- 10:44 genK2 finished: no uniform proof. Results: charge identity; DFS branching bound giving a computable (astronomical) bound f(K); n >= K^2+2;
  in minimum GEN_5/GEN_6 counterexamples every oriented edge extends to P6/P7, so both are 2-connected; sound set-loss attachment rule (GEN_5 search blows up, 6375 states at order 16).
  Hand-checked; control Q and ROOT(4) family re-verified (verify/genK2_checks.py).
- RAD(6) VERIFIED: verify/rad6_mine.py reproduces all counts (F_{10,1}, F_{8,2}, F_{6,3}). Corollary 17: with ell <= 6, only (r=4,p=9) and (r=5,p=10) remain open; both need GEN_5.
- radtest n=16 finished: 382 graphs with r>=4, p=2r-1 (380 at r=4, 1 at r=5), all e=n+T (consistent with RAD*(4), RAD*(5)).
- R3 certificate extended (rad6 + RAD* counterexample); verify_round_branch_r3.py -> verify_r3.log OVERALL PASS (53 s). sha256 cef23e9c...
- PROOF_NOTES §4d and §5 updated. ROUND 3 DONE 11:18. No detached jobs running.
- NEXT (R4 plan): (1) GEN_5 restricted to cells (r=4,p=9) and (r=5,p=10): exploit the radius (dominating structure via Camby-Schaudt) rather than full GEN_5;
  (2) EP endpoint lemma (uniform route); (3) RAD(7) via the radK2 method; (4) ROOT(5).
- R4 launched 11:19 (astra_r4/*): cells (CELL A r=4,p=9; CELL B r=5,p=10) pid 1142650 session 01a14d05-d0a8-70b2-9153-921275128897;
  ep (EP lemma + two-arm splicing) pid 1142651 session 01a14d05-d099-7783-82ab-d13cf301d4ba; rad7 (RAD(7) + ROOT(5)) pid 1142652 session 01a14d05-d0a3-70b0-b2ae-847b0f0d9fdb;
  audit5 (adversarial RAD5) pid 1142653 session 01a14d05-d097-7912-bc18-0fc7feef0db0; audit6 (adversarial RAD6 + ROOT4) pid 1142654 session 01a14d05-d090-7e70-914a-9b567f87db76.
- 11:23 steering (Neil): broaden with idea-generation sessions. Launched astra_r4/idea1 (discharging/LP/flag/averaging) pid 1148727 session 01a14d08-c638-7f61-8fd1-7106e6e5f314;
  idea2 (radius-keeping induction, dominating structures, BFS layer mass) pid 1148728 session 01a14d08-c628-78a3-bae2-eda127b14728;
  idea3 (counting/probabilistic/GEN_K counterexample constructions) pid 1148729 session 01a14d08-c622-7ab3-8ed4-5e6a5bb00976. Shared state file astra_r4/STATE.md.
- 11:20 own data job radK/celltest (max ell per (r,p), n=10..15) pid 1144352 -> radK/celltest.log.
- 11:41 audit6 finished: RAD(6) + ROOT(4) CORRECT (own code reproduces all RAD6 and inherited RAD5 classifications; 2 presentational wording fixes).
- 11:48/11:49 idea1, idea2 finished. My quick tests (ideas/): idea1#2 path-count recurrence I_{2k+1} >= (ell-k) I_{2k-1} SURVIVES on Petersen, B_2..B_6, Petersen vertex amalgams, ER_3/5/7, HS (tightest ratio 1.18 at k=5), theta_10, the RAD* example, and Astra's close case (1.075).
  idea2 stress graph verified: C6 + length-4 arms + 11 Petersen blocks: n=129, r=7, p=13, ell=3.02 (so RAD(7) admits no ell<=3 bound; fine for ell<=6).
- celltest (own data): CELL A (r=4,p=9) max ell 2.71 (n<=14); CELL B (r=5,p=10) max ell 2.43 (n<=14). n=15 still running (pid 1144352).
- 11:50 audit5 finished: RAD(5) CORRECT (own code reproduces all six classifications; the only 'gap' is that the l<=5 corollary needs GEN_3/GEN_4, which are proved separately and were not in that session's context).
- 12:04 new rule (/workspace/bot-rule/dispatch.md): max 2 concurrent Codex sessions, exponential backoff; running ones (cells, ep, rad7, idea3) left alone, no new launches until <2 running; further sessions queued.
- ~11:54 BOX REBOOTED (uptime check at 12:14): all detached jobs died (Astra cells/ep/rad7/idea3 mid-run; celltest had finished n=15: CELL A max ell 2.933, CELL B 2.667).
- 12:15 resumed per the 2-concurrent rule via resume_chain.sh (codex exec resume <session>, exponential backoff 60s*2^k, 6 tries):
  chain1 (pid 37289): ep -> rad7 ; chain2 (pid 37954): cells -> idea3. (A first chain2 launch, pid 37290, carried the wrong idea3 session id and was killed within seconds.)
  At most 2 Codex sessions from this agent at any time.
- 12:19 ep finished (resumed): EP PROVED for q<=6 (charge lemma, hand-checked outline); EP passes all 364.8M oriented-edge domains n<=14; EP+ FALSE (K?`@?b_JAsOw: root 8, q=8, D(E)=16>14, verified ideas/ep_checks.py); componentwise charging fails (I?AE@`ke?, verified).
  Two-arm reduction: lambda_H(s) >= lambda_G(s)-(K-1) after deleting N[arm]\{s} (hand-checked); exact boundary identity; for K=5,6 the ONLY missing step on this route is the boundary-selection inequality (8).
- 12:23 cells finished (resumed): cells NOT closed. Partial results (Astra-proved, Astra-audited): dominating C6/C7/C8/C10 branches of CELL A; C9/C11 branches and the p(H)=7 core of CELL B. Remaining: CELL A cores r(H)=3, or the Theorem-D C6 core not dominating G; CELL B core r(H)=4, p(H)=8.
  Families G_{b,t} (B_b plus two tails) give ell -> 7/2 in both cells (verified ideas/cells_fam.py). Data: CELL A max ell 2.93 (n<=15), CELL B 2.67.
- chains continue: rad7 (chain1) and idea3 (chain2) resumed (2 concurrent).
- ~12:40 rad7 finished (resumed): Astra claims RAD(7) (S <= 5n-42), Struct(5..7), lifting lemma, ROOT(5) (S <= 4(n-1)-2d(s), coefficient 4 optimal), radius-extremal ell unbounded (projective-plane grafts).
  Hand-checked: RAD(7) mass argument (D-clique <=3, M(J)<=5|J|, tip savings, constants), lifting-lemma logic.
- ~12:45 idea3 finished: ranked routes (random induced walk, two-ball loss, Moore-type counting, triangle-deleted ER_q, amalgam exclusions, scalar dominating-core recurrence); warns a degree-57 Moore graph would refute GEN_K while satisfying REAL-133.
- No Codex sessions running since ~12:45 (all 8 R4 sessions EXIT 0).
- verify/rad7_mine.py (pid 52470, own code) DONE: all RAD(7) classifications reproduce Astra exactly: C4+dist-safe 85/231/313/339, singles 37/51/57/55 = claimed lists, pairs 13/51/73/91 = claimed lists, rooted A-R^k exclusion 0, three-parent 0 (all four flowers).
- verify/rad7_64facts.py (own code): (6,4) facts (a) two-parent survivors exactly 6 rotations, (b) 0, (c) 0. (First run had a fixed-after-new ordering bug that gave 777/4248/2304; fixed by ordering fixed vertices first; clean log rad7_64facts.log.)
  => RAD(7) VERIFIED (finite part independently; mass argument by hand). ROOT(5) general lemma: Astra-proved, not independently re-derived; sharp family F_b (S=4(n-1)-6, rooted max 5) verified ideas/rad7_examples.py; radial example n=69 r=7 p=13 S=210 verified.
- Idea tests (ideas/idea3_tests.py, twoball_bb.py): random induced walk E ceil(|P|/2) >= ell (min lambda>=2) SURVIVES on Petersen (tight, =3), B_2..B_4, Pet^3, theta_6, ER_5.
  Two-ball lemma (some edge with proper U_xy=B2(x)uB2(y), D(U)<=K|U|) REFUTED: B_5 (n=42, p=9, K=5) min ratio 5.22; B_b ratio grows (6.44 at b=12); Pet^12 vertex amalgam 5.30.
- R4 certificate: build_r4_cert.py -> ROUND_BRANCH_R4_CERTIFICATE.json; checker verify_round_branch_r4.py running (pid in verify_r4.pid) -> verify_r4.log.
- verify_round_branch_r4.py -> verify_r4.log OVERALL PASS (119 s). Certificate sha256 42c860ade94c3037...
- PROOF_NOTES §4e (R4) and §5 (open, updated R4) written. ROUND 4 DONE 12:39. No detached jobs or Codex sessions running.
- R5 certificate: ROUND_BRANCH_R5_CERTIFICATE.json (sha256 ac372227…); verify_round_branch_r5.py → verify_r5.log OVERALL PASS (0.3s).
- All 4 R6 sessions EXIT 0; 0 Codex. Certificate ROUND_BRANCH_R6_CERTIFICATE.json (sha256 fa5d1eefea0b551d…); verify_r6.log OVERALL PASS. PROOF_NOTES §4g/§5 updated. ROUND 6 DONE 15:52.
  - cellsA1A2B1: `python3 scratch/reproduce.py` EXIT 0 (ctx sha256 OK; tables/b1_family regenerated); audit.json / charging_audit.json (92) / c5_audit.json (6) present — matches Astra’s 98-core audit claim.
- 18:03 ROUND_BRANCH_R7_CERTIFICATE.json built from referee verdict.json files (sha256 222e74e8d57ffbf1…). ROUND 7 DONE. R8 running: root7 (lane1, since 17:41), ep8 (lane2, since 17:53); queued: cells (lane1) then referees v_root7, v_cells; v_ep8 after ep8.
- 19:25 ROUND_BRANCH_R8_CERTIFICATE.json built from referee verdict.json files (sha256 8265dadbfe1d0b6a…). ROUND 8 DONE.
- 22:05 ROUND_BRANCH_R9_CERTIFICATE.json built from referee verdict files (sha256 b65661bc26dbe97f…). ROUND 9 DONE.
- 22:44 ROUND_BRANCH_R10_CERTIFICATE.json built from referee verdicts (sha256 3fc0bd9179f01d65…). ROUND 10 DONE. No R11 launched.
- 00:04 ROUND_BRANCH_R11_CERTIFICATE.json built from referee verdicts (sha256 279ffa80b7dad0c8…). ROUND 11 DONE. No R12 prepared/launched.
- 01:58 v_r12_charge EXIT 0 01:56: OVERALL CORRECT (24/24 claims CORRECT, no fixes; all 3 certificates independently regenerated). VERIFIED: **GEN_5 (p≤10 ⇒ S≤5n)**; REAL-133 for p≤10; **REAL-133 for ℓ≤6 ⇒ Cell B CLOSED** (via RAD(6) for r=6, p=11); GEN_6 for p≤10, plus a p=11 reduction. All R12 sessions EXIT 0, with no retries or GAVEUP. §4m complete.
- 01:59 ROUND_BRANCH_R12_CERTIFICATE.json built from the 3 referee verdict.json files (sha256 bb04701f4f5f71476c65d573f789ac246af192f56b4f4f7c5498af60d54b1507). ROUND 12 DONE. No R13 prepared or launched.
- 08:42 ROUND_BRANCH_R13_CERTIFICATE.json built from the 3 referee verdict.json files (accepted claims: A 33/40, B 33/39, compare 84/98; the rest are UNVERIFIED conjectures/provenance). sha256 65be08d6da4472882eeb1116c68ae877745a35ff94d03e817a5f106a230622fa. ROUND 13 DONE. PAUSED per Neil: no R14, paper untouched.
- 14:43 ROUND_BRANCH_R14_CERTIFICATE.json built from the 2 referee verdict.json files (accepted: CE 25/27, RC 33/38). sha256 bf9c54e049f0e994c1f7c74f697098ab5f8577e14ab46a46751d281a2a4655a8. ROUND 14 DONE. No R15; paper untouched.
- 16:05 ROUND_BRANCH_R15_CERTIFICATE.json built from the 3 R15 referee verdicts (accepted RC611 32/34, CE612 26/28, general 38/42). sha256 b19d57690283b2e5fa5b90dad78ec5d890b365f1520e9348c805a771b127b293. ROUND 15 DONE; GEN_6 not closed. R16 running: r16_RC612 (START 15:38), r16_RC611 (15:50), r16_CE612 (16:02). ncodex=3/4.
- 17:06 v_r16_CE612 EXIT 0 17:02: CORRECT, no fixes (32/34; UNVERIFIED: provenance, CE(6,12) λ=7/8 residual). VERIFIED: 518 more records excluded; residual 12,773 (λ8: 911, λ7: 11,862); five-vertex cheap-set certificate; no counterexample. ROUND_BRANCH_R16_CERTIFICATE.json built from the 3 R16 verdicts (RC612 41/45, RC611 31/34, CE612 32/34), sha256 fd826854e2b26ffdd3174fc9ff74cca00e1de5ea383455199d87bc277fb60c69. ROUND 16 DONE. GEN_6 NOT proved (RC(6,11)/MASS_11, CE(6,12) λ=7,8 and RC(6,12) open). .codex_cap reset to 2; watcher stopped. STOP: no R17, paper untouched.
- 19:22 v_r17_compare EXIT 0: CORRECT_WITH_FIXES (77 CORRECT + 1 CWF / 86; UNVERIFIED: R1–R5 proposals, open targets, literature). Fix: diverge corollary needs K≥2. §4r complete. ROUND_BRANCH_R17_CERTIFICATE.json built from the 3 R17 verdicts (pathRC 30/31, diverge 31/32, compare 78/86), sha256 4fac5fa2984cf9fb528de431ff05391d72757ad008c988fc2342f5d7a05871e5. ROUND 17 DONE. No R18; paper untouched; the watcher/launcher exited; my sessions use 0 Codex slots; cap 2.
- 20:31 v_r18_uniformRC EXIT 0: CORRECT_WITH_FIXES (36 CORRECT + 3 CWF / 43). VERIFIED: Theorem R (odd step: ≥K recipients; K/K+1 ⇒ one component; odd RC for |B|≤K−1), Theorems M/S/E, shield theorem, even K² barrier, cut residuals, cheap-set identities. MISSING: CE-X, P, F (plus SRS/shield). r18_compare NOT run (no general theorem verified; missing lemmas already isolated). ROUND_BRANCH_R18_CERTIFICATE.json built (uniformRC 39/43, contract 39/45), sha256 eb251a5db4654ed820939b137f47c59623c3f0e5ed7421bff9c115e373e780e8. ROUND 18 DONE. General GEN_K NOT proved. No R19; paper untouched; watcher stopped.
- 22:49 v_r19_compare EXIT 0: CORRECT_WITH_FIXES (32 CORRECT + 4 CWF / 43). VERIFIED: GEN_K ⇔ (18) ⇔ IR_K; exact p(G42)=p(HS)=20; 37 irreducible HS cores with p=20; no counterexample in polarity, field or amalgam searches; bounds (F),(G),(H). Recommendation: near-order-barrier path lemma, then small-transversal dichotomy. §4t complete. ROUND_BRANCH_R19_CERTIFICATE.json built (A 46/51, B 42/46, compare 36/43), sha256 c64b5ef4000d56e19e0a8560af7a6ab7e3d89fb26796b64c04b23870bd0d616c. ROUND 19 DONE. (18)/general GEN_K NOT proved. No R20; paper untouched; watchers stopped.
- 01:10 ROUND_BRANCH_R20_CERTIFICATE.json built from the 3 verdict.json files: barrier 38/41, transversal 48/54, compare 39/44 accepted.
  - sha256 cbdd36f7d48c45a9944b3dd3342467527ba5953a315e708dcb3b7dc58a70bc48
  - Watcher/tail stopped; no R20 sessions left running. R20 CLOSED; no R21; paper untouched.
- 08:46 ROUND_BRANCH_R21_CERTIFICATE.json built from the 3 verdict.json files: n41 30/37, general 28/34, compare 31/35 accepted.
  - sha256 e890a775b9565a6b86e44f83b2393b84b6a3f2252573cdfbfabc602db12e9075
  - Watcher/tail stopped; no R21 sessions running. R21 CLOSED; no R22 started; paper untouched; nothing pushed.
- 10:15 r22_endpoint EXIT 0 10:12. Prover claims (not yet refereed), PROVED computer-assisted: (41,4) EMPTY; (41,3) always contains P13; every positive-6-surplus graph on 41 vertices has profile (1,0,36,4) and contains P13, so a GEN_6 counterexample needs n ≥ 42. Evidence: 4 CNF instances with deletion-free RUP refutations (2,873,790 additions) + matching cases with P13 witnesses. mkver's default copy omits .cnf/.rup.gz, so I copied the 8 manifest-required CNF/RUP files into v_r22_endpoint/data (all 23 manifest sha256 match) and added a soundness/encoding focus to the referee prompt before it started. v_r22_endpoint is waiting at the gate.
  - PROVED computer-assisted: K=6 cell (43,5) CLOSED. Its graphs have (ε,T)=(6,0) and contain P13 (7 CNF/DRUP refutations); explicit irreducible G43 proves nonemptiness. Uniform path-contact accounting, top-boundary triangle and two-root normal forms, localisation of large surplus.
- 10:22 v_r22_nbex2 auto-started at 10:21:00 WITHOUT the 14 CNF/DRUP certificate files (mkver copies only json/txt). Killed it after ~40 s (empty scratch), copied all 47 manifest files (sha256 verified), added the soundness/encoding focus, and requeued it as a :REF follower (chain 2410290); fresh START 10:21:44.
- 10:44 v_r22_nbex2 EXIT 0 10:42: CORRECT (22 C + 1 UNV / 23, no fixes). VERIFIED: (43,5) CLOSED, i.e. (ε,T)=(6,0) only, and P13 holds there (7 RUP refutations independently checked; encodings sound); G43 irreducible; uniform contact identity, capacity inequality, triangle/derangement normal forms; ε ≥ K−1 localises to the top boundary. Copied to data/r22. v_r22_endpoint still live.
- 10:56 ROUND_BRANCH_R22_CERTIFICATE.json built from the 2 verdict.json files: endpoint 34/36, nbex2 22/23 accepted.
  - sha256 fa45115f68645a0393efe9e23a6608a49c612d85983bac3c86a2e1dddb292170
  - Watcher/tail stopped; no R22 sessions running. R22 CLOSED; no R23 started; paper untouched; nothing pushed.
- 12:45 ROUND_BRANCH_R23_CERTIFICATE.json built from the 2 verdict.json files: direct 39/43, reformulate 37/39 accepted.
  - sha256 97a06c2ab116458fb6f35e5fe709be02e595145461623f28688201f6b04ceef2
  - Watcher/tail stopped; no R23 sessions running. R23 CLOSED; no R24 started; paper untouched; nothing pushed.
- 23:40 watcher and capguard stopped. §4y recorded in PROOF_NOTES.md. Building ROUND_BRANCH_R24_CERTIFICATE.json.
- 23:41 ROUND_BRANCH_R24_CERTIFICATE.json built from the 3 referee verdict.json files: sha256 5e7cab43a5f88ac993aba22def0f54fad058ba8c3dd2b0c9e2defae62847b55a. 107/113 claims accepted; the other 6 are UNVERIFIED (labelled conjectures/provenance only). R24 complete.
- 19:39 ROUND_BRANCH_R25_CERTIFICATE.json built from the 3 referee verdict.json files: sha256 50843797d497073c9d3583bca80a9f800ff7b44adf0569dbe24edec7ed16b83d. 116/122 claims accepted; the other 6 are UNVERIFIED (labelled open/provenance only). R25 complete.
- 22:08 ROUND_BRANCH_R26_CERTIFICATE.json built from the 2 referee verdict.json files: sha256 0eedd34db33fb01f662af881807385cc658985a7aaacaefe74e1c32cb8fdd963. 62/65 claims accepted; the other 3 are UNVERIFIED. R26 complete.
- 00:09 ROUND_BRANCH_R27_CERTIFICATE.json built from the 2 referee verdict.json files: sha256 59c8d16c9a2410138f8b7d9ad57403cbff95576bd58983e7c2f6c3d10abe30db. 66/69 claims accepted; the other 3 are UNVERIFIED (labelled open/history). R27 complete.
- R28 complete 2026-10-23 08:49 Asia/Shanghai: sha256 e17c42d95cd2a195962d8e45e50b067db58807121c43a2a2d9faf67b8f369dea (63/71 accepted).
- 2026-10-23 10:12 Asia/Shanghai: R29 COMPLETE. Certificate sha256 5d61db5b9d2f66b694674888cacb067b413cc8739806bdb58435cc977f7919a5. See PROOF_NOTES §4ad.
- PROOF_NOTES.md §4ae appended; ROUND_BRANCH_R30_CERTIFICATE.json sha256 `3f3b111a9bcb7a9b11831d55e6a0786a85ff67551e620375b6c82d7627239bbb`.
4 provers/4 referees: zk9 CORRECT, c33_42/c33_43/t6_irred CWF; 128/138 accepted. Z_9=RB_9=C_9 VERIFIED; R31.D42 (Δ≤7 at n=42), R31.D8 (Δ≤8 at n=43) ⇒ all R30.C33 forms excluded; star+spoke min-cut theorem. T_6/GEN_6 open (CE order ≥42). Cert ROUND_BRANCH_R31_CERTIFICATE.json sha fa0b2e09…8764; §4af. R32 running: t6_loss, t6_model, f42 (19:27), zk10 (20:04).
- 21:10 Asia/Shanghai: R32 CLOSED. Z₁₀ proved. Cert sha256 46340d86…. R33 four provers live (f42, kernel7, highdeg, zk11). Window to 01:00.
## R35 launched (2026-10-24 07:15 Asia/Shanghai) — Neil 继续 (t176u); cap=2
- Assembled `data/r35/` BRIEFING sha256 `59f0c1a0784f075058a9413a2a470d94db90a8dba2219fecec185acebc6a67b7` (PART I = EB6 residuals + E8-LOSS assembly; PART II = R34 briefing verbatim). Ctx includes R34 endpoint/tri_one referee packs, R33 highdeg, bs_strategy_review (ideas), R34 cert `8d29038b…`.
- Watch/capguard: `astra_r35v/watch.sh`, `astra_r35v/capguard.sh`. ncodex=2, `.codex_cap=2`. No paper edits, no push. Do **not** auto-start R36 on close; report and stop.
## R35 complete (2026-10-24 09:07 Asia/Shanghai)
- Verdicts copied to `data/r35/v_r35_*`. PROOF_NOTES.md §4aj. ROUND_BRANCH_R35_CERTIFICATE.json sha256 `132f7ecaba1663f20811bb8930e71f55ac481aa55003d638ca2ad3c0841eb0af`. Accepted 78/84 (UNVERIFIED = open/provenance). No paper edits, no push, no R36.
## R36 launched (2026-10-24 Asia/Shanghai) — Neil 继续 (t177u); cap=2
- Assembled `data/r36/` BRIEFING sha256 `e94181217d08bff68ce01f2377cc1506b6d69f99e06d7bd4173dc59fdd951c43` (PART I = 122 deg-7 P12 residuals → universal EB6 + TF GEN₆ double-pentagon residual; PART II = R35 briefing verbatim). Ctx includes R35 eb6_resid/tf_gen6 referee packs, residuals (`r35_single7_q12_remaining.json.gz`), R33 highdeg, R34 endpoint, R35 cert `132f7ecaba…`.
- Watch/capguard: `astra_r36v/watch.sh`, `astra_r36v/capguard.sh`. ncodex≤2, `.codex_cap=2`. No paper edits, no push. Do **not** auto-start R37 on close.
## R36 complete (2026-10-24 10:54 Asia/Shanghai)
- v_r36_eb6_d7p12: CORRECT_WITH_FIXES (39 C + 5 CWF + 6 UNV / 50). **All 122 deg-7 P12 residuals closed** (R36.E7-12; completes 1,585 with R35). Presentation/packaging fixes. **Universal EB6 still open** (endpoint deg 4–6).
- v_r36_tf_gen6: CORRECT_WITH_FIXES (35 C + 2 CWF + 3 UNV / 40). **TF mass for p≤12 when each edge in ≤3 pentagons** (extends R35 ≤1). Packaging/order-stat fixes. **Unrestricted TF GEN₆ still open** (residual: edge in ≥4 pentagons, endpoints deg≤6).
- Verdicts copied to `data/r36/v_r36_*`. PROOF_NOTES.md §4ak. ROUND_BRANCH_R36_CERTIFICATE.json sha256 `410e10c00646bc3cba711a601b826b83a2078c4fec0b474ab0340e2c91137b34`. Accepted 81/90 (UNVERIFIED = open/provenance). No paper edits, no push, no R37.
## R37 CLOSED (2026-10-24 ~12:58 CST)
Cert sha256 `27894d51a027f033ec005b94f6ff57f75c1a4bdb866eb926af207324b6683758`. Both referees CWF; 75/80 accepted. See PROOF_NOTES §4al / data/CONTINUOUS_LOG.md. Universal EB6 + unrestricted TF GEN₆ still open. Cap=2; watch stopped; parent may chain R38 before 18:00.
## R38 launched (2026-10-24 13:04 Asia/Shanghai) — Neil 继续 (t180u); cap=2
- Assembled `data/r38/` BRIEFING sha256 `160c4ca00524afe61ca368a5102aac8b92c16e6f86810c1c2ac6457db4590af7` (PART I = A37 / surviving deg-4 nine-contact / unrestricted TF GEN₆; PART II = R37 briefing verbatim). Ctx includes R37 eb6_d46/tf_gen6 referee packs, `r37/residuals/` (A37, r37_remaining.json.gz, index 2176), R37 cert `27894d51…`, PROOF_NOTES_4al.
- Watch/capguard: `astra_r38v/watch.sh`, `astra_r38v/capguard.sh`. `.codex_cap=2`. No paper edits, no push. Do **not** auto-start R39 on close; parent may chain before 18:00.
## R40 CLOSED (2026-10-24 18:15 CST) — window end (Neil t184u)
- Continuous proving window closed **18:00 Asia/Shanghai**. Cap remains `.codex_cap=2`. **No R41**. ncodex=0. `astra_r40v/capguard.stop` touched; watch/capguard exited.
  - `v_r40_a38_empty`: 29 CORRECT + 1 CWF + 3 UNVERIFIED / 33. Verdict sha256 `559623887c122a562cd62cef09d563f2b83dfa6509ed90fab8344bc9e3604e20`.
  - `v_r40_tf_dfree`: 22 CORRECT + 5 CWF + 4 UNVERIFIED / 31. Verdict sha256 `60d33f7f0b373cbfece4b727dbb5c55443b9c2c0adf0fd535ea459579632b05d`.
- Certificate: `ROUND_BRANCH_R40_CERTIFICATE.json` sha256 `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`.
- Packaging (t184u): RESULTS_TO_2026-10-24.md; paper update `paper/main.tex`; GitHub staging at `/workspace/graph133/github_publish/` (no push from this agent).
