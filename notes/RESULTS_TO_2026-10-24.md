# Results through 2026-10-24 18:00 Asia/Shanghai / 截至 2026-10-24 18:00（Asia/Shanghai）的结果整理

**English.** Packaging snapshot after the continuous proving window closed at 18:00 Asia/Shanghai on 2026-10-24 (Neil t184u). Only referee verdicts **CORRECT** / **CORRECT_WITH_FIXES** are treated as accepted. UNVERIFIED claims are open or provenance and are **not** theorems.

**中文。** 连续证明窗口于 2026-10-24 18:00（Asia/Shanghai）关闭后的整理快照（Neil t184u）。仅裁判 **CORRECT** / **CORRECT_WITH_FIXES** 计为已接受；UNVERIFIED 为开放项或过程叙述，**不**作为定理。

Source certificates: `work/round_branch/ROUND_BRANCH_R{35..40}_CERTIFICATE.json` (built from `astra_r*v/*/scratch/verdict.json` only).

---

## 1. Continuous window timeline / 连续窗口时间线（R35→R40）

| Round | Closed (CST) | Sessions | Overall | Accepted (C+CWF) / total |
|------:|:-------------|:---------|:--------|-------------------------:|
| R35 | 2026-10-24 09:07 CST | `r35_eb6_resid + r35_tf_gen6` | CWF+CWF | 78/84 |
| R36 | 2026-10-24 10:54 CST | `r36_eb6_d7p12 + r36_tf_gen6` | CWF+CWF | 81/90 |
| R37 | 2026-10-24 12:59 CST | `r37_eb6_d46 + r37_tf_gen6` | CWF+CWF | 75/80 |
| R38 | 2026-10-24 14:42 CST | `r38_eb6_a37 + r38_tf_gen6` | CWF+CWF | 71/77 |
| R39 | 2026-10-24 16:32 CST | `r39_a38_kill + r39_tf_drop` | CWF+CWF | 60/65 |
| R40 | 2026-10-24 18:12 CST | `r40_a38_empty + r40_tf_dfree` | CWF+CWF | 57/64 |

Protocol throughout: Astra prover → separate fresh Astra referee (`mkver.sh`); cap `.codex_cap=2`; structural redirect from t183u (no contact-catalog sweeping as main claim). Window end: no further proof rounds; packaging only.

协议全程：Astra 证明者 → 独立新鲜 Astra 裁判；并发上限 2；t183u 结构优先（不以接触目录扫荡作主声称）。窗口结束后不再开证明轮，仅整理。

---

## 2. Certificate SHA-256 and headlines / 证书哈希与已接受要点

### R35 — `132f7ecaba1663f20811bb8930e71f55ac481aa55003d638ca2ad3c0841eb0af`
- Created: 2026-10-24 09:07 CST
- **Headline verified (CORRECT/CWF):**
  - r35_eb6_resid (CWF, 38C+1CWF+3UNV): All P11 cases of EB6 CLOSED without endpoint-degree cap (single7/6/5 + shared + separate). Full P12 common-two-contact-neighbor family CLOSED (R35.A12-full). Degree-seven P12: 1,463 certified closures / 122 unresolved (51 six-contact + 71 seven-contact). Packaging link fixes only. Universal EB6 still open at residual P12.
  - r35_tf_gen6 (CWF, 37C+2CWF+3UNV): Triangle-free strongly C4-free: S(G)<=6|V| for p<=11 (R35.P11/M11/CORE); also for p<=12 when every edge is in at most one pentagon (R35.PLANE / C1-GEN6). Written R35.GIRTH7 (K=6) and R35.GIRTH8 (general K). Doc count fix (omission allocations 1164+3). Unrestricted triangle-free GEN6 still open (residual: p=12 with an edge in two pentagons).
- **Open (from certificate):**
  - Universal EB6 (endpoint-bounded deletion for all longest-path endpoints deg<=7 at P12 residual) still open; 122 unresolved deg-7 P12 patterns remain
  - Unrestricted triangle-free GEN6 still open (assembly residual: p=12 with an edge shared by two pentagons); T6 / GEN6 inclusive; F42 (CE>=42)
  - Z_K (K>=12), T10, GEN10, RAD, REAL-133

### R36 — `410e10c00646bc3cba711a601b826b83a2078c4fec0b474ab0340e2c91137b34`
- Created: 2026-10-24 10:54 CST
- **Headline verified (CORRECT/CWF):**
  - r36_eb6_d7p12 (CWF, 39C+5CWF+6UNV): All 122 degree-seven P12 residuals CLOSED (unrestricted interior degrees); with R35.E7-12 this completes all 1,585 deg-7 P12 contact systems (R36.E7-12). Data-only replay: 6,658 states / 2,779,236 path witnesses. Presentation/packaging fixes only. Universal EB6 still open (endpoint degrees 4–6 remain).
  - r36_tf_gen6 (CWF, 35C+2CWF+3UNV): Triangle-free strongly C4-free: S(G)<=6|V| when p<=12 and every edge lies in at most THREE pentagons (extends R35 <=1-pentagon bound), with exact min-degree-four classification and weighted deletion. All 122 deg-7 closures frozen/locally verified. Presentation/packaging fixes only. Unrestricted TF GEN6 still open (residual: endpoint deg<=6 and an edge in >=4 pentagons).
- **Open (from certificate):**
  - Universal EB6 still open: longest-path endpoint degrees 4–6 remain after deg-7 P12 closure
  - Unrestricted triangle-free GEN6 still open (residual: p=12 with an edge in at least four pentagons and longest-path endpoints deg<=6); T6 / GEN6 inclusive; F42 (CE>=42)
  - Z_K (K>=12), T10, GEN10, RAD, REAL-133

### R37 — `27894d51a027f033ec005b94f6ff57f75c1a4bdb866eb926af207324b6683758`
- Created: 2026-10-24 12:59 CST
- **Headline verified (CORRECT/CWF):**
  - r37_eb6_d46 (CWF, 37C+2CWF+2UNV): Sharp S≤6n−28 for triangle-free strongly C4-free with p≤11,n≥8 (R37.M11-28) + P12-transversal closures; all 301 deg-6 nine-contact P12 systems closed (R37.E6-9); all 63 deg-5 nine-contact under global endpoint cap five (R37.E5-9); one explicit deg-4 family under endpoint cap four (R37.E4-six). 713-root data replay. Presentation/packaging fixes only. Universal EB6 still open (exact remaining avoiding class A37 / surviving deg-4 nine-contact).
  - r37_tf_gen6 (CWF, 34C+2CWF+3UNV): Triangle-free strongly C4-free: S(G)≤6|V| when p≤12 provided all pentagons through any edge of multiplicity ≥4 share a common adjacent edge (multiplicity unbounded; B-CLASSIFICATION / B-MASS / cover). 145 new completion roots + 28 minimal induced B-obstructions verified. Scope/cover wording + packaging fixes. Unrestricted TF GEN6 still open (residual without the common-adjacent-edge spine hypothesis).
- **Open (from certificate):**
  - Universal EB6 still open: exact remaining avoiding class A37 / surviving degree-four nine-contact configurations (endpoint degrees 4–6 not fully closed)
  - Unrestricted triangle-free GEN6 still open (residual without common-adjacent-edge condition on ≥4-pentagon edges; endpoints deg≤6); T6 / GEN6 inclusive; F42 (CE≥42)
  - Z_K (K≥12), T10, GEN10, RAD, REAL-133

### R38 — `0f199e4ec5681d92467b04bd0747029235edba3341ef7b3f3f13feeec2ee2bd5`
- Created: 2026-10-24 14:42 CST
- **Headline verified (CORRECT/CWF):**
  - r38_eb6_a37 (CWF, 30C+1CWF+3UNV): R38.M4 entire cap-four branch — all 2177 deg-4 P12 endpoint systems including survivor 2176; R38.M4-MASS; R38.E6-8 all 1140 deg-6 eight-contact (+ accepted E6-9); R38.E5-8 all 494 deg-5 eight-contact under endpoint cap five (+ accepted E5-9); 154 additional deg-6 seven-return systems (partial); exact remaining avoiding class A38. Replay 1,668,068 states / 57,501,752 path witnesses. Packaging-link fixes only. Universal EB6 still open (lower-contact deg-5/6 residuals).
  - r38_tf_gen6 (CWF, 39C+1CWF+3UNV): Triangle-free strongly C4-free: S≤6n for p≤12 when every ≥4-pentagon edge has a common adjacent edge, OR disjoint pentagon interiors, OR exactly four pentagons inducing Petersen (SM/SMP classification); for n≥14, S≤6n−38. Exactly 22 minimal SM + 21 minimal SMP obstructions; E14/E16 edge bounds; DELETE19/COVER19. Packaging-link fixes. Unrestricted TF GEN6 still open.
- **Open (from certificate):**
  - Universal EB6 still open: lower-contact degree-five/six residuals (cap5/cap6 incomplete families); exact remaining avoiding class A38 is nonempty in statement
  - Unrestricted triangle-free GEN6 still open; T6 / GEN6 inclusive; F42 (CE≥42)
  - Z_K (K≥12), T10, GEN10, RAD, REAL-133

### R39 — `dc1224bcc8843e6fdbcf285e68d036e0945165acb585b1c8f65c5bec5bb34477`
- Created: 2026-10-24 16:32 CST
- **Headline verified (CORRECT/CWF):**
  - r39_a38_kill (CWF, 34C+3CWF+1UNV): ROOT7; NO-CUT; PAIR; H28 uncapped cheap deletion (sharp via C106 with 29 high verts); PENALTY/C4-D28; ENDPOINT-REDUCTION; H31-EB (≤31 deg≥5 ⇒ S≤6n for p≤12 TF strong-C4-free) + H35-CAP5 (≤35 under P12 endpoint cap 5); H31-MASS / H35-CAP5-MASS; C106 full induced criticality; fixed-cap transfer K≥6; conditional budget-transfer + A39 sufficient restriction (retains all seven A38 conditions). Packaging/hash/display fixes only. A38 NOT emptied; universal EB6 still open.
  - r39_tf_drop (CWF, 20C+3CWF+4UNV): Explicit 18-vertex D/Robertson frame: cycle-contact forces outside deg≤3; induced R is a component at δ≥4; induced D forces component=R; sharp five-vertex cheap deletion on that domain; positive graphs reduce to positive induced-D-free; all 33 mandatory controls; fixed-cap transfer K≥6; residual deletion equivalence (conditional) to unrestricted TF GEN6. Connectedness fix on D-free corollary; graph6/link packaging fixes. Unrestricted TF GEN6 still open; SM/SMP hypotheses not fully dropped to unrestricted.
- **Open (from certificate):**
  - A38 not emptied; universal EB6 still open (A39 is a sufficient restriction retaining A38's seven conditions; H31/H35 are high-vertex mass bounds, not universal EB6)
  - Unrestricted triangle-free GEN6 still open (SM/SMP / common-adjacent / Petersen-4 style hyps not eliminated; Robertson/D-free residual remains)
  - T6 / triangle-inclusive GEN6; F42 (CE≥42); general GEN_K / RAD / REAL-133; rank-1/rank-2 existence lemmas proposed but unproved

### R40 — `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`
- Created: 2026-10-24 18:12 CST
- **Headline verified (CORRECT/CWF):**
  - r40_a38_empty (CWF, 29C+1CWF+3UNV): MIN4-P11 (δ≥4 ⇒ induced P11 / p≤10 is 3-degenerate); C4-D36 (p≤12, P12-endpoint cap4, n≥14 ⇒ S≤6n−36); END18 weight≤18 endpoint reduction; H32-MASS (≤32 high verts ⇒ S≤6n, no interior degree bound) + H36-CAP5-MASS (≤36 under P12 endpoint cap5); SUPPORT-COVER / FOREST-EXACT / COMPLEMENT-EXACT / ORDER-SUPPORT identities; BOUNDARY necessary rows at h33/cap6 and h37/cap5 (ε=2; realizability not claimed); explicit C112 (n=112,e=337,ε=2,h=29,η=6) induced-critical with 112 rooted P13s; fixed-cap transfer K≥6; residual-reduction equivalence (conditional) of cheap deletion on residual R40 to universal EB6 and unrestricted TF GEN6. Packaging/archive-size fixes only. A38 NOT emptied; universal EB6 still open.
  - r40_tf_dfree (CWF, 22C+5CWF+4UNV): Robertson one-vertex puncture classification (connected δ≥4 ⇒ R / X21 / X22 / X23); outside-contact degree bounds; sharp seven-vertex cheap deletion whenever a puncture is induced (sharp on X22); every positive capped graph reduces to a positive puncture-free induced subgraph; X22 exact p=12, ε6=−38, min cheap size 7; residual equivalence (conditional) of cheap deletion on the full residual to unrestricted TF GEN6; fixed-cap transfer + conditional GEN interfaces. Ordinary-path cut convention / packaging / unused-diagnostic fixes. Unrestricted TF GEN6 still open; ranked existence lemmas unproved.
- **Open (from certificate):**
  - A38 not emptied; universal EB6 still open (H32/H36 are high-vertex mass bounds; residual R40 cheap-deletion equivalence is conditional, not emptiness)
  - Unrestricted triangle-free GEN6 still open (puncture residual discharged structurally; remaining residual mass bound unproved; ranked endpoint/SMP existence lemmas unproved)
  - T6 / triangle-inclusive GEN6; F42 (CE≤42); general GEN_K / RAD / REAL-133

---

## 3. Still open / 仍开放项（截至 R40）

Aggregated from R40 `open` (and consistent with R35–R39):

1. **A38 not emptied; universal EB6 still open.** H31/H32/H35/H36 are high-vertex mass bounds; residual cheap-deletion equivalences are conditional, not emptiness of A38.
2. **Unrestricted triangle-free GEN₆ still open.** Puncture / Robertson–D residual reduced structurally; remaining residual mass bound and ranked existence lemmas unproved.
3. **T₆ / triangle-inclusive GEN₆; F42 (CE bound); general GEN_K / RAD / REAL-133.**

中文对应：
1. **A38 未清空；普遍 EB6 仍开放。** H31/H32/H35/H36 为高点质量界；残差廉价删除等价是条件性的，不是 A38 空类。
2. **无限制三角形无关 GEN₆ 仍开放。** 穿刺 / Robertson–D 残差已结构性约化；剩余残差质量界与 ranked 存在引理未证。
3. **T₆ / 含三角形 GEN₆；F42；一般 GEN_K / RAD / REAL-133。**

---

## 4. Scope for paper and public repo / 论文与仓库收录范围

- **Default inclusion:** only claims with referee verdict CORRECT or CORRECT_WITH_FIXES.
- **Excluded as theorems:** UNVERIFIED (open conjectures, ranked existence proposals, private execution-history narratives).
- **Conditional lemmas:** stated with explicit hypotheses (e.g. residual cheap-deletion ⇒ EB6 / TF GEN₆ equivalences; fixed-cap transfer at path cap 12 only).
- Paper draft: `/workspace/graph133/paper/main.tex` (+ PDF). Public staging: `/workspace/graph133/github_publish/` for CloudAgent push to `neardws/graph-conjecture-133` (this agent does not push).

- **默认收录：** 仅 CORRECT / CORRECT_WITH_FIXES。
- **不作定理：** UNVERIFIED。
- **条件引理：** 写清假设。
- 论文草稿与 GitHub staging 见上；真正 push 由父代理 CloudAgent 执行。

---

## 5. R40 session metadata / R40 会话元数据

- **r40_a38_empty**: prover `astra_r40/r40_a38_empty` sid `01a16d0c-b9b1-7df2-88a7-379fc0557529`; referee `astra_r40v/v_r40_a38_empty` sid `01a16d48-edf7-7c93-8c7d-caef74efa904`; overall `CORRECT_WITH_FIXES`; breakdown `{'CORRECT': 29, 'CORRECT_WITH_FIXES': 1, 'UNVERIFIED': 3}`; verdict sha256 `559623887c122a562cd62cef09d563f2b83dfa6509ed90fab8344bc9e3604e20`.
- **r40_tf_dfree**: prover `astra_r40/r40_tf_dfree` sid `01a16d0c-e850-7942-af55-f4fa4d208527`; referee `astra_r40v/v_r40_tf_dfree` sid `01a16d40-0ec7-7730-a90f-b7cf9838d8ae`; overall `CORRECT_WITH_FIXES`; breakdown `{'CORRECT': 22, 'CORRECT_WITH_FIXES': 5, 'UNVERIFIED': 4}`; verdict sha256 `60d33f7f0b373cbfece4b727dbb5c55443b9c2c0adf0fd535ea459579632b05d`.

Certificate file sha256: `71819fcdd5681a6cb5413a6ff326d1d6d651ebd5f2e316886d8f4abc0de9e4f7`.

