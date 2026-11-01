# Results through 2026-11-01 (Asia/Shanghai) / 截至 2026-11-01（Asia/Shanghai）的结果整理

**English.** Packaging snapshot after continuous proving was stopped on 2026-11-01 (Asia/Shanghai), on Neil's instruction. This note organises sealed certificates. It does not prove REAL-133, and it does not prove any of the six universal production gates below. Only referee marks **CORRECT** / **CORRECT_WITH_FIXES** count as accepted, and only inside the partial scope the referee actually accepted. **UNVERIFIED** items are not theorems. An **INCORRECT** session is not accepted. A session that exited without a verdict is not accepted.

**中文。** 2026-11-01（Asia/Shanghai）按 Neil 的要求停止连续证明之后的整理快照。本说明只归档已封存证书。它不证明 REAL-133，也不证明下面六个全称生产门中的任何一个。仅裁判 **CORRECT** / **CORRECT_WITH_FIXES** 在其实际接受的部分范围内计为已接受。**UNVERIFIED** 不是定理。整段 **INCORRECT** 的会话不接受。没有裁决就退出的会话不接受。

The earlier public snapshot stopped at R40 / 2026-10-24 and is unchanged: `notes/RESULTS_TO_2026-10-24.md`. This file covers the later pack. That pack contains certificate JSON for **R46–R53 only**. It does not contain R41–R45 certificate files, and it does not contain an R54 certificate.

较早的公开快照停在 R40 / 2026-10-24，文件 `notes/RESULTS_TO_2026-10-24.md` 保持原样。本文件写其后的包。该包只有 **R46–R53** 的证书 JSON，没有 R41–R45 证书文件，也没有 R54 证书。

---

## 1. What this snapshot does not claim / 本快照明确不声称

The six universal production gates are still **open**:

1. Universal EB6 / empty A38 residual.
2. Unrestricted triangle-free GEN6.
3. Full TF-STAR-PRODUCTION6 (BALANCED-LOW-TREE6 singleton / G41).
4. Universal T6 / TRI-GEN6.
5. GEN_K / BOUNDARY-STAR / HYBRID-STAR universal production.
6. Funded noncyclic RAD leading to unconditional REAL-133.

六个全称生产门仍然**开放**：

1. 普遍 EB6 / 清空 A38 残差。
2. 无限制三角形无关 GEN6。
3. 完整 TF-STAR-PRODUCTION6（BALANCED-LOW-TREE6 的 singleton / G41）。
4. 普遍 T6 / TRI-GEN6。
5. GEN_K / BOUNDARY-STAR / HYBRID-STAR 的全称生产。
6. 已付费的非循环 RAD 推出无条件 REAL-133。

R49–R53 mostly add scaffolding that referees marked CORRECT_WITH_FIXES on partial statements. The list of six gates did not shrink, and the distance to a complete proof did not shrink. Scaffolding CWF is not a theorem of REAL-133.

R49–R53 主要是部分陈述上的脚手架 CWF。六门名单没有缩短，离完整证明的距离也没有缩短。脚手架 CWF 不是 REAL-133 的定理。

Last sealed round: **R53**. Certificate `certificates/ROUND_BRANCH_R53_CERTIFICATE.json`, sha256 `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`. Five sessions CORRECT_WITH_FIXES; the STAR session INCORRECT. No R54 certificate (R54 exited without a trusted verdict; this snapshot does not invent one).

最后封证轮：**R53**。证书 `certificates/ROUND_BRANCH_R53_CERTIFICATE.json`，sha256 `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`。五路 CORRECT_WITH_FIXES；STAR 路 INCORRECT。没有 R54 证书（R54 异常退出，没有可信裁决；本快照不编造证书）。

---

## 2. Pack gap before R46 / R46 之前的包缺口

R41–R45 JSON files are not in the 2026-11-01 pack, so this note does not summarise their claims and does not treat them as files in this repository.

The R46 certificate's own protocol text says it inherits an R45 certificate with sha256 `1b05993f54e0fb96942dd0ef9af0c2529a6e731ea11cc7d243a6d8a4a8136b33`, and that the R41 certificate was still deferred at the R46 seal. That hash is a pointer recorded inside R46. The R45 file is not in this snapshot, and this note does not audit it.

R41–R45 的 JSON 不在 2026-11-01 的包里，因此本说明不概述它们的声称，也不把它们当作本仓库中的文件。

R46 证书的协议文字自行记录：它继承 sha256 为 `1b05993f54e0fb96942dd0ef9af0c2529a6e731ea11cc7d243a6d8a4a8136b33` 的 R45 证书，并且在 R46 封存时 R41 证书仍被推迟。该哈希只是写在 R46 里面的指针。R45 文件不在本快照中，本说明不审核它。

---

## 3. Certificate table / 证书表（R46–R53）

Counts below are summed from each certificate's per-session `claim_breakdown`. They count claims inside refereed sessions. They are not a count of closed gates. Sessions with an empty breakdown are omitted from the numeric columns and named in the round notes.

下表数字是各证书里各会话 `claim_breakdown` 的合计，只统计已有裁判表的声称，不是已关闭的门的个数。没有 breakdown 的会话不计入数字列，在该轮说明里点名。

| Round | Sealed (CST) | Certificate sha256 | Refereed sessions | C | CWF | INC | UNV | Session verdicts |
|------:|:-------------|:-------------------|:------------------|----:|----:|----:|----:|:-----------------|
| R46 | 2026-10-28 18:36 | `18acca0d37550ed985cb9b5f8b205c16a22bdbc788d2084a52e940aba9daf030` | 6/6 | 175 | 20 | 0 | 28 | all six CWF |
| R47 | 2026-10-29 00:30 | `da0ef7adb88d62efd4cacac7281c80bfeead1c81e810b102e42e07253176aae7` | 3/6 | 78 | 4 | 0 | 22 | tf, star, t6 CWF; a38, genk, rad: claim failed, no referee |
| R48 | 2026-10-30 19:30 | `1ebbc46c67c63a1ecc4fad07a95aa325cc51687c077b75109839072ef7d8dd4e` | 1/6 | 28 | 3 | 1 | 6 | star CWF but one claim INCORRECT; a38 and rad: no referee; tf, t6, genk: referee failed, no verdict |
| R49 | 2026-10-31 03:05 | `e95aabd77cdf22b8669cd27c8943e8e51ec93da5740255c7f8c363f4af41c44b` | 2/6 | 49 | 4 | 0 | 13 | tf and rad CWF; a38, star, t6, genk: failed claim, no report |
| R50 | 2026-10-31 04:38 | `6a1c7aece7bc53906548cfb9f896b9ea32480f51d1edb9de46acbe693824b111` | 6/6 | 197 | 13 | 0 | 20 | all six CWF |
| R51 | 2026-10-31 06:28 | `aebe0c00de6fd8ed0059280a2ac6d9c56e6c64355487912d0fde5a5be04999f7` | 6/6 | 183 | 10 | 0 | 22 | all six CWF; last STAR session accepted as CWF |
| R52 | 2026-10-31 08:34 | `8383d17dac2d9f23995b066b4a9e82a6b977602ee9451bab90fd810161ee171a` | 6/6 | 155 | 12 | 3 | 18 | five CWF; star INCORRECT |
| R53 | 2026-10-31 16:39 | `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd` | 6/6 | 56 | 12 | 0 | 8 | five CWF; star INCORRECT; four sessions have no claim table |

Check a file with `cd certificates && sha256sum -c ROUND_BRANCH_R53_CERTIFICATE.sha256`. Sidecars `ROUND_BRANCH_R{46..53}_CERTIFICATE.sha256` and `.json.sha256` are the `sha256sum` lines for those JSON files.

可用 `cd certificates && sha256sum -c ROUND_BRANCH_R53_CERTIFICATE.sha256` 核对。`ROUND_BRANCH_R{46..53}_CERTIFICATE.sha256` 与 `.json.sha256` 都是对应 JSON 的 `sha256sum` 行。

---

## 4. Accepted scaffolding versus open gates / 已接受的脚手架与仍开放的门

Every round below still lists all six gates as open in its certificate `open` field. "Accepted" means partial CWF scaffolding only.

下面每一轮的证书 `open` 字段仍把六门全部列为开放。「已接受」只表示部分范围上的 CWF 脚手架。

### R46 — `18acca0d37550ed985cb9b5f8b205c16a22bdbc788d2084a52e940aba9daf030`

- **Accepted as CWF scaffolding:** all six sessions (`r46_a38_univ`, `r46_tf_gen6`, `r46_star_prod`, `r46_t6_univ`, `r46_genk_prod`, `r46_rad_real133`). The stored headlines give claim counts and do not state a universal theorem. This note does not promote individual claim identifiers to theorems.
- **Not accepted / still open:** all six universal gates, in the certificate's own `open` list. UNVERIFIED claims (28 in the summed table) are not theorems.
- **中文：** 六路都是 CWF 脚手架。证书标题只给了声称计数，没有全称定理。本说明不把单条声称编号提升为定理。六门仍开放。28 条 UNVERIFIED 不是定理。

### R47 — `da0ef7adb88d62efd4cacac7281c80bfeead1c81e810b102e42e07253176aae7`

- **Accepted as CWF scaffolding:** `r47_tf_gen6` (18C+1CWF+7UNV), `r47_star_prod` (26C+1CWF+6UNV), `r47_t6_univ` (34C+2CWF+9UNV). The certificate calls these partial production / partial domains / partial cells.
- **Not accepted:** `r47_a38_univ`, `r47_genk_prod`, `r47_rad_real133` exited with failed claims and no referee. Universal EB6, GEN_K/HYBRID, and funded RAD stay open for that reason, and the three CWF sessions also leave their own universal targets open.
- **中文：** 仅 tf、star、t6 为部分 CWF。a38、genk、rad 声称失败且没有裁判。三门因此没有新的接受结果；已接受的三路自己的全称目标也仍开放。

### R48 — `1ebbc46c67c63a1ecc4fad07a95aa325cc51687c077b75109839072ef7d8dd4e`

- **Accepted as CWF scaffolding:** `r48_star_prod` only, and only the claims the referee did not mark INCORRECT. The session overall is CWF, with breakdown 28C+3CWF+1 INC+6UNV. The certificate calls it partial production. The one INCORRECT claim is not accepted.
- **Not accepted:** `r48_a38_univ` and `r48_rad_real133` have no referee. `r48_tf_gen6`, `r48_t6_univ`, and `r48_genk_prod` have no verdict. Full TF-STAR-PRODUCTION6 remains open.
- **中文：** 只有 star 路整体 CWF，且其中 1 条声称 INCORRECT，那一条不接受。证书称之为部分生产。a38 与 rad 无裁判；tf、t6、genk 无裁决。完整 STAR 生产门仍开放。

### R49 — `e95aabd77cdf22b8669cd27c8943e8e51ec93da5740255c7f8c363f4af41c44b`

- **Accepted as CWF scaffolding:** `r49_tf_gen6` (22C+2CWF+6UNV). The certificate headline says the partial production theorems are correct relative to the accepted context, and that unrestricted targets remain unverified. `r49_rad_real133` (27C+2CWF+7UNV) is CWF at a partial scope; the stored headline says accepted context is background. Universal RAD and unconditional REAL-133 stay open in the certificate `open` line.
- **Not accepted:** `r49_a38_univ`, `r49_star_prod`, `r49_t6_univ`, and `r49_genk_prod` failed with no report. The certificate says prior R48 star CWF and prior R47 t6 CWF are retained as background. That is a pointer to earlier partial certificates, not a new proof of those gates.
- **中文：** tf 与 rad 为部分 CWF。证书写明无限制目标仍未核验，普遍 RAD 与无条件 REAL-133 仍开放。a38、star、t6、genk 没有报告。证书把先前的 R48 star CWF 和 R47 t6 CWF 留作背景，这不是这些门的新证明。

### R50 — `6a1c7aece7bc53906548cfb9f896b9ea32480f51d1edb9de46acbe693824b111`

- **Accepted as CWF scaffolding:** all six sessions, each explicitly partial. Stored headlines that are complete sentences: a38, the partial theorem and its finite premises verify, and explicitly conjectured universal statements remain unverified; tf, partial structural production only, unrestricted TF GEN6 and REAL-133 remain unverified; star, partial production theorems, full STAR production and REAL-133 remain unverified. t6, genk, and rad are likewise CWF with universal targets left unverified.
- **Not accepted:** the six universal gates (UNVERIFIED lines in the certificate).
- **中文：** 六路都是部分 CWF。证书写明全称猜想、无限制 TF GEN6、完整 STAR 与 REAL-133 仍未核验。六门仍开放。

### R51 — `aebe0c00de6fd8ed0059280a2ac6d9c56e6c64355487912d0fde5a5be04999f7`

- **Accepted as CWF scaffolding:** all six sessions, partial. The tf headline says the stated mathematical partial claims were verified relative to accepted context, packaging needed correction, and unrestricted assertions remain open. The certificate `open` lines leave UNIVERSAL_EB6, unrestricted TF GEN6, full STAR (O1–O5), universal T6, GEN_K targets, and unconditional REAL-133 unverified.
- **STAR baseline:** this is the last STAR session whose overall verdict is CWF. R52 and R53 STAR sessions are INCORRECT and are not the baseline.
- **中文：** 六路部分 CWF。无限制与全称目标在证书里仍是 UNVERIFIED。STAR 的最后一次整体 CWF 是这一轮。R52 与 R53 的 STAR 为 INCORRECT，不能当作基线。

### R52 — `8383d17dac2d9f23995b066b4a9e82a6b977602ee9451bab90fd810161ee171a`

- **Accepted as CWF scaffolding:** `r52_a38_univ` (26C+3CWF+3UNV), `r52_tf_gen6` (28C+2CWF+3UNV), `r52_t6_univ` (30C+1CWF+4UNV), `r52_genk_prod` (12C+2CWF+3UNV), `r52_rad_real133` (30C+1CWF+3UNV). The certificate describes these as partial, and it leaves the universal targets unverified. Delivery and wording fixes do not enlarge the scope.
- **Not accepted:** `r52_star_prod` overall INCORRECT (29C+3 INC+3CWF+2UNV). The certificate says BALANCED-LOW-TREE6 is false as stated because singleton low trees are admitted, and that G41 is an explicit positive irreducible counterexample to that statement. The prior R51 star CWF is the retained baseline. The three INCORRECT claims are not theorems. Full TF-STAR-PRODUCTION6 stays open.
- **中文：** 五路部分 CWF，全称目标仍未核验。star 整体 INCORRECT：证书写明 BALANCED-LOW-TREE6 对 singleton 低树不成立，G41 是该陈述的显式反例。STAR 基线仍是 R51 的 CWF。完整 STAR 门仍开放。

### R53 — `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`

- **Accepted as CWF scaffolding (partial only):**
  - `r53_a38_univ` (17C+3CWF+3UNV). The stored headline says the partial metric-core theorem is correct after local wording and delivery fixes, and that the universal EB6 and REAL-133 obligations remain open.
  - `r53_tf_gen6`. The stored headline says substantive partial theorems and computational certificates verify, with delivery-reference fixes. It does not say unrestricted TF GEN6 is proved. No claim table was stored.
  - `r53_t6_univ` (39C+9CWF+5UNV). The stored headline says the positive-source partial theorem and the mathematical certificates pass, and that some subsidiary statements that omit positivity are literally false and need fixes. Universal T6 stays open.
  - `r53_genk_prod` and `r53_rad_real133`. The stored headlines limit both to stated partial scopes, with delivery or stress-counter fixes. No claim tables were stored. Universal GEN_K/HYBRID and unconditional REAL-133 stay open.
- **Not accepted:** `r53_star_prod` overall INCORRECT. The stored headline says the stated BALANCED-LOW-TREE6 theorem is false because the class admits singleton trees. No claim table was stored. The STAR baseline remains the R51 CWF session, not R52 or R53.
- **Seal limitation, as written in the certificate:** tracks whose on-disk `verdict.json` was missing at seal time were reconstructed from the final OVERALL line in the referee log. The certificate note says `all_six_accepted=false`, and that the six universal gates remain open (partial CWF only).
- **中文：** 五路部分 CWF。a38 是局部度量核陈述，普遍 EB6 与 REAL-133 仍开放。tf、genk、rad 没有声称表，标题把范围限制在部分陈述。t6 是正源的部分定理，普遍 T6 仍开放。star 为 INCORRECT，singleton 缺陷仍在。证书写明缺失的 `verdict.json` 由裁判日志的最终 OVERALL 重建。`all_six_accepted=false`。

---

## 5. Distance note (not a theorem) / 距离评估（不是定理）

File: `notes/DISTANCE_ASSESS_R54.md`.

sha256: `ce156ef7fe942b391cd41fd88e29db404cc660a6b7cd2070968acce4f69f4dde`.

This repository stores that assess file unchanged. The file labels itself. Its opening lines say it is a strategy assessment, not a proof attempt, not a proof certificate, and not a new research round.

本仓库原样存放该评估文件。文件自己标明：它是策略评估，不是证明尝试，不是证明证书，也不是新一轮研究任务。

Quoted conclusion (Chinese, from that file):

> **OPEN — 总判断。** 完整 REAL-133 仍是研究开放问题。现有材料不足以支持“再运行若干轮即可完成”的判断。缺少的是覆盖全部剩余输入的结构强迫定理，而不只是整理或修补现有证明。

Close English rendering of that paragraph, for readers of this note: the overall judgment is OPEN. Complete REAL-133 is still research-open. The existing material does not support the claim that running some further automatic rounds would finish the proof. What is missing is a structural forcing theorem that covers every remaining input, not a cleanup of proofs already written.

The same note's proposals to Neil, quoted here only as proposals:

> **PROPOSAL — 保持暂停，先重设计。** 当前不值得恢复连续自动证明链；完整 REAL-133 仍应登记为 **OPEN / research-open**。
>
> **PROPOSAL — 若继续，只先攻 EB6/A38。**
>
> **PROPOSAL — R55 自动轮现在不值得启动。**

The assess manifest's one-line conclusion is: REAL-133 remains research-open; pause the automatic chain; if work continues, redesign around universal EB6/A38 forcing; do not start an automatic R55 round now. CLOSEST, in that note, means a relative choice of which open gate to attack first. It is not a promise that the gate is nearly proved.

同一份说明给 Neil 的建议是：保持暂停；若以后继续，先攻 EB6/A38 的整类强迫；现在不启动 R55 自动轮。其中的 CLOSEST 只是相对优先的选择，不是「即将证完」的承诺。

---

## 6. Paper scope / 论文收录范围

- Theorem G in `paper/main.tex` remains the R35–R40 partial mass statement. The 2026-11-01 edit does not add R46–R53 claims to that theorem.
- The paper records that R46–R53 certificates exist under `certificates/`, that they are scaffolding, and that the six gates and REAL-133 are open. See the 1 November 2026 addendum.
- Authors in the public draft: Xingchen Wang (first, name only), Neil Xu (second). Neil Xu's email is withheld.

- 论文中的 Theorem G 仍是 R35–R40 的部分质量陈述。2026-11-01 的修改没有把 R46–R53 的声称写进该定理。
- 论文只记录 `certificates/` 下存在 R46–R53 脚手架证书，并且六门与 REAL-133 仍开放。见 2026-11-01 的附记。
- 公开草稿作者：Xingchen Wang（第一，仅姓名），Neil Xu（第二）。Neil Xu 的邮箱不公开。
