# REAL-133：R53 封存、R54 暂停后的整体距离评估

日期：2026-11-01。对象：Neil。性质：策略评估，不是证明尝试、证明证书或新一轮研究任务。

**OPEN — 总判断。** 完整 REAL-133 仍是研究开放问题。现有材料不足以支持“再运行若干轮即可完成”的判断。缺少的是覆盖全部剩余输入的结构强迫定理，而不只是整理或修补现有证明。

**PROVED — 本文的证据口径。** 本文接受给定封存结果及其 CWF 修正，不重新裁决。`PROVED` 表示封存范围内已成立的结果或条件归约；不表示本文新证明了它。`COMPUTED` 区分本次核对与前轮 referee 已报告的计算。`CONJECTURED` 表示未证明的数学候选或主观距离判断。`PROPOSAL` 表示建议。`OPEN` 表示尚缺的结果。排名不是成功概率或时间上界。

**COMPUTED — 本次来源核对。** 优先读取 `ctx`。R53 证书 SHA-256 为 `b90cc797e755cb8cf849937c20ad1576ea551a7b0ec3b780676c3e84d81b6ecd`，与指定值一致。R53 是五个 CWF、STAR INCORRECT；STAR 的有效基线为 R51。R54 退出、无可信裁决及无证书的状态采用用户给定记录。本次未运行前轮 producer、referee 或图枚举程序。

## 1) 六个通用门的距离排名

**OPEN — 六门状态。** 以下六门均未关闭。CLOSEST 只表示相对优先尝试；仍可能需要新的数学思想。

| 通用门 | 距离判断 | 一句话依据 |
|---|---|---|
| 1. Universal EB6 / A38 | **CONJECTURED — CLOSEST** | **OPEN：** 固定在路径阶 11/12 的明确删除目标，但 R53 的终端四分支 metric-core 定理不保证核心存在，完整 A38 仍可能避开全部已付费核心。 |
| 2. Unrestricted TF GEN6 | **CONJECTURED — MID** | **OPEN：** R53 已处理若干完整 connected-core 源类，却未从整个 residual 强迫独立外邻域、唯一父点及颜色/原始度预算；SM/SMP、PRIVATE/COLOR/LEAF 都不能提供该全域步骤。 |
| 3. Full TF-STAR-PRODUCTION6 | **CONJECTURED — MID** | **OPEN：** singleton 缺陷可明确定位，但排除 singleton 后仍有 empty-low、isolated-low、dense-contact 和所有根均失败的 R51 加权余类。 |
| 4. Universal T6 / TRI-GEN6 | **CONJECTURED — MID** | **OPEN：** R53 关闭 binary nonclique-return 的若干 cactus 类，尚未控制高重数 witness、未付费 K4 load、小 incidence mass、高边界度及 noncactus 核。 |
| 5. GEN_K / BOUNDARY-STAR / HYBRID | **CONJECTURED — FURTHEST** | **OPEN：** 当前 thin-star-cut 的 P13 机制仍主要作用于 cap 12；一般 K 的原生 cap、任意边界几何和全部高参数归纳义务尚未解决。 |
| 6. Funded noncyclic RAD → REAL-133 | **CONJECTURED — FURTHEST** | **OPEN：** R53 的 block/entry 付款仍依赖 BN 等源条件，任意深度的非循环核心、wide component 与全部 shortest-entry 失败情形没有通用付款。 |

**PROVED — 依赖关系，不能把六门当作六个连续关卡。** 按封存装配，下面是一条充分路线：

\[
(\mathrm{EB6}\ \lor\ \mathrm{TF\ GEN6})
\ \land\ T_6
\ \land\ \text{完整高参数 GEN 归纳输入}
\ \land\ \mathrm{RAD}
\ \Longrightarrow\ \mathrm{REAL133}.
\]

**PROVED — 路线的含义。** EB6 与 unrestricted TF GEN6 是六级的替代入口。STAR 是实现 TF 生产的候选方法，可被完整六级定理绕过；它不是此装配中额外必需的独立前提。高参数块和 RAD 块各包含无界参数族，不能把“四块”理解为四个局部修补。[依据：R45 装配 §4、referee；R53 RAD §4。](../ctx/r45/real133_asm/PROOF_REPORT.md)

## 2) 完整证明仍缺哪些具体成分

**PROVED — 统一记号。** 路径阶数按顶点数。strong C4-free 排除普通四圈，包括带弦四圈。令 `S(G)=2e(G)−3T(G)`，`ε_K(G)=S(G)−K|G|`。非空 `U` 为 K-cheap，指 `F_{K,G}(U)=S(G)−S(G−U)−K|U|≤0`。正剩余量输入经该删除仍为正。模型必须保留全部袋间邻接；TF 模型还须保持无三角形。

### 2.1 EB6 / A38：需要一个覆盖全余类的删除论证

**PROVED — 已有工具。** 端点归约、旧 cut/exchange/closure 排除，以及 R51–R53 的若干 ambient-isometric dominating core 付款，均可按其原范围使用。R53 的终端 intrinsic-degree-four 分支类能直接产出原图 cheap set。

**OPEN — 真正缺的主引理。** 对每个 EB6 输入——连通、TF、strong C4-free，`p∈{11,12}`、最小度至少四、每条全局最长诱导路的每个端点实际度至多七——产出一个非空 6-cheap set。等价的研究目标是处理带全部继承限制的 R53 A38 余类；不能只处理一个选定核心。

**PROPOSAL — 首选结构攻击。** 以“完整 A38 输入 + 无 cheap set”为反设，证明一次全局的路径上界/删除预算矛盾。可选中间目标是：强迫已封存的 endpoint-reducing 或 mixed-tree 删除，或推出原图 cheap set；不能先假设存在 subcubic、unicyclic 或终端四分支核心。旧的 `w(X)≤18` 且余图阶至少十四，是已有端点删除接口的一个明确预算，不是已证明必然出现的集合。

**OPEN — 必须跨过的障碍。** 有些候选可能没有上述任何核心；有核心时，也可能有昂贵高实际度分支、相邻分支、非终端四分支、更多短圈或多圈结构。最长路端点有界不等于内部实际度有界。R53 对指定源类的改进没有消除这些情形。

**PROVED — “kill A38”的准确含义。** 对整个形式余类证明 cheap-set 存在已经足够；要求不存在“同时无 cheap set 的候选”才是相应矛盾。不能把所有形式 residual 描述自动读成已经证明或必须证明的空图类。[依据：R40 §5、R52 §5、R53 §§2、5。](../ctx/r53/a38_univ/PROOF_REPORT.md)

### 2.2 Unrestricted TF GEN6：缺少全域的源存在或模型存在定理

**PROVED — 已有工具。** 封存的 TF descent 和 path lifting 提供最小正反例入口。R53 CONNECTED-CORE6 在独立完整外邻域、唯一 core parent 和相应 conflict-color/原始度条件下产出正 proper TF 模型；supported core 的内部付款可调用已封存 GEN5。这些是真实的部分生产定理。

**OPEN — 所需全域结论。** 每个 TF、strong C4-free、`p≤12` 图均有 `2e≤6n`。在最小正反例形式下，必须强迫一个合法正 proper TF 模型、cheap set 或 P13，覆盖 empty-low、isolated-low、重叠端口、非饱和中心、高频接触和过重外臂。

**PROPOSAL — 缺失的桥。** 证明“所有候选根/核心的预算同时失败，就强迫 P13 或 cheap set”的全局替代定理；或者设计可处理重复父点、外邻域边和高颜色数的新交换。继续证明 SM/SMP 或又一个低接触子类，不提供这座桥。[依据：R53 TF §§1、2、5。](../ctx/r53/tf_gen6/PROOF_REPORT.md)

### 2.3 STAR：先纠正非退化性，再解决 availability

**PROVED — 有效基线。** 可用的是 R51 的 NEIGHBOR-AVERAGE、ROOT-CLOSURE、LOW-TREE-AVERAGE 三族及其精确加权最优值。R52、R53 的 STAR 总声明均不作为封存前提。

**COMPUTED — 引用 R53 referee 的反例。** G41 的 `(n,e,ε₆)=(41,124,2)`。取 `T={0}` 时，所称 region quotient 就是原图，没有 proper descent；referee 报告其精确 `p=20`。它推翻无 cap 的 singleton 声明，并非 cap-12 猜想反例。

**PROPOSAL — 修订的必要边界。** 按 referee 要求，BALANCED-LOW-TREE / even-K averaging 须显式加入 `|T|≥2`，逐项保留 properness 和严格正性条件。本评估不为修订后定理作新认证。

**OPEN — 修订后仍缺的内容。** 必须另行覆盖 singleton、空 low 集、独立 low 集及所有 R51 加权独立集预算均失败的输入；还要在 dense retained-center contacts 下强迫安全交换、ordinary-return 或 double-star 的可付费出口。排除 singleton 缩小了声明，不能关闭完整 STAR 门。[依据：R51 STAR §5；R53 失败裁决。](../ctx/r53/_failed_claims/star_prod/REFEREE_VERDICT.md)

### 2.4 T6：需要无条件的三角形下降覆盖

**PROVED — 已有工具。** 合法 core contraction、实际 low-component 价格、joint safety、LONG9/END6/END8、private-pair，以及 R53 binary-return cactus 的自动付款，均已在其范围内封存。R53 的正输出始终要求 `ε₆(G)>0`。

**OPEN — 所需新结构。** 对全部正、2-connected、cap-12、all-model-irreducible 的三角形输入，证明 cheap set、P13 或正 proper admissible model 必有其一。需要处理高边界度、core 非三角边度过大、noncactus incidence、一个 witness 看见至少三个 unit endpoints，以及未付费 K4 分量。

**PROPOSAL — 可检验的主攻击。** 证明“这些返回障碍不能被核心信用支付，就强迫过长诱导路或另一种合法联合收缩”的二择一定理。仅在 binary cactus 范围内，现有局部预算是 `2κ≤3(t+2c_I−2b−6)+2(e₀+m)`；须从完整输入推出该不等式，或绕过它，并另行覆盖域外情形。不能删掉 clique charge 后宣布原 producer 通用，也不能把局部安全收缩直接当成联合安全。[依据：R53 T6 §§2、5 及 referee 修正。](../ctx/r53/t6_univ/PROOF_REPORT.md)

### 2.5 General K / HYBRID：必须真正进入原生参数范围

**PROVED — 条件骨架。** 封存接口为 `GEN_{K−1}+T_K+Z_K ⇒ GEN_K`。完整路线仍需 lower-GEN 归纳下所有 `K≥7` 的 T_K，以及 `K≥12` 的剩余 Z_K，或能证明同等完整 GEN 族的替代方法。已封存的 Z 输入到十一不能外推到全部 K。

**OPEN — 缺失的生产。** BOUNDARY/HYBRID 须在全部所需输入中选出 root、arms、predeletion，并支付完整边界修复及 triangle cleanup；不能假设独立边界、two-center 频数、cubic center、低实际度或足够 arm capacity 自动存在。clustered matching contacts 等余类仍未关闭。

**PROPOSAL — 必要的参数升级。** 新主引理应在 `p≤2K` 下给出随 K 有效的路径/模型/付款结论，覆盖奇偶 K、任意接触和相应 cut 义务。R53 的 P13 在原生 K≥7 时可能完全合法；固定 cap-12 下把付款公式写成 K，不等于证明原生 GEN_K。HYBRID 的最终清理也必须实际付费，不能只证明中间含三角形模型为正。[依据：R53 GEN_K §§4、5；R45 装配 §4。](../ctx/r53/genk_prod/PROOF_REPORT.md)

### 2.6 RAD：需要普遍可支付的非循环下降

**OPEN — 全域目标。** 对所有连通 strong C4-free 图，`r=rad(G)≥11`、`p(G)=2r−1` 时证明 `S(G)≤(r−1)|G|`。这仍是独立于全部 GEN 的开放块。

**PROVED — 已有条件付款。** 封存的下降核心具有 `rad(D)=r−1`、`p(D)=2r−3`。令 `X=V(G)\D`，较低半径 RAD 给出 `ε_{r−1}(G)≤−|D|+F_{r−1,G}(X)`。因此普遍产出 `F_{r−1,G}(X)≤|D|` 的合法核心，是一条足够的关闭路线；已有 W/O/J52/E53 等源只在各自范围内做到付款。

**OPEN — 真正缺失的范围。** 对每个剩余正的 least-radius 输入，选到可付费核心，或直接证明同等强的质量上界。R53 的补集允许每个 anchor 都留下失败 component；包括 wide attachment、NP 失败的 root block，以及所有 shortest-entry 都不满足 BN 的 rootless component。任意深度和非循环终端均须有出口。

**PROPOSAL — 新付款引理的形式。** 从真实 radius equality、全局诱导路 cap 与所有端口接触共同推出总层损失上界；或用能支付正负质量抵消的 rooted block 势替代 BN 假设。不能仅扩大“若具有某良性终端则付费”的列表。

**PROVED — 不可省略的 cap 区别。** `p(D)=2r−3` 超过 `GEN_{r−2}` 的 cap `2r−4`。这里必须使用正确的低半径 RAD 或新定理，不能靠 GEN 补上。[依据：R53 RAD §§4、5；R45 装配 §4。](../ctx/r53/rad_real133/PROOF_REPORT.md)

## 3) 粗略距离：仍是 research-open，无法诚实换算成天数或轮数

**CONJECTURED — 距离判断。** “完整证明仍远”是合理的项目判断。这里的“远”表示至少几个彼此未解决的全域结构问题，且有无界 K 与半径义务；不是对未来突破日期的预测。现有证据不支持给出剩余百分比、天数、十轮/百轮或计算量数量级。

**PROVED — 已实现的进展与未实现的进展。** R53 确实证明了更大的源类，不能称为毫无数学进展。但这些报告明说：没有证明全部真实正 capped residual 的严格缩小，或根本没有相应严格性声明。新增源类、更多控制图和新证书计数，都不是离全域覆盖还差多少的度量。

**COMPUTED — 引用现有记录的边界。** R53 A38 的两个展示图分别有负 ε₆，且带 P13；TF、T6、GEN_K 的所述新机制图也带 P13。这些图验证方法及其限制，不能作为 cap-12 剩余输入正在被逐个消除的计数依据。此处引用封存报告，没有新做路径极值计算。

**PROVED — 自动包装的作用边界。** 包装已有部分定理，不会逻辑上补出缺失的全称命题。CWF 本身不是障碍：一个覆盖全域的定理也可能仅因交付问题获 CWF，并真正关门；关键是定理的范围。

**CONJECTURED — 对 R55+ 的预期。** 只延续“找一个额外子类、包装 CWF、自动下一轮”的方式，没有可信的关门机制。未来某轮当然可能产生突破，但那需要新的全域论证，不能由已有轮次外推。增加模型运行量也没有已知换算成完成距离的比例。

## 4) 值得继续之前，必须改变什么

**PROPOSAL — 先冻结自动链。** 保留现有工具库。停止以六条线均产出可接受包为默认完成条件。R54 的退出只说明该次运行未交付，不单独证明数学不可能；暂停的主要理由是通用缺口持续存在。

**PROPOSAL — 只设一个主目标：A38 的全域删除引理。** 研究说明第一页就写明完整输入、要产出的原图集合、原始度预算，以及全局 `p≤12` 在哪一步不可替代。特别说明如何处理“没有任何良性 metric core”的分支。没有这一步，就不能把核心付款继续称作本门的主关闭路线。

**PROPOSAL — 改变成功标准。** 可进入正式关门评审的结果是：整个余类都被一个合法出口覆盖；或得到不依赖未证生产义务的全域替代归约。新部分定理仍可归档，但不能触发自动续轮或“接近完成”的升级。若提出有限穷举路线，先证明覆盖全部输入的有限化界，再安排枚举。

**PROPOSAL — 设定停止条件。** 先用一至两次限时策略讨论检查主候选，而不启动新的证明轮。若候选仍需先给一个好核心、成功 coloring 或已付费 repair，或只能再加度/深度阈值，就停止该主线。若反例只被 P13 排除，下一步必须解释为何所有对应障碍都强迫 P13；再构造一个 uncapped 机制图不足以通过这个检查。

**PROPOSAL — 减少并行主题。** STAR 降为 EB6/TF 的辅助方法，singleton 修正留作局部维护。GEN_K 与 RAD 各保留准确的独立开放目标，待有覆盖原生参数范围的新主引理再恢复主动推进。T6 作为后续必要门保留，不能误认为先完成 EB6 就同时完成三角形问题。

**PROPOSAL — 若 A38 路线仍无全域候选。** 暂停生产流水线，转做新不变量或根化质量—半径路线的可行性设计。baseline G2 的有符号抵消、G3 的一般 rooted PP133 可以提示方向；它们本身仍 OPEN，不能写成已完成的替代装配。

**PROPOSAL — 不再继续的工作。** 不以 contact-catalog 扫描、h 阈值提升、重复 SM/SMP 子类、纯“若已生产则关闭”标题或更多 fixture 数量为主目标。不从“某一 producer 最优值不正”推断“所有模型都不存在”。控制图只用于否定过强候选，测试须保留全部接触、原始度、路径 cap、positivity 和正确的 irreducibility。

## 5) 给 Neil 的建议

- **PROPOSAL — 保持暂停，先重设计。** 当前不值得恢复连续自动证明链；完整 REAL-133 仍应登记为 **OPEN / research-open**。
- **PROPOSAL — 若继续，只先攻 EB6/A38。** 目标是对完整余类一次性强迫 cheap deletion 或 cap 矛盾；CLOSEST 是相对选择，绝不是近期完成承诺。
- **PROPOSAL — 不把 STAR 修正当成关门进度。** `|T|≥2` 处理一个明确的声明漏洞；empty/isolated-low 与全域 availability 仍须独立解决。
- **PROPOSAL — 重启须有明确新数学内容。** 先拿出覆盖整个目标域的主引理或已证明有效的全域替代归约，再安排正式证明与独立核验；不要因又一个部分 CWF 自动推进。
- **PROPOSAL — R55 自动轮现在不值得启动。** 现阶段应投入问题重述和全域强迫机制设计。即使 EB6 完成，T6、高参数 GEN/HYBRID 与 RAD 仍分别是 **OPEN**。

证据定位：当前状态见 [R54 briefing](../ctx/BRIEFING.md) 与 [R53 certificate](../ctx/ROUND_BRANCH_R53_CERTIFICATE.json)；各数学范围以本文所引 PROOF_REPORT 加同目录 referee 修正为准。较早开放地图仅作方向参考，见 [OPEN_PROBLEMS](OPEN_PROBLEMS.md)。本次仅交付评估；没有修改 `ctx`、重审 R54、启动 R55 或生成证明证书。
