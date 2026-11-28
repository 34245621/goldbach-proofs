# 中间命题提交稿：GRH 下全范围显式 1+1 例外集（$C = 16$）、短区间（$C_1 = 8$）与 Linnik 二幂偏移表示（$K = 18$）

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)） · [上游源码快照（`d5081e7`）](https://github.com/Visio-Vanitas/buchstab-switching/tree/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1) · [复核指南](README.md)

**定位与诚实边界。** 本提交稿在**仅假设 Dirichlet $L$ 函数广义黎曼猜想**（`DirichletLNonvanishingRightOfHalf`，与 `lean/ResearchSupport/GRH.lean` 及 `lsernau/grh-lean@72fead1` 逐字一致；其中定理 1B 仅需普通 RH）与**已发表强哥德巴赫经验验证界** $E(4\cdot 10^{18}) = 0$（Oliveira e Silva–Herzog–Pardi, 2014）的前提下，给出围绕强哥德巴赫（`1+1`）猜想的三组**全体偶数/全实数起点（$N_0 = 4$ / $N_0 = 40$）**显式定量推进、零浮点计算证书及 Lean `v4.36.0` 条件归约。本轮 **v2 完整收口版** 将定理 1A 从 `12731` 压缩 **795.7×** 至 **`16`**、定理 1B 从 `6281` 压缩 **785.1×** 至 **`8`**（优于 Chirre–Hagen 2026 的 $123(\log X)^2$ 达 **15.4×**）、定理 3 Linnik–Goldbach 全范围显式常数从 **`22` 压缩至 `18`**（纯有效渐近 GRH 从 `7` 推进至 **`6`**，无 Siegel 非构造依赖）、在 `HasLinnikRep` 类型中直接补严正指数约束 $k_j \ge 1$，并**彻底移除全部黑箱经验缓冲常数**（消除 v1 中的 `+4.00` 与 `+0.06`）。对任意 $N > 4\cdot 10^{18}$ 的无条件逐点 `1+1`（$K = 1, s = 0$）依然开放。

---

## 1. 认证命题总览

| 编号 | 定理名称（`OnePlusOne.Main`） | 假设条件 | 显式结论（无渐近大 $O$ 隐含常数） | 全范围起点 |
|---|---|---|---|---|
| **1A (v2)** | `theorem_1A_all_even_exceptional_set` | GRH + $E(4\cdot 10^{18}) = 0$ | $E(X) \le 16 \sqrt{X} (\log X)^3$ | **全体 $X \ge 4$** |
| **1B (v2)** | `theorem_1B_all_even_short_interval` | RH（$\zeta(s)$） + $E(4\cdot 10^{18}) = 0$ | $[X,\ X + 8 (\log X)^2]$ 必含偶数 $N = p_1 + p_2$ | **全体 $X \ge 4$** |
| **3A (v2)** | `theorem_3A_all_even_exact_linnik_18` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{i=1}^{18} 2^{k_i}$（$k_i \ge 1$，精确 **18** 个正指数幂） | **全体偶数 $N \ge 40$** |
| **3 (v2)** | `theorem_3_all_even_linnik_goldbach` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{j=1}^s 2^{k_j}$（$0 \le s \le 18$，类型内强制 $k_j \ge 1$） | **全体偶数 $N \ge 4$** |

---

## 2. 关键技术推进与全范围闭合机制

### 2.1 定理 1A v2：4-adic 壳层 Laplace 引擎（$12731 \to 16$，零黑箱缓冲）

- **4-adic 壳层与缩放优化**：采用 4-adic 壳层 $(Y/4, Y]$、缩放因子 $\kappa = 11/20 = 0.55$、主弧截断 $Q_0 = \lfloor 3 Z^{1/4} \rfloor$ 与精确 Dirichlet 分母 $Q_D = \lfloor \sqrt{Z} \rfloor$（$\Delta(q) = 1/(q Q_D)$）。
- **BMOR 零点计数 + Binet 垂线界 + 零黑箱 $C_{E_2}$**：结合 BMOR (2021) 显式零点计数、$\chi/\bar\chi$ 配对与 Riemann–Stieltjes 分部积分、Binet 第一公式垂线界与单位区间 Bochner 核 + $\operatorname{Re}(s)=5/2$ Hadamard 展开推导 $C_{E_2} \le 28.09150728248$。
- **全区间外舍入认证与 Lean 4 收口**：15 个向外舍入细胞（80 位 `Decimal` + `FloatOperation` 陷阱）认证 $E(Y) - E(Y/4) \le 7.77 \sqrt{Y}(\log Y)^3$（最弱细胞 `7.76342528`，尾段 `4.61768434`）；Lean 4 无条件证明 4-adic 叠缩因子 $< 2$（`Arithmetic.fouradic_geom_sum_lt`、`Exceptional.exceptional_all_range_of_fouradic`），结合 $2 \times 7.77 = 15.54 < 16$ 收口至全体 $X \ge 4$。

### 2.2 定理 1B v2：平均锐截断 Fejér 核 + 精确闭式 Mellin 矩（$6281 \to 8$，高区仅需 RH）

- 基于锐截断恒等式 $R_\Lambda(n) = 2\psi(n-1)-(n-1)+(e*e)(n)$ 及平均 Fejér 权 $\widetilde{W}(n) = \sum_{h = \lceil M_0/4 \rceil}^{M_0} W_h(n)$（$\varepsilon = 1/4$），配合精确闭式一二阶 Mellin 矩、Bochner 最优核 $K(u) = Z^2 e^{-2|u-u_Z|}$、$\operatorname{Re}(s)=5/2$ Hadamard 行和（$C_{\text{row}} \le 0.687875$）与 Fatou 引理（零显式公式截断余项），全区间 $C_J \le 1.75087527 < 1.76$（至 $\infty$ 保留 $> 6.6\%$ 正余量），统一认证 $C_1 = 8$。

### 2.3 定理 3 / 3A v2：构造性二进制桥梁 + 零黑箱 $\sin^2$ 圈法（$22 \to 18$；纯有效渐近 GRH $K = 6$）

- **二进制哥德巴赫桥梁（Lean 4 无条件证完）**：设桥梁上界
  $$N_{\mathrm{br}}(18) := (2^{19} - 2)\cdot 2^{61} + 4\cdot 10^{18} = 1{,}208{,}925{,}207{,}928{,}610{,}747{,}318{,}272 \approx 1.208925 \cdot 10^{24}.$$
  对任意偶数 $N \in [40, N_{\mathrm{br}}(18)]$，在 $[N - 4\cdot 10^{18}, N - 4]$ 内取 $M\cdot 2^{61}$（$1 \le M \le 2^{19} - 2$，二进制 1 比特数 $\le 18$），再由 $2^e = 2^{e-1} + 2^{e-1}$ 劈分至恰好 18 个正指数 $k_i \ge 1$，余数落入 $[4, 4\cdot 10^{18}]$ 命中已知哥德巴赫表。该定理在 [`OnePlusOne/Linnik/Reduction.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1/OnePlusOne/Linnik/Reduction.lean)（`binary_goldbach_bridge_18`）中 100% 无条件证完，且 `HasLinnikRep` 已直接在 Lean 类型中强制要求 $\forall k \in ks,\ 1 \le k$。
- **高区零黑箱 $\sin^2(\pi t/N)$ 圈法（$N > N_{\mathrm{br}}(18)$，$L = \lfloor \log_2(N/8) \rfloor \ge 76$）**：
  - **彻底消除 v1 两项经验缓冲**：单位区间 Bochner–Hadamard 零黑箱主弧 $L^2$ 常数 $C_{E_2} \le 31.3259$（$C_{\text{row,dir}} \le 1.0000$，替代 v1 `+4.00`）；主弧非零点项分别采用全圆 Parseval 素数幂界（Rosser–Schoenfeld $\psi-\vartheta \le 1.4262\sqrt{N}$）、$\omega(q)(\ln N + 2\ln Q_0)$ 互素修正与精确主弧 $U \le U_q$ 垂线界；43 个奇数无平方模 $q \le 105$ 精确有理 Ramanujan 和表 + $D_1 = 2000$ 截断尾（$\le 0.01683$）+ $Q \le 1{,}800{,}000$ 外舍入前缀和（替代 v1 `+0.06`）；
  - **单 $N$ Dirichlet 小弧上确界与 16 方向精确有理凸多边形自动机**：用 $Q_1 = Q_{\max} = \sqrt{Y}$ 消除子区间 $(N_{\mathrm{hi}}/N_{\mathrm{lo}})^{3.5}$ 膨胀；16 个勾股有理方向构成 20 层嵌套精确 `Fraction` 凸多边形，利用 $x^2+y^2$ 凸性在精确有理顶点处取最大值并作 Abel 分层求和；
  - **全区间外舍入结果（总耗时 45.97 秒）**：全部 44 个有限段 $L \in [76, 119]$ 均通过（最紧段 $L = 76$：`lhs >= 1.0000 > rhs <= 0.9883`，余量 $\ge 0.0117$；$L = 85$ 起切换至无 $M_{\text{dyad}}$ 纯 $B=10$ 矩阵，至 $L = 119$ 余量升至 $\ge 0.2765$）；$L \ge 120$ 无穷尾由纯 Collatz–Wielandt 步长衰减因子 $\le 0.916314 < 1$ 统一封口（`lhs >= 1.0000 > rhs <= 0.8886`，余量 $\ge 0.1114$）；
  - **纯有效渐近 GRH 基准（吸收 Li–Liu `arXiv:2610.15784v1`）**：460 对显式有理方向网（无 Siegel 非构造定理，$C_1 = 8.0$）认证 **`K = 6`**（`lhs <= 0.5131 < rhs >= 0.5929`，余量 $\ge 0.0798$）；同网代入 Lichtman $C_1 = 6.7814$ 亦零浮点复现 Li–Liu 的 `K = 5`（余量 $\ge 0.0044$）。

---

## 3. Lean 4 形式化信任边界与宿主机复核实测结果

在 64 核 `GoldBach` 宿主机（容器外，CI 一致配置 Lean `v4.36.0`、Mathlib `fc4f59e5`）实测通过全部检查：

1. **Lean 无条件证明范围**：
   - `Arithmetic.major_arcs_disjoint`、`ratio_2p_sub_1_le_pow_eighth`、`twin_prime_partial_product_ge`、`totient_sq_ge_half`、`dyadic_geom_sum_lt`、`fouradic_geom_sum_lt`；
   - `Exceptional.exceptional_all_range_of_dyadic`、`exceptional_all_range_of_fouradic`、`fouradic_multiplier_le_16`、`fouradic_of_parseval_bounds`、`theorem_1A_of_fouradic`；
   - `ShortInterval.one_lt_log_four`、`short_interval_small_range`、`exists_goldbach_of_weighted_pos`、`short_interval_all_range`（`ShortIntervalProp 8 2`）；
   - `Linnik.binary_goldbach_bridge_18`（$40 \le N \le 1.208925\cdot 10^{24}$ 全体偶数）、`Linnik.all_even_exact_linnik_18`、`Linnik.all_even_linnik_18`（含 `HasLinnikRep` 类型内强制 $k_j \ge 1$）；
   - `Certificates.certifiedCells_valid`（15 行 $10^{-8}$）、`fouradic_16_rat_check`、`linnikCheckpointCells_valid`（6 节点 $10^{-4}$）、`linnik_tail_growth_lt_one`（`916314 / 1000000 < 1`）由纯内核 `by decide` / `norm_num` 检验（零 `native_decide`）。
2. **显式隔离的外部解析接口（`OnePlusOne/External/Premises.lean`，零 `axiom`）**：
   - `EmpiricalGoldbachBase`（$E(4\cdot 10^{18}) = 0$）、`FouradicLaplaceCirclePremise`（`777 / 100`）、`FejerShortIntervalPositivityPremise`（`8`）、`LinnikCircleAboveBridgePremise`（`K = 18`，阈值 $N_{\mathrm{br}}(18)$）。
3. **验证实测摘要（快照 `d5081e7`）**：
   - `python3 -I scripts/quick_verify.py`：4 项检查全过（双脚本 AST 零浮点/`import math`、65 秒双脚本精确重放、`Data.lean` 逐位吻合、10 个 Lean 文件零禁词）。
   - `lake build OnePlusOne`：7,412 jobs **0 错误、0 警告**。
   - `lake env lean AxiomsCheckOnePlusOne.lean`：32 条导出声明全部严格仅依赖 `[propext, Classical.choice, Quot.sound]` 及其子集。
   - `bash comparator/run_comparator.sh`（16 个导出目标，`red-challenge.export` = `2f2597bf827...`，`red-solution.export` = `e96622f4baf...`）：`leanchecker-paranoid`、`nanoda_bin` 与 Lean 默认内核均接受解模块（`exit 0`），且含 `sorryAx` 的自挑战被正确拒斥（`exit 1`）。
