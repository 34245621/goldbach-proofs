# 中间命题提交稿：GRH 下全范围显式 1+1 例外集（$C = 16$）、短区间（$C_1 = 8$）与 Linnik 二幂偏移表示（$K = 22$）

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)） · [上游源码快照（`eef391f`）](https://github.com/Visio-Vanitas/buchstab-switching/tree/eef391f3dc2579fcba703886b773f24330233cf9/1%2B1) · [复核指南](README.md)

**定位与诚实边界。** 本提交稿在**仅假设 Dirichlet $L$ 函数广义黎曼猜想**（`DirichletLNonvanishingRightOfHalf`，与 `lean/PEqualNP/GRH.lean` 及 `lsernau/grh-lean@72fead1` 逐字一致；其中定理 1B 仅需普通 RH）与**已发表强哥德巴赫经验验证界** $E(4\cdot 10^{18}) = 0$（Oliveira e Silva–Herzog–Pardi, 2014）的前提下，给出围绕强哥德巴赫（`1+1`）猜想的三组**全体偶数/全实数起点（$N_0 = 4$ / $N_0 = 48$）**显式定量推进、零浮点计算证书及 Lean `v4.36.0` 条件归约。本轮 v2 升级将定理 1A 从 `12731` 压缩 **795.7×** 至 **`16`**、将定理 1B 从 `6281` 压缩 **785.1×** 至 **`8`**（优于 Chirre–Hagen 2026 的 $123(\log X)^2$ 达 **15.4×**），并彻底移除所有黑箱经验缓冲常数。对任意 $N > 4\cdot 10^{18}$ 的无条件逐点 `1+1`（$K = 1, s = 0$）依然开放。

---

## 1. 认证命题总览

| 编号 | 定理名称（`OnePlusOne.Main`） | 假设条件 | 显式结论（无渐近大 $O$ 隐含常数） | 全范围起点 |
|---|---|---|---|---|
| **1A (v2)** | `theorem_1A_all_even_exceptional_set` | GRH + $E(4\cdot 10^{18}) = 0$ | $E(X) \le 16 \sqrt{X} (\log X)^3$ | **全体 $X \ge 4$** |
| **1B (v2)** | `theorem_1B_all_even_short_interval` | RH（$\zeta(s)$） + $E(4\cdot 10^{18}) = 0$ | $[X,\ X + 8 (\log X)^2]$ 必含偶数 $N = p_1 + p_2$ | **全体 $X \ge 4$** |
| **3A** | `theorem_3A_all_even_exact_linnik_22` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{i=1}^{22} 2^{k_i}$（$k_i \ge 1$，精确 **22** 个幂） | **全体偶数 $N \ge 48$** |
| **3** | `theorem_3_all_even_linnik_goldbach` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{j=1}^s 2^{k_j}$（$s \le 22$） | **全体偶数 $N \ge 4$** |

---

## 2. 关键技术推进与全范围闭合机制

### 2.1 定理 1A v2：4-adic 壳层 Laplace 引擎（$12731 \to 16$，零黑箱缓冲）

- **4-adic 壳层与缩放优化**：采用 4-adic 壳层 $(Y/4, Y]$、缩放因子 $\kappa = 11/20 = 0.55$、主弧截断 $Q_0 = \lfloor 3 Z^{1/4} \rfloor$ 与精确 Dirichlet 分母 $Q_D = \lfloor \sqrt{Z} \rfloor$（$\Delta(q) = 1/(q Q_D)$，消除 $\sqrt{Z}$ 与 $\lfloor\sqrt{Z}\rfloor$ 的边界缝隙）。
- **BMOR 零点计数 + Binet 垂线界 + 零黑箱 $C_{E_2}$**：
  - 结合 Bennett–Martin–O'Bryant–Rechnitzer (2021) 显式零点计数、$\chi/\bar\chi$ 配对与 Riemann–Stieltjes 分部积分；
  - 用 Binet 第一公式得到 $|\Gamma(\frac{1}{4}+it)| \le \sqrt{2\pi}\,e^{1/3}|t|^{-1/4}e^{-\frac{\pi}{2}|t|}$ 并与 $\operatorname{Re}(s)=\frac{5}{2}$ 相减（精确因子 `4.5`），将垂线积分误差压至 $\sim 10^{-6}$；
  - 用单位区间 Bochner 核 $e^{-2|v-(v_k+1/2)|} \ge e^{-1}$ + $\operatorname{Re}(s)=\frac{5}{2}$ Hadamard 展开从零推导出 $C_{E_2} \le 28.09150728248$（完全无 `+4.00` 等经验缓冲）。
- **全区间外舍入认证与 Lean 4 收口**：在 `[4 * 10^18, 10^10000]` 切分 15 个向外有向区间细胞及单调渐近尾段 $[10^{10000}, \infty)$（80 位 `Decimal` + `FloatOperation` 陷阱，见 [`scripts/certify_exceptional_short.py`](https://github.com/Visio-Vanitas/buchstab-switching/blob/eef391f3dc2579fcba703886b773f24330233cf9/1%2B1/scripts/certify_exceptional_short.py)），认证 4-adic 增量上界 $E(Y) - E(Y/4) \le 7.77 \sqrt{Y}(\log Y)^3$（最弱细胞 $[4\cdot 10^{18}, 10^{19}]$ 处 `7.76342528`，单调递减至尾段 `4.61768434`）；Lean 4 内 [`Exceptional.exceptional_all_range_of_fouradic`](https://github.com/Visio-Vanitas/buchstab-switching/blob/eef391f3dc2579fcba703886b773f24330233cf9/1%2B1/OnePlusOne/Exceptional/DyadicClosure.lean) 无条件证明叠缩因子 $\sum_{k<m}(1/2)^k < 2$（`Arithmetic.fouradic_geom_sum_lt`），与 $2 \times 7.77 = 15.54 < 16$（原始上界 `15.526850543`）无缝闭合至全体 $X \ge 4$。

### 2.2 定理 1B v2：平均锐截断 Fejér 核 + 精确闭式 Mellin 矩（$6281 \to 8$，高区仅需 RH）

- **平均 Fejér 窗与锐截断恒等式**：基于 $R_\Lambda(n) = 2\psi(n-1)-(n-1)+(e*e)(n)$ 及平均 Fejér 权 $\widetilde{W}(n) = \sum_{h = \lceil M_0/4 \rceil}^{M_0} W_h(n)$（取 $\varepsilon = 1/4$，接近最优 $2-\sqrt{3} \approx 0.268$，给出 $(2-\varepsilon)/(1-\varepsilon^2) = 28/15$，极限系数 $4\cdot 28/15 = 7.467 < 8$，直到 $\infty$ 均保持 $> 6.6\%$ 正余量）。
- **精确闭式 Mellin 矩与 Fatou 引理零截断余项**：采用精确闭式一二阶矩 $\frac{2}{\pi}\int_0^\infty \frac{\sin^2 v}{v^2}\log v\,dv = 1 - \gamma_E - \log 2$、$\frac{2}{\pi}\int_0^\infty \frac{\sin^2 v}{v^2}(\log v)^2\,dv = (1-\gamma_E-\log 2)^2 + 1 + \frac{\pi^2}{12}$、Bochner 最优核 $K(u) = Z^2 e^{-2|u-u_Z|}$、$\operatorname{Re}(s)=\frac{5}{2}$ Hadamard 界（$C_{\text{row}} \le 0.687875$）与 Fatou 引理（完全消除显式公式截断余项 $R(x, T)$）。
- **全区间认证与 Lean 4 闭合**：15 个细胞上 $C_J$ 从 $4\cdot 10^{18}$ 处的 `1.05284360` 单调增至 $[10^{10000}, \infty)$ 处的 `1.75087527 < 1.76`，全部细胞统一认证 $C_1 = 8$；Lean 4 内 [`ShortInterval.short_interval_small_range`](https://github.com/Visio-Vanitas/buchstab-switching/blob/eef391f3dc2579fcba703886b773f24330233cf9/1%2B1/OnePlusOne/ShortInterval/FejerReduction.lean) 无条件证明 $[4, 4\cdot 10^{18})$ 内任意长 $8(\log X)^2 \ge 2$ 的区间必含偶数并由 $E(4\cdot 10^{18})=0$ 闭合。

### 2.3 构造性二进制桥梁 + 圈法压低全范围 Linnik–Goldbach 到 $K = 22$（定理 3 / 3A）

- **直接强推圆法的瓶颈**：不带二进制桥梁直接在 $N = 4\cdot 10^{18}$ 运行显式圈法需要 $r_{\mathrm{dir}} = 52$（`maj_net = 0.5302 > minor = 0.4839`），而文献渐近 GRH 的 $K = 7$（脚本亦复现：`minor <= 1.7909 < Maj >= 1.9204`）不含显式小 $N$ 起点。
- **二进制哥德巴赫桥梁（已全量形式化进 Lean 内核，零外部计算依赖）**：设桥梁上界
  $$N_{\mathrm{br}}(22) := (2^{23} - 2)\cdot 2^{61} + 4\cdot 10^{18} \approx 1.93428 \cdot 10^{25}.$$
  因 $2^{61} \le 4\cdot 10^{18} - 4$，对任意偶数 $N \in [48, N_{\mathrm{br}}(22)]$，区间 $[N - 4\cdot 10^{18}, N - 4]$ 内必存在 $M\cdot 2^{61}$（$1 \le M \le 2^{23} - 2$）；$M$ 的二进制展开最多含 22 个 1 比特，若不足 22 个则利用 $2^e = 2^{e-1} + 2^{e-1}$ 从 $\ge 61$ 的指数反复拆分成恰好 22 个正指数 $k_i \ge 1$，使余数 $N - M\cdot 2^{61} \in [4, 4\cdot 10^{18}]$ 命中已知哥德巴赫表。该构造在 [`OnePlusOne/Linnik/Reduction.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/eef391f3dc2579fcba703886b773f24330233cf9/1%2B1/OnePlusOne/Linnik/Reduction.lean) 的 `binary_goldbach_bridge_22` 中 **100% 无条件证完**。
- **高区圈法接棒（$N > N_{\mathrm{br}}(22)$，对应 $L = \lfloor \log_2(N/16) \rfloor \ge 79$）**：
  - 高斯窗 Mellin–Plancherel 主弧 $L^2$ 界 $C_{E_2} \le 38.6184 < 40$ + 奇异级数 $T_D(X) \ge 1.172$ 截断保正；
  - 精确 1D Selberg 素数筛（$C_{\mathrm{Sel}} \le 5.499$ at $L=79$，$C_{\mathrm{Sel}} \le 9.1412$ for $L \ge 140$）+ mod $105$ / Pintz–Ruzsa $P_{15}$ 均值表（$\bar{\mathfrak{S}}_2 \le 2.600769$）+ $B=8$ 状态 Bessel-$I_0$ 转移矩阵（$M_\phi = 32$）；
  - $r = 21$ 在 $L = 78$ 失败（`1.6486 < 1.7909`），**$r = 22$ 在 $L = 79$ 首次跨越（`1.6429 > 1.4393`，余量 `+0.2036`）**，覆盖全部 $L \in [79, 139]$（最差余量 `+0.1008` at $L=83$），并在 $L \ge 140$ 由 Collatz–Wielandt 步长衰减因子 `0.910613 < 1` 统一收口（`maj_net >= 1.7553 > minor <= 0.9813`，余量 `+0.7740`）。

---

## 3. Lean 4 形式化信任边界与宿主机复核实测结果

在 64 核 `GoldBach` 宿主机（容器外，使用与本仓库 CI 一致的 Lean `v4.36.0`、Mathlib `fc4f59e5` 及 `autoImplicit = false`、`relaxedAutoImplicit = false`、`maxSynthPendingDepth = 3`、`maxHeartbeats = 4000000`）已实测通过全部检查：

1. **Lean 无条件证明范围**：
   - `Arithmetic.major_arcs_disjoint`、`ratio_2p_sub_1_le_pow_eighth`、`twin_prime_partial_product_ge`（`> 0.65928`）、`totient_sq_ge_half`、`dyadic_geom_sum_lt`（`< 2 + √2`）、`fouradic_geom_sum_lt`（`< 2`）；
   - `Exceptional.exceptional_all_range_of_dyadic`、`exceptional_all_range_of_fouradic`、`fouradic_multiplier_le_16`、`fouradic_of_parseval_bounds`、`theorem_1A_of_fouradic`；
   - `ShortInterval.one_lt_log_four`、`short_interval_small_range`、`exists_goldbach_of_weighted_pos`、`short_interval_all_range`（`ShortIntervalProp 8 2`）；
   - `Linnik.binary_goldbach_bridge_22`（$48 \le N \le 1.93428\cdot 10^{25}$ 全体偶数）、`Linnik.all_even_exact_linnik_22`、`Linnik.all_even_linnik_22`；
   - `Certificates.certifiedCells_valid`（15 行 $10^{-8}$ 精度）、`Certificates.fouradic_16_rat_check`、`Certificates.linnikCheckpointCells_valid`（6 个关键节点）由纯内核 `by decide` / `norm_num` 检验（零 `native_decide`）。
2. **显式隔离的外部解析接口（`OnePlusOne/External/Premises.lean`，零 `axiom`）**：
   - `EmpiricalGoldbachBase`（$E(4\cdot 10^{18}) = 0$）、`FouradicLaplaceCirclePremise`（定理 1A v2 高区 4-adic Parseval–Laplace 界 `777 / 100`）、`FejerShortIntervalPositivityPremise`（定理 1B v2 高区平均 Fejér–Mellin 正性 `8`）、`LinnikCircleAboveBridgePremise`（定理 3 高于 $N_{\mathrm{br}}(22)$ 处的圈法正性）。
3. **验证实测摘要**：
   - `python3 -I scripts/quick_verify.py`：4 项检查全过（两套 Python 脚本 AST 零浮点/`import math` 泄漏、精确重放比对、`Data.lean` 15 行 $10^{-8}$ + 6 节点数据逐位吻合、10 个 Lean 源码文件零禁词）。
   - `lake build OnePlusOne`：7,412 jobs **0 错误、0 警告**。
   - `lake env lean AxiomsCheckOnePlusOne.lean`：32 条导出声明全部严格仅依赖 `[propext, Classical.choice, Quot.sound]` 及其子集。
   - `bash comparator/run_comparator.sh`（16 个导出目标，`red-challenge.export` = `9e7a7768eaf...`，`red-solution.export` = `a5db4023b39...`）：`leanchecker-paranoid`、`nanoda_bin` 与 Lean 默认内核均接受解模块（`exit 0`），且含 `sorryAx` 的自挑战被正确拒斥（`exit 1`）。
