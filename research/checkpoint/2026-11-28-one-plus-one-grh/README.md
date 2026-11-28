# 全范围显式 1+1 例外集（C = 16）、短区间（C₁ = 8）与 Linnik 二幂偏移表示（K = 18）· 上游固定快照与独立复核指南

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)）。[中间命题提交稿](proof.md)

本目录提交强哥德巴赫（`1+1`）方向在 GRH（定理 1B 高区仅需 RH）+ 已知经验界 $E(4\cdot 10^{18}) = 0$ 下的三项全范围显式中间定理及其 Lean 4（`v4.36.0`）形式化归约与零浮点计算证书（**v2 完整收口版：定理 1A `12731 → 16`（795.7×）、定理 1B `6281 → 8`（785.1×）、定理 3 Linnik–Goldbach 全范围 `22 → 18` + 纯有效渐近 GRH `7 → 6`、`HasLinnikRep` 直接在类型中补严正指数 $k_j \ge 1$，并彻底消除全部黑箱经验缓冲常数**），供仓库维护者与同行独立复核。所有数值证书、Lean 编译结果及外部解析接口均以独立重放审定为准。

---

## 1. 上游仓库与固定版本信息

- **上游仓库**：[`https://github.com/Visio-Vanitas/buchstab-switching`](https://github.com/Visio-Vanitas/buchstab-switching)（分支 `feat/one-plus-one-v436`，子目录 `1+1/`）
- **固定代码与验证快照 SHA**：`d5081e7a2dae5d8067c43d92cf35403ce12f0ee4`（完整论文手稿位于分支同目录 `1+1/manuscript/linnik_goldbach_all_range.pdf`）
- **Lean 工具链与依赖锁**（与本仓库 `lean/lean-toolchain`、`lean/lake-manifest.json` 及 CI `leanOptions` 完全一致）：
  - [`1+1/lean-toolchain`](https://github.com/Visio-Vanitas/buchstab-switching/blob/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1/lean-toolchain)：`leanprover/lean4:v4.36.0`
  - [`1+1/lake-manifest.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1/lake-manifest.json)：Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  - [`1+1/lakefile.toml`](https://github.com/Visio-Vanitas/buchstab-switching/blob/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1/lakefile.toml)：`autoImplicit = false`、`relaxedAutoImplicit = false`、`maxSynthPendingDepth = 3`、`pp.unicode.fun = true`、`maxHeartbeats = 4000000`
- **GRH 声明对齐目标**：[`1+1/OnePlusOne/Core/Defs.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/d5081e7a2dae5d8067c43d92cf35403ce12f0ee4/1%2B1/OnePlusOne/Core/Defs.lean) 中的 `DirichletLNonvanishingRightOfHalf` 与本仓库 `lean/ResearchSupport/GRH.lean` 及 [`lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) 逐字一致；**零 `native_decide`**（全部 32 条导出声明仅依赖 `[propext, Classical.choice, Quot.sound]` 及其子集）。

### 关键存档文件 SHA-256（以 `git clone -c core.autocrlf=false` 检出 `d5081e7` 为准）

| 相对路径 | SHA-256 | 说明 |
|---|---|---|
| `1+1/scripts/certify_exceptional_short.py` | `6ce343ef33d175bb01ed1f10ef53c6ba969d337582c5fbad097cd6e0caa209c4` | 定理 1A / 1B v2 零浮点 80 位 `Decimal` 认证器（零经验缓冲） |
| `1+1/data/certify_exceptional_short_output.txt` | `761055c9aefb1efcd2044b77f008867b3d705f2c2964e06c0dca29dc0ba62243` | 定理 1A / 1B v2 完整外舍入认证日志（15 个细胞 + 尾段） |
| `1+1/scripts/certify_linnik_r.py` | `ff3cb2a0e344b123de51ead4d8cad6e96f0a02f26dec62e487262d06253665c4` | 定理 3 v2（全范围 $K=18$ + 有效渐近 GRH $K=6$）零浮点零黑箱认证器（45.9s） |
| `1+1/data/certify_linnik_r_output.txt` | `7e899404ab298381e86209eaa4c91247031158d00c527a8c7d1defcde4c8b48c` | 定理 3 v2 外舍入认证日志（44 有限段 $L=76\dots 119$ + $L\ge 120$ 尾段） |
| `1+1/scripts/quick_verify.py` | `9b5b2e9dc00006c4d19fed213d8a3fa8c31ec8c637cbb10bc73c08666c2f50fa` | AST 零浮点扫描 + 双认证器重放 + `Data.lean` 精确比对 + 静态审计 |
| `1+1/OnePlusOne/Core/Defs.lean` | `0ff71f62d13cf5b98831aa29937528269b22445b80b40617f609815e6b1c67ea` | 核心定义（含补严后的 `HasLinnikRep` $k_j \ge 1$ 与 `GRH` 声明） |
| `1+1/OnePlusOne/Certificates/Data.lean` | `859cd787b4f04b296d68c0c246f34f531d5f6efc115d02e17bbc2afb08bd2676` | 纯内核 `by decide` / `norm_num` 整数证书表（15 行 $10^{-8}$ + 6 节点 $10^{-4}$） |
| `1+1/OnePlusOne/Exceptional/DyadicClosure.lean` | `951510f0c23ba39e8b81abc013afea0123bc2929fe406e9b89cae9343b1199b8` | 纯 Lean 无条件 4-adic 与二进叠缩收口（$C_{\text{4-adic}} \le 7.77 \implies C = 16$） |
| `1+1/OnePlusOne/ShortInterval/FejerReduction.lean` | `78d01ec07f710ed5788e51ac4bf01fe340b8496ff85678252cbcfea096ae9260` | 纯 Lean 无条件小区间补空与短区间正性归约（$C_1 = 8$） |
| `1+1/OnePlusOne/Linnik/Reduction.lean` | `c9635330a0caff38f6773229d28a0d06593e6219ab1e7dc3d25440510510efbf` | 纯 Lean 无条件二进制哥德巴赫桥梁（$40 \le N \le 1.208925\cdot 10^{24}$，精确 $K=18$） |
| `1+1/OnePlusOne/Main.lean` | `3c680528f8c14252ba90238967c8eb5994c4d1cf395013586642146dced25154` | 顶层导出定理 `theorem_1A`（16）、`theorem_1B`（8）、`theorem_3A`（18）、`theorem_3`（18） |
| `1+1/AxiomsCheckOnePlusOne.lean` | `8c012514c2479ad760087f555512b964bdc47cef8f71150fcce0a97d3a0c485a` | 32 条导出定理的 `#print axioms` 公理审计文件 |
| `1+1/comparator_output.txt` | `027afee387e4da89d1c0ab155dbac04b8cdb1e77bd7aa147bbbfb2b754e99c9f` | 16 个导出目标三内核 `comparator` 实测复核完整日志 |

---

## 2. 供维护者独立执行的复核命令（POSIX shell）

```sh
git clone -c core.autocrlf=false https://github.com/Visio-Vanitas/buchstab-switching.git
cd buchstab-switching
git fetch origin d5081e7a2dae5d8067c43d92cf35403ce12f0ee4
git checkout --detach FETCH_HEAD

# 1. Python 零浮点 AST 审计、双证书全量重算对照（约 65 秒）与 Lean 静态洁净度扫描
cd 1+1
python3 -m py_compile scripts/*.py
bash -n comparator/run_comparator.sh
python3 -I scripts/quick_verify.py

# 2. Lean 4.36.0（CI 编译配置）构建与 32 条声明三公理白名单检查
lake exe cache get
lake build OnePlusOne
lake env lean AxiomsCheckOnePlusOne.lean

# 3. Comparator 独立多内核导出复核（16 目标，leanchecker-paranoid + nanoda_bin + sorryAx 自挑战拒斥）
bash comparator/run_comparator.sh
```

---

## 3. 主要源码与论文手稿索引

| 核查模块 | 上游路径 |
|---|---|
| 顶层导出定理 | `1+1/OnePlusOne/Main.lean` |
| 显式外部解析前提接口（零 `axiom`） | `1+1/OnePlusOne/External/Premises.lean` |
| 初等算术与筛法核心引理（无条件 Lean 证明） | `1+1/OnePlusOne/Arithmetic/ElementaryBounds.lean` |
| 定理 1A 4-adic 与二进叠缩全范围收口（无条件 Lean 证明） | `1+1/OnePlusOne/Exceptional/DyadicClosure.lean` |
| 定理 1B 小区间补空与 Fejér 正性归约（$C_1 = 8$） | `1+1/OnePlusOne/ShortInterval/FejerReduction.lean` |
| 定理 3 构造性二进制桥梁 $40 \le N \le 1.208925\cdot 10^{24}$（$K = 18$） | `1+1/OnePlusOne/Linnik/Reduction.lean` |
| 独立 Comparator 挑战目标声明（16 个目标） | `1+1/comparator/ChallengeOnePlusOneReduction.lean` |
| 数学推导规范与 Linnik–Goldbach 论文手稿（LaTeX + PDF） | `1+1/notes/DESIGN_AND_PROOF_SPEC.md`、`1+1/notes/LINNIK_GOLDBACH_SPEC.md`、`1+1/manuscript/` |
