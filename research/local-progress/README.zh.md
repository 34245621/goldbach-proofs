# 本地研究进展快照

本目录登记 `/home/azureuser/projects/goldbach/` 下的本地研究，供众包研究台引用。它记录研究状态和可复核入口，不把条件定理、有限计算或数值实验记为强哥德巴赫猜想的无条件证明。

## 条件 Goldbach 形式化

来源目录为 `conditional-goldbach-lean`，提交 `c55db645f3b4aed00374fe4aa1fcee2428c88c4b`。项目的 Lean 4.36 证明工程报告了 102 条审阅声明和 1400 条传递依赖的闭合检查。`ConditionalGoldbach.Proofs.WeakS` 中的 `goldbach_of_weakS` 从 `WeakS` 和权函数条件推出充分大偶数的中央三分之一素数表示。`WeakS` 本身仍是待证明的解析输入，因此该结果属于条件研究进展。

可复核入口如下。

- `formalization/ConditionalGoldbach/Proofs/WeakS.lean`
- `formalization/verification/independent-audit/final-comparison.json`
- `formalization/README.zh.md`

主工程固定 Mathlib 提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。完整审阅仍应在原项目的 `formalization` 目录运行，众包仓库不把它作为已发布社区模块直接导入。

## Dirichlet GRH 形式化

来源目录为 `grh-lean`，提交 `72fead102f663d5c7a407964a13dc0cf9d977207`。其中 `grh/src/New/Reduction/MainInequality.lean` 提供研究笔记使用的归约入口。它服务于 GRH 下的条件路线，不能替代无条件的素数分布估计。

## 固定间距与间距 180 研究

来源目录为未带 Git 历史的 `twin-prime-spectrum` 工作树。`grh-critical-zero-window.md` 将间距 180 的判据归约到临界线上高度 `|γ| < 0.24`、阶大于 `x^0.4295` 的偶本原特征窗口。`check_grh_critical_zero_window.py` 的区间计算已复核窗口外的数值余量。窗口内所需的带符号零点下界仍开放，故这是一条已量化的条件研究路线。

## 弱 S 与二元哥德巴赫

来源目录为未带 Git 历史的 `weak-S` 工作树。它给出固定权、主弧和次弧的研究分解，并记录有限数值试验。当前缺口是对每个充分大偶数的次弧带符号估计。有限样本和主弧数值不会替代该估计。

## 合并约定

本快照只进入研究文档，不进入 `research/gaps.json`，也不生成新的已核验任务。若要把其中某个结论发布为社区任务，应先把完整 Lean 声明、冻结哈希、依赖和证明范围写入对应任务，再由固定工具链独立核验。

精确提交、文件哈希和验证命令见同目录的 `manifest.json`。
