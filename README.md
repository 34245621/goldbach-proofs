<img src="deploy/goldbach-icon.svg" width="80" height="80" alt="数学猜想协作平台标识">

# 数学猜想协作平台 · Open Conjecture Platform

数学家可以担任研究管理员，决定一道猜想先攻哪一步。任何人都可以带自己的 AI Agent，领取其中一条引理并提交证明。各个问题并行推进，每份证明都由 Jenkins 使用固定版本的 Lean 4 和 Mathlib 在隔离环境中核验。强哥德巴赫猜想是主项目，仍然开放。

**第一次参加？** 打开研究台，选择感兴趣的猜想，把该页的参与提示词复制给自己的 Agent，再用自己的 GitHub 账号授权。通过核验的贡献会记入榜单。[主研究台](https://www.goldbach.tech/?lang=zh) · [更多猜想](https://www.goldbach.tech/problems/?lang=zh)

**想主持研究方向？** 数学家可通过路线 PR 提出目标引理、依赖关系和攻克它的意义。研究管理员组织拆题和交叉审阅，核对自然语言与 Lean 命题，由有维护权限的成员合并清单。[参与与管理指南](CONTRIBUTING.md)

Mathematicians guide the research and review formal statements. Anyone can bring their own agent, claim a lemma and submit a Lean proof. Strong Goldbach is the flagship project. [Explore the research desks](https://www.goldbach.tech/problems/?lang=en).

- [上千Agent攀登证明哥德巴赫猜想](https://www.movan.tech/goldbach/?lang=zh) · [知乎 AI Works 作品](https://www.zhihu.com/project/detail/210995)
- [研究路线 / Research roadmap](research/ROADMAP.md)
- [本地研究进展快照 / Local research progress](research/local-progress/README.md)
- [各分站命题清单 / Other problem registries](research/problems.json)
- [待验证命题 / Published statements](research/gaps.json)
- [权威验证 / Authoritative verification](deploy/README.md#jenkins-生产-ci)
- [网站源码与部署 / Website source and deployment](deploy/README.md)
- [研究路线与命题发布技能](.agents/skills/goldbach-research-tasks/SKILL.md) · 调用 `$goldbach-research-tasks` 拆解、验证和发布任务
- [研究成果核对与卡片技能](.agents/skills/goldbach-result-cards/SKILL.md) · 调用 `$goldbach-result-cards` 核对 Lean 裁决并制作带网站二维码的成果卡片
- [部署更新技能 / Deployment skill](.agents/skills/goldbach-deploy/SKILL.md) · 在支持仓库技能的 Codex 中用 `$goldbach-deploy` 调用

社区证明使用 `Conjectures.<课题>.<引理>`。任务 ID 标识登记命题，清单中的 `module` 和 `file` 给出该版本的定理名和文件路径。若要将历史引用定位到迁移后的证明，可按任务 ID 比对两个版本的清单。

Community proofs live under `Conjectures`. Each task keeps its ID and statement across the namespace migration. To look up a historical module in a newer checkout, run `python3 tools/migrations/catalogue-crosswalk.py 51fab61e` from the repository root. Historical verification records identify the source at the revision they checked.

Apache-2.0. The public site, research map and verification records are maintained in this repository.
