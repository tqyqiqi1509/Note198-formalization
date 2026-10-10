# Note198 两项 Lean 桥接补充与复验

本次工作对应上一轮审查的 U01、U02。论文采用已补充零模约定的 `note198.tex`；本轮未编辑论文。数学源码在新的 Ubuntu 副本 `/opt/codex-comparator/workspaces/note198-bridges-01a125b7` 中补齐，并按固定 Lean 4.34.1 与原公理名单检查。

## 选择迭代公式

`Note198.SelectionIterationBridge` 直接使用原有 `Selection.Data`、`H` 和 `iterate`。参数为任意域 k、k-代数 R、中心幂等元 e 以及 k-代数自同构 α；M 为任意左 R-模，n 为非负整数。

`eAt_eq_pow` 证明第 i 个选择子为 α^i(e)。`iterationProduct_eq_finset` 的实际陈述使用有序列表乘积，证明递归乘积等于 e_0 e_1 … e_(n−1)，n=0 时为空积 1。`productSelected_eq_image` 证明该乘积的固定子模就是它的像。

`productPullback` 将上述子模的 R-作用沿 α^n 拉回。`iterateProductMap_bijective` 与 `iterateProductEquiv` 给出原有递归迭代到该拉回模的真实 R-线性同构；`selection_iteration_formula` 陈述该同构存在。其构造保留底层元素，并证明作用关系为 r ↦ α^n(r)。

原有模块 `Note198.SelectingSimpleFamily` 中的定理 `Note198.selecting_simple_family` 使用同一个 `Selection.Data` 与 `Selection.iterate`。后续自同态接口由模块 `Note198.SelectionEndomorphismBridge` 中既有的 `Note198.selection_H_endomorphism` 和 `Note198.selection_iterate_endomorphism` 连接。因此本次同构适用于工程中的实际选择操作。

因此机器检查对应论文公式

\[
H^{\circ n}(M)\cong{}_{\alpha^n}(e_0e_1\cdots e_{n-1}M).
\]

上述同构对任意左 R-模成立，包括零模和无限维模。

## 有限源的标量关系与左理想

`Note198.SelectionProductNormalization` 来自本地工程中已有、但未列入上一轮 25 组正式复验的源码，本轮将其加入目标。`Note198.FiniteSourceBridge` 补足完整桥接。

参数为任意域 k、素数 p、正整数 m，并要求 p 在 k 中非零。`coordinateFactor_earlier` 和 `coordinateFactor_last` 分别证明各因子确实是论文的平均选择子 e_i 和 1−e_(m−1)。`paperProduct` 在中心坐标群代数中计算前 m−1 个因子的乘积，再映入有限商群代数并乘上末因子；m=1 时前面的乘积为 1。这就是论文的 p_m。

接受目标证明

\[
\mathrm{paperProduct}=p^{-(m-1)}\,\mathrm{sourceVector},\qquad
\mathrm{sourceVector}=p^{m-1}\,\mathrm{paperProduct},
\]

以及

\[
\mathrm{sourceIdeal}=k[F_m]\,\mathrm{paperProduct}.
\]

最后一式在 Lean 中表述为以实际群代数为标量环、由单个 `paperProduct` 生成的子模相等，因而是左主理想的相等。证明覆盖 sourceIdeal 中的每个元素，使用中心性、平均选择子的作用关系及 p 在 k 中非零给出两个包含。

## 本次验收结果

完整入口构建成功，58 个目标类型及公理查询成功；**28/28 组 Comparator 接受，58/58 个目标覆盖**。所有本次验收命令退出码为 0，正式目标公理查询未出现 `sorryAx` 或未许可公理。最终源码、配置及工具版本比对通过，论文文件的 SHA-256 在本轮前后相同。

| 检查组 | 本次结果 | 耗时（秒） |
| --- | --- | ---: |
| build-fixed | 成功 | 12.4 |
| types-and-axioms | 成功 | 76.4 |
| Bridge-SelectionIterationBridge | 接受 | 18.2 |
| Bridge-SelectionProductNormalization | 接受 | 22.9 |
| Bridge-FiniteSourceBridge | 接受 | 22.4 |
| Final-BarSplitting | 接受 | 137.0 |
| Final-BigFinitisticDimension | 接受 | 40.2 |
| Final-Core | 接受 | 14.2 |
| Final-ExplicitSimpleModulesFinal | 接受 | 42.0 |
| Final-FiniteEncoding | 接受 | 64.3 |
| Final-FinitePresentationEncoding | 接受 | 13.6 |
| Final-GenericExactDimension | 接受 | 170.9 |
| Final-GenericPDDetection | 接受 | 163.2 |
| Final-PrimeFifteenPresentation | 接受 | 11.6 |
| Final-PrimeFiniteQuotient | 接受 | 21.0 |
| Final-RemainingAlgebraModules | 接受 | 362.2 |
| Final-RemainingCentralShift | 接受 | 9.4 |
| Final-RemainingDimensions | 接受 | 348.6 |
| Final-RemainingDirectedBound | 接受 | 66.0 |
| Final-RemainingKernelChain | 接受 | 1230.2 |
| Final-RemainingLiftedDiagram | 接受 | 106.8 |
| Final-RemainingOrdinarySimulation | 接受 | 394.4 |
| Final-RemainingRealization | 接受 | 394.5 |
| Final-SelectingBoundedThickKernelChain | 接受 | 427.5 |
| Final-SelectingExactFunctor | 接受 | 397.1 |
| Final-SelectingIteration | 接受 | 398.1 |
| Final-SelectingSimpleFamily | 接受 | 23.7 |
| Final-SourceDiagramLift | 接受 | 37.8 |
| Final-StandaloneGenericRectification | 接受 | 300.0 |
| MainPacket | 接受 | 1732.2 |


新目标共 12 个，分成三组：选择迭代桥接 5 个、已有归一化源码 3 个、有限源桥接 4 个。原 25 组的 46 个目标也在本次副本中重新运行，合计 28 组、58 个不同目标。原有 766 个 Lean 源文件在补充前逐文件比对一致，最终再次核对它们与新增源码的字节稳定性。

许可公理保持 `propext`、`Quot.sound`、`Classical.choice`。Challenge 的 `sorry` 为目标模板占位；正式 Solution 目标的实际公理查询不得出现 `sorryAx`。本次 Comparator 配置保持 `enable_nanoda=false`，实际结果属于 Lean 默认内核检查，没有运行独立外部内核。

项目使用复制的原工程构建缓存，并通过符号链接复用固定依赖目录。版本、构建日志、目标类型与公理查询、逐组退出码、源文件冻结与最终稳定性比对均保存在 `logs/`。

## 如何理解“现在是否就可以了”

本次完成后，上一轮明确指出的两项桥接覆盖缺口得到 Lean 证明和实际验收；加上此前的零模约定修订，这三项具体待办已有对应证据。

可准确表述为：本次固定版本中列出的 58 个目标通过相应 Lean/Comparator 验收，两项桥接已纳入其中。20 个编号结果与原稿的对应关系仍依据此前逐项语义审查。这里没有把每行正文、全部外部引用或每个未编号断言都转化成新的独立形式化目标，也不宣称整篇论文已由另一套独立内核或人类专家完整认证。

## 文件与复验

- `project/Note198/SelectionIterationBridge.lean`：选择迭代完整桥接。
- `project/Note198/SelectionProductNormalization.lean`：原有中心坐标乘积与归一化。
- `project/Note198/FiniteSourceBridge.lean`：论文乘积、可逆标量关系、左理想相等。
- `project/Note198/ManuscriptWithBridges.lean`：原论文入口加两项桥接的统一入口。
- `project/comparator-bridge-*.json` 与 `project/Note198Challenges/`：新目标配置与模板。
- `project/AuditWithBridges.lean`：原目标和新目标的类型、公理查询。
- `logs/verification-results.json`：本次所有实际退出码与接受结果。
- `logs/types-and-axioms.log`：实际陈述、公理与关键定义输出。
- `logs/source-freeze.json` 与 `logs/final-source-stability.json`：源码版本对应。
- `scripts/`：本次准备、验收及导出脚本；记录了本机绝对路径，迁移机器时须调整这些路径。

复验可直接使用已保存的 Ubuntu 工程：

```bash
source /opt/codex-comparator/env.sh
cd /opt/codex-comparator/workspaces/note198-bridges-01a125b7
lake build +Note198.ManuscriptWithBridges
lake env lean AuditWithBridges.lean
bash comparator-check-serial-noprecommit comparator-bridge-SelectionIterationBridge.json
bash comparator-check-serial-noprecommit comparator-bridge-SelectionProductNormalization.json
bash comparator-check-serial-noprecommit comparator-bridge-FiniteSourceBridge.json
```

交付的 `project/` 包含数学源码、目标模板和配置；不含大型 Lean/Mathlib 安装、vendor 依赖或构建缓存。离开本机复验须先恢复 `lakefile.toml` 中列出的固定本地依赖及匹配工具链，不能直接把这些本地路径当作可自动下载的依赖声明。SHA-256 清单用于字节一致性检查，不作为数学正确性证明。
