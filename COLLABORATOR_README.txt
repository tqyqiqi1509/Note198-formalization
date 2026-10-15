Note198 合作者阅读入口
日期：2026-10-15（北京时间）

本次调整
新增集中阅读层，保留原有数学提供模块与证明。
CollaboratorMain.lean 首先显示一般域主定理的完整十五项结论；
同文件的 main_properties_iff_expanded 证明展开前后双向等价。
CollaboratorResults.lean 集中列出复数域分支、6.1、6.2、6.3、7.3、
实际模块投射维数精确公式及8.1的一般域版本。
这些代码块复用既有证明，不重新命名原构造，不增加数学假设。

建议阅读顺序
1. Note198/CollaboratorMain.lean：theorem_1_1。
2. Note198/CollaboratorResults.lean：按所需结果定位完整声明。
3. 各声明末尾的原证明提供者：需要细读证明时直接跳转。
4. AuditCollaborator.lean：八项原声明全类型对应和十项公理查询。

编译
从含 lakefile.toml、lake-manifest.json、lean-toolchain 的仓库根运行：
  lake build
  lake env lean AuditCollaborator.lean
固定 Lean 4.34.1，固定 Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612。
首次在新机器使用时按 LOCAL_BUILD.md 准备固定版本的依赖缓存。
Note198.lean 已同时导入原入口与新阅读入口，因此默认编译覆盖新文件。

准确性保障
主定理十五个字段逐项展开，并有双向等价证明；其余八项有Lean全类型对应检查。
独立语义监督核对原声明、原稿与已存覆盖记录，特别检查同一对象的量词顺序、
原End环结构字典、Loewy非零项、构造顶点范围、双模投射性、相反代数方向和零输入边界。
这确认新增阅读层与既有声明的对应；不扩大历史论文证明审查范围。
本次不构成全稿重新独立证明，也不构成完整nano-lean第二内核认证。

版本来源
基于提交5769b33f0f30d5f3ce5dbf1300bbc46bfbd26a98。
本阅读层发布在独立分支collaborator-readable-20261015；原main分支保留。

构建记录
本轮普通 lake build 已成功（9606 jobs，复用固定版本的既有依赖缓存）。
三位子智能体分别参与主定理实现、独立语义监督及编译监督。
完整编译与审查日志见 verification-logs/collaborator-readable-20261015/；
原数学提供者相对基线Git提交没有差异。
本机缓存恢复使用 .lake 下的本地固定源码覆盖配置；它不进入源码分发包，
不改变分发包的官方固定依赖配置。

最终核验结果
普通 lake build：退出码0。
AuditCollaborator：退出码0，八项完整类型对应通过。
十项新声明的公理依赖均为 propext、Classical.choice、Quot.sound，无 sorryAx。
773个原数学Lean文件相对基线提交零差异；依赖配置零差异。
