# Note198 可读性重组：独立语义监督

审查时间：2026-10-15。只读检查原项目；未修改任何 Lean 提供模块。

## 证据与范围

读取 MEMORY.md 相关 Note198 条目（175–188，229–242）以定位历史语义边界，随后实读 E:/Formalization/Note198/note198-formalization/coverage_final.md、verification/final_type_semantic_audit.md、reference/note198.tex，以及 WSL /opt/codex-comparator/workspaces/note198-local-build/Note198 下 MainPacket、SelectingMain、Manuscript、ManuscriptWithBridges、RemainingRealization、GenericExactDimension、GenericPDDetection、SelectingBrickFamily、SelectingFamilyMaximum。

WSL 构建副本没有 reference/coverage_final.md；E: 原稿和现行覆盖报告是文本对应证据锚。覆盖报告主张 20 个编号结果、25 个提供模块均有已冻结核验与 AI 语义审查；本轮阅读不把历史记录或 Lean 编译升级为人工论文认证，也没有独立 nano-lean 完整通过结论。

## 安全实施方案

新增 CollaboratorMain.lean / CollaboratorResults.lean 作为合作者阅读入口；保留旧提供者声明、命名、证明、import 与冻结收据。新增公开 theorem 使用完整类型；主定理展开 MainProperties 的全部 15 字段，并证明与原 MainProperties 的 iff，而非仅依靠单向投影。证明调用原已核定理，避免重做数学或引入额外假设。语法格式及命名可以改变，量词和实例字典必须一致。

## 主定理逐字段不可遗漏项

1. 同一个 R、Ring R、Algebra k R、S、E、F 在所有 m 之前选定；不能变为每个 m 另选代数。
2. k 是任意域、同一 universe，不能静默限定 ℂ 或 CharZero。
3. 主代数为实际 SelectingOrdinaryAlgebra.A E S；split basic 为 Jacobson 商与 Fin (3*length+6) → k 的 k-algebra 等价。
4. radical 七次为零；模族逐个有限维及三倍原向量空间维数。
5. Loewy 三需要 J^3 作用为零和 J^2 有非零作用两项；后项不能省为仅 ≤3。
6. 每个 End 的 DivisionRing 必须保留 d.toRing = 原 Module.End Ring 的字典等式；仅 ∃ DivisionRing 同载体不足以断言原 End 环是除环。
7. cross-Hom 对所有 m n、m≠n、每个 A-linear map 为零。
8. exact_pd 为实际 module 的 pd = Nat maximum；不能把被证明对象替换成计数模型。
9. 线性上下界中的 m : ℕ+、m.val-1、coefficient+5 和 length+3 均原样保留，pd 的 WithBot ℕ∞ coercion 由 Lean 检查。
10. complete / primitive / field / scalar 四组顶点性质均保留。仅构造中的顶点 i；不能误写任意 primitive idempotent。
11. 原 A little finitistic dimension 为 ⊤；与 Section 8 新构造 Lambda 区别。

MainProperties 正好 15 字段，逐项为 algebra_finite, split_basic, radical_seven, finite_modules, module_dimensions, loewy_three, end_division, hom_zero, exact_pd, linear_bounds, complete_vertices, primitive_vertices, field_corners, scalar_corners, finitistic_infinite。

## 其他完整块

- ℂ 分支需同一 ComplexBrickFamily 实例的 MainProperties、每个 m 的 3*2^(3*m.val)、ℂ-linear AlgebraEquiv 到原 End、全部跨族 Hom 为零。历史打印器超限不等于丢字典；不要任意引入新 ring。
- 所有奇移位：s : ℤ、3≤s、Odd s；先选 P 后 ∀Y。P 是 B⊗Bᵒᵖ 模块范畴的 BiComplex，Projective 不能弱化成左 B-projective；有界、逐项有限维、full balanced tensor 以及 derived iso 的两个直和项和 shift s 全保留。
- 实际 pd 精确式：索引为 Sum (Fin m.val) (Fin m.val)，even 项 +0、odd 项 +1；迭代次数 j.val 和两个原 projectiveDimension 输入保持完整。
- Section 8：同一个 Lambda 的 finite、little=big=⊤、opposite little=big=0、左不生成和右生成七项；一般域结论比原稿 ℂ 版本强，注释应明确“general-field version”，勿宣称逐字相同。
- 4.1：固定 P 和 BoundedProjective model M 先于所有 Y；不得改 ∀Y∃P。
- 6.2/6.3：无需外加选定数值 g/hg、X-projectivity 或最小模型证书；signed pd 的零输入为 -∞，Fin t 的空索引、t=0 不能静默排除。
- 3.1：最终 RemainingDirectedBound 没有 0<n，不能引用早期 Core 正顶点辅助版本冒充全结论。

## 验证要求

新文件逐字比较原声明（排除名字和空白），主定理逐字段比对并编译双向 iff；编译新阅读入口、#print axioms 新 theorem 且无 sorryAx；不修改旧提供者则历史冻结证据保持可引用，但新声明应单独记录本轮编译结果。本轮没有运行重复 lake build。

## 新文件审查

等待新文件落盘后补充。

### 2026-10-15 新文件落盘复审

已实读 CollaboratorMain.lean：main_properties_iff_expanded 的 15 字段逐一完整，双向证明映射顺序一致；theorem_1_1 同一 existential R/S/E/F 位于全部正整数 m 之前；End 原 Ring 字典、Loewy 非零项、exact_pd、上下界、完整正交/primitive/corner/scalar 及 ∞ 均保留。最终格式版本新增十五条语义注释，无数学改动。当前尚待独占构建监督者确认 Lean 编译；本监督者未竞争 lake 目标。

已实读 CollaboratorResults.lean：四个 MainPacket 对应声明进行去空白后的完整声明文本比较（在行末声明/证明分隔符截断，避免 letI/:= 命名参数误截），全部精确相等：

- packet_complex_bricks → theorem_1_1_complex（339非空白字符）。
- packet_all_odd_shifts → proposition_7_3（881非空白字符）。
- packet_actual_module_formula → exact_module_projective_dimension（688非空白字符）。
- packet_general_main_and_asymmetry → main_and_corollary_8_1（721非空白字符）。

另审 corollary_8_1 全七项与原 SelectingMain.asymmetry 相同；6.1、6.2、6.3 的 section 变量、Module 字典、scalar tower 与原提供者逐项一致，未增加 projectivity 或 numerical g/hg 假设。6.3 的 signedModuleProjectiveDimension 和 Fin t 保留零输入及 t=0 边界；7.3 的 P 在 BiComplex k B，Projective 针对实际 enveloping 模块对象；固定 P 先于所有有限维 Y，无量词交换。

建议已告知主代理：原稿6.1类型为 Proposition，可将 theorem_6_1 改名 proposition_6_1；8.1 注释说明 general-field version（原稿只写 ℂ）；最长行和结论缩进作纯格式优化。这些是标签/阅读建议，无语义阻断项。

结论：所审新文件的数学声明没有发现弱化、额外前提、量词错序、对象替换或边界丢失。准确性结论限于本轮新阅读层与既有已核声明的对应；不宣称本轮重新独立证明全稿，也不宣称完整 nano-lean 认证。原提供者未修改应由主代理最终哈希复核。

### 最终排版与证明重排复审

最终 CollaboratorMain 已将 theorem_1_1 放在前面，以原 main_properties 的全部 15 投影直接构造结论；双向 iff 放在其后。逐项复读无语义变化。实读 /tmp/note198-collaborator-main-format-receipt.json：去注释空白前后类型 token SHA 均一致，theorem_1_1 为 290a79a1b1a2109f29efc7c5cf0a3c6635c3a7ff39ffa4d4ee3e047311017cb7，iff 为 40262cd945a3f523416bb6eea1d821ac70a47b5343ae14633bd169c35a848382；206 行，最长 98 字符。

最终 Results 已改 proposition_6_1，并以注释明确8.1为一般域版本、原稿ℂ为其特例。实读仓库根 AuditCollaborator.lean：包含八项 @new = @original := rfl，以及十个新命题 #print axioms。这些测试若编译通过，则强制完整参数类型及字典兼容；本监督者未自行编译，不把测试文本存在当作通过。

实读 E:/Formalization/Note198/readability-20261015/evidence/preservation-check.json：基准750项中只有 Note198.lean 导航改变，original_mathematical_sources_unchanged=true。此收据是本轮原提供者保留检查，非数学正确性认证。

最终源文件 SHA-256（实际读取WSL仓库计算）：

- Note198/CollaboratorMain.lean: cbf304baf96581e9acb791db891ca7878229237575c74a97253f674a1091b5f6
- Note198/CollaboratorResults.lean: 4ac87f4787e2f945fc11e8dd1ee83be4f453fa15a9a687b28467450528e9d287
- AuditCollaborator.lean: 03b896f00a8011e856ac007ce4b5069c5d518dad00f2e0ff7241e2c614612881

最终只读监督结论：未发现翻译准确性变化；本轮改动在新增完整阅读块、格式、原定理直接引用与明确对应证明范围内。编译/axioms结果由独占构建监督者单独给出。

最终检查文件补充：两组涉及一般域存在见证的常量比较显式使用同一 universe u，以避免自由宇宙推断引起 CoeT 超时；未更改任何被审声明。上述 AuditCollaborator 哈希已更新至这一版。其实际通过状态见构建监督日志。
