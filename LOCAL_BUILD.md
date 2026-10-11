# 本地运行 Note198

请下载或克隆**整个仓库**，不要只下载 `Note198/` 或 `paper/` 子目录。
运行命令时，当前目录必须包含 `lakefile.toml`、`lake-manifest.json` 和 `lean-toolchain`。

## 安装与构建

先安装 Git 和 [elan](https://github.com/leanprover/elan#installation)。elan 会根据仓库的 `lean-toolchain` 安装 Lean 4.34.1。

```sh
git clone https://github.com/tqyqiqi1509/Note198-formalization.git
cd Note198-formalization
lake --version
lake exe cache get
lake build
```

`lake exe cache get` 下载固定 Mathlib 版本的预编译缓存；第一次运行需要联网。`lake build` 的默认入口为 `Note198.lean`，它导入 `Note198.ManuscriptWithBridges`，包括论文形式化和两处桥接证明。

也可以明确指定同一个入口：

```sh
lake build +Note198.ManuscriptWithBridges
lake env lean AuditBridgeReadable.lean
```

完整目标类型和公理查询：

```sh
lake env lean AuditWithBridges.lean
```

## 在 VS Code 中阅读

安装 Lean 4 扩展，然后用 **Open Folder** 打开仓库根目录。不要只打开某一个源码文件或 `Note198/` 子目录。
完成上述构建后，可以打开 `Note198/MainPacket.lean`、`Note198/SelectionIterationBridge.lean` 和 `Note198/FiniteSourceBridge.lean`。

## 配置与检查范围

- `lakefile.toml`：构建目标和依赖。
- `lake-manifest.json`：Mathlib 和传递依赖的固定提交。
- `lean-toolchain`：Lean 4.34.1。
- `Note198.lean`：默认构建入口。
- `vendor/`：旧验收所用的源码快照，保留供对照；当前构建使用配置中指定的官方 Git 依赖。

普通 Lean 构建不需要安装 Comparator。重新运行 Comparator 则需要它的匹配工具和环境；仓库中的 `comparator-check-serial-noprecommit` 是原验收机器的包装脚本，包含本机安装路径，不是通用安装器。

若运行失败，请保存从**第一条错误开始**的输出，以及 `lake --version` 的输出；这能区分目录、下载、工具链和证明编译问题。

## Windows：使用 WSL 的 Linux 文件系统

在 Windows 上建议通过 WSL Ubuntu 运行 Git 和 Lean，并把工程保存在 Linux 文件系统，例如 `~/projects/Note198-formalization`。避免在 WSL 中对 `/mnt/c/`、`/mnt/d/` 等 Windows 挂载目录进行大量构建；[Microsoft 的文件系统说明](https://learn.microsoft.com/en-us/windows/wsl/filesystems)解释了跨文件系统访问的性能代价。

先从 Windows 终端进入 Ubuntu：

```powershell
wsl -d Ubuntu
```

在 Ubuntu 中安装 Git 和 elan 后，运行：

```sh
mkdir -p ~/projects
cd ~/projects
git clone https://github.com/tqyqiqi1509/Note198-formalization.git
cd Note198-formalization
lake exe cache get
lake build
```

已有 Linux 工作副本时，直接进入该目录即可，无需重新克隆。编辑时使用 Windows VS Code 的 WSL 扩展，通过 **WSL: Open Folder in WSL** 打开 Linux 中的仓库根目录，同时安装 Lean 4 扩展到 WSL 环境。这样编辑界面仍在 Windows，Git 和 Lean 使用 Linux 工具和文件系统。

本次构建配置修复没有改变原有数学声明或证明。新增的 `Note198.lean` 只导入已有入口；已有 773 个数学 Lean 源文件保持不变。`local-build-logs/` 记录了配置修复后的构建和两处桥接公理查询。原完整 Comparator 验收对应此前固定版本；最终用于平台登记的提交仍应执行该平台要求的验收，并人工核对自然语言命题与 Lean 声明。
