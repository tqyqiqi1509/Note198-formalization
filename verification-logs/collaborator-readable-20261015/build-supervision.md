# Note198 compilation supervision — 2026-10-15

Working tree: `/opt/codex-comparator/workspaces/note198-local-build` in Ubuntu WSL.

Baseline HEAD: `5769b33f0f30d5f3ce5dbf1300bbc46bfbd26a98`.
Lean: `4.34.1`; Lake: `5.0.0-src+5045d00`.
Mathlib locked revision: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No project or ancestor AGENTS.md was found under `/opt`; user-supplied instructions apply.

## Commands and baseline

Use Ubuntu's default user `lenovo`, not root:

```sh
source /opt/codex-comparator/env.sh
cd /opt/codex-comparator/workspaces/note198-local-build
lake build
lake env lean AuditWithBridges.lean
```

The environment sets `LEAN_NUM_THREADS=2`; the project's existing library setting uses `weakLeanArgs = ["-j1"]`. No unsupported `lake -j` option was added. The original baseline `lake build` exited 0 with `Build completed successfully (9603 jobs).` This reused existing artifacts and replayed existing linter warnings; it was not a clean rebuild.

Evidence directory: `E:\Formalization\Note198\readability-20261015\evidence`.

* `baseline-build.log`: successful baseline build.
* `baseline-axioms-types.log`: first audit attempt, failed during another agent's accidental dependency-directory deletion.
* `recovered-baseline-axioms-types.log`: successful complete baseline audit, exit 0, 58 axiom queries, no `sorryAx`. Every axiom list is either `[propext, Classical.choice, Quot.sound]` or `[propext, Quot.sound]`.
* `baseline-source-sha256.txt`: file hashes saved after baseline; a collaborator's newly created file may already occur, so use Git HEAD comparison for the original-provider preservation claim.
* `baseline-lake-manifest.json`: original manifest.

## Environment incident and local recovery

Another agent ran Lake as root. Root Git cannot read the lenovo-owned dependency repository normally: a read-only `git remote get-url origin` against the preserved `batteries` dependency reports `detected dubious ownership`; `git config --get remote.origin.url` fails. Lake reported `mathlib: URL has changed; deleting ... and cloning again`. That process and its clone child were stopped (PIDs 4829 and 4933). This was an environment problem, not a mathematical or proof failure.

No dependency upgrade or download was used for recovery. A Lake-native local `.lake/package-overrides.json` selects `/opt/codex-comparator/workspaces/note198/vendor/mathlib`, whose cached artifacts use Lean 4.34.1. A recursive comparison of this source with the current project's fixed vendor/mathlib snapshot found only the extra `.github` directory, no mathematical source difference. The original prior local-build receipt identifies the vendor snapshot with the fixed Mathlib revision. The tracked lakefile and manifest are unchanged. Other installed dependencies remain in the project's `.lake/packages`.

This local override makes ordinary `lake build` and `lake env lean` work without extra command-line parameters. It must remain a local cache detail and must not be included in a source distribution. A portable fresh checkout continues to use the unchanged official pinned dependencies. A direct-Lean helper was used only for the recovered original audit; the final new modules must pass normal Lake build and the new audit through Lake.

`recovered-build.log` records an interim failure caused by placing an import after a module doc comment in the changed root navigation file. The parent agent corrected the import order. `final-build.log` records the subsequent final build run.

The final build compiled `Note198.CollaboratorResults`, `Note198.CollaboratorMain`, `Note198.Collaborator`, and the root entry. Normal `lake build` exited 0 with `Build completed successfully (9606 jobs).`

The first `lake env lean -j1 AuditCollaborator.lean` run verified all 10 new axiom queries (only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`) and six of eight full-type proof equalities. Two equalities between universe-polymorphic constants required explicit matching universe arguments: unconstrained universes triggered coercion search and its typeclass heartbeat limit. This is recorded in `audit-collaborator-attempt-1.log`.

After the parent added `universe u` and explicit `.{u}` arguments to those two pairs in the audit script, the final `lake env lean -j1 AuditCollaborator.lean` exited 0. All eight full-type equalities compiled with `rfl`, all ten axiom queries reported exactly `[propext, Classical.choice, Quot.sound]`, and there were no errors or `sorryAx`. `final-audit-collaborator.log` is the successful final evidence. `AuditCollaborator.lean` and `final-new-source-sha256.txt` in the evidence directory were refreshed after this correction.

The original 773 tracked mathematical providers under `Note198`, `Note198Challenges`, and `upstream` have no diff against HEAD. `original-provider-diff.txt` and `dependency-config-diff.txt` are intentionally empty successful diff reports. Only the existing root `Note198.lean` changes, adding the new navigation import.

## Evidence boundary

Compilation and axiom inspection establish Lean acceptance relative to the fixed dependencies and the listed standard axioms. They do not independently establish correspondence with the natural-language manuscript. Full-type equality checks and the separate translation supervisor address preservation of the existing Lean translation; neither upgrades the original paper-to-Lean audit evidence.
