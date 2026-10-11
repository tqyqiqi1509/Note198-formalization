# Note198 formalization

Lean source and verification records for Note198. Lean version: **4.34.1**.

## Build

Clone the entire repository, open its root folder, and install Git and elan. See [local build instructions](LOCAL_BUILD.md). Then run:

```sh
lake exe cache get
lake build
lake env lean AuditWithBridges.lean
```

The build uses the canonical Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612, matching Lean 4.34.1. Its transitive dependencies are pinned by lake-manifest.json. The old dependency source snapshots under vendor/ are retained for provenance comparison; the current build uses the official Git dependencies. Build caches and tool binaries are excluded. Each snapshot retains its original license; hashes are in vendor-source-sha256.json.

## Verification

The fixed version passed 28 Comparator groups covering 58 targets. Queried axioms were limited to `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurred in the accepted target dependencies. See `VERIFICATION.md` and `verification-logs/` for statements, configuration, versions and actual results. Historical input receipts are separately stored under `verification-receipts/`.

`Note198Challenges/` contains challenge templates with intentional proof placeholders. They are not the completed solution files, which reside in `Note198/`.

Comparator replay additionally requires the matching Comparator installation and its environment; the supplied wrapper records the original local setup. The formalization covers the listed targets and does not claim that every sentence of the manuscript has been formalized. The manuscript TeX and PDF are provided under `paper/`.

AI assistance was used in preparing the formalization and reviewing proofs. Lean and Comparator checks are recorded as machine verification of the specified targets, distinct from human verification.

## Manuscript

- [PDF](paper/note198.pdf)
- [LaTeX source](paper/note198.tex)

This is the revision with the explicit zero-module, zero-complex and empty-supremum conventions. Its TeX hash matches the manuscript frozen during the recorded Lean bridge verification.
