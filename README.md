# Note198 formalization

Lean source and verification records for Note198. Lean version: **4.34.1**.

## Build

Install the matching Lean toolchain using elan, then run:

```sh
lake build +Note198.ManuscriptWithBridges
lake env lean AuditWithBridges.lean
```

The repository includes the exact dependency source snapshots under `vendor/`, preserving the path dependencies used in verification. Build caches and tool binaries are excluded. Each dependency retains its original license; see its directory. Snapshot hashes are in `vendor-source-sha256.json`.

## Verification

The fixed version passed 28 Comparator groups covering 58 targets. Queried axioms were limited to `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurred in the accepted target dependencies. See `VERIFICATION.md` and `verification-logs/` for statements, configuration, versions and actual results. Historical input receipts are separately stored under `verification-receipts/`.

`Note198Challenges/` contains challenge templates with intentional proof placeholders. They are not the completed solution files, which reside in `Note198/`.

Comparator replay additionally requires the matching Comparator installation and its environment; the supplied wrapper records the original local setup. The formalization covers the listed targets and does not claim that every sentence of the manuscript has been formalized. No paper TeX or PDF is included.

AI assistance was used in preparing the formalization and reviewing proofs. Lean and Comparator checks are recorded as machine verification of the specified targets, distinct from human verification.
