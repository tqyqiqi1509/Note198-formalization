# Derived tensor definition update — 2026-10-23

## Reason for this update

A natural-language-to-Lean review system stopped at an unproved `derivedTensor_exists` obligation after reading the original brief convention for derived tensor products. Its generated code was unavailable. The targeted audit found no mathematical existence obstruction in the uses examined, but identified a need for more explicit foundational definitions.

This folder contains the revised manuscript and its verification records. Only the opening definition block was expanded: input/output categories, module actions, direct-sum totalization and signs, the left-derived universal property, a resolution construction and well-definedness proof, and conditions for using projective models. All TeX content outside that block is byte-for-byte unchanged; the original 20 numbered results and labels retain their order.

- `note198.tex`, `note198.pdf`: updated manuscript.
- `opening-definition.patch`: exact source change.
- `修改与核验说明.txt`: detailed change and validation notes.
- Review reports and JSON files: independent AI review, scope checks, and compilation records.

The PDF compiled successfully and was visually checked. These records do not certify that the external natural-language-to-Lean system will succeed, or that the new general resolution proof has itself been formalized in Lean.

The existing `paper/` files and existing branches are preserved. This update is published in a new folder on a separate branch.
