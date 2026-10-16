# Vendored library subset

Unmodified source files (`.v` only) from the **Coq Library of Undecidability Proofs**,
https://github.com/uds-psl/coq-library-undecidability, branch `coq-8.20`,
commit `70dfc56f33a6e4835281044e68aa68279989047e` (2024-09-18).
License: Mozilla Public License 2.0, see `LICENSE` (copied from the upstream repository).

`theories/` keeps the upstream directory layout (logical root `Undecidability`). The subset is the
dependency closure of the files used by this development: `FOL/Sets/minZF.v`, `FOL/Sets/ZF.v`,
`FOL/Deduction/FullNDFacts.v`, `FOL/Reductions/PCPb_to_minZF.v`, `FOL/Sets/Models/ZF_conservativity.v`.
`../../check.py` compiles it with the upstream `_CoqProject` option `-set "Default Proof Using = Type"`.
