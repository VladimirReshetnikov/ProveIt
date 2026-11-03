# Source review: symbolic compact kernel alias

Reviewed `KernelAliasExplicit.lean` at commit `7c14598ac5` and its author-side
observation. The alias is defined as the actual natural expression
`paramKernel rho`; `kernelAlias_eq` unfolds that definition, and
`kernelAlias_mod` applies the previously checked `symbolic_kernel_mod` in
the correct direction using congruence of the remainder proposition. The
local irreducibility attributes affect elaboration, not the stated equality.
No mathematical defect was found in this small source argument. The imported
residue proof has a [separate source review](../compact44-symbolic-k-horner-mathematical-review/README.md).

[`audit.py`](audit.py) checks the retained source, successful compiler log and
receipt, live alias and residue object hashes, and the subsequent failed
unit-client receipt. The successful alias run exited 0 and reports
`propext`, `Classical.choice`, and `Quot.sound` for both declarations. The
later `AliasControllerUnit` attempt exited 1 with excessive kernel memory;
its self-referential axiom report is failed-declaration recovery, not a unit
proof. The audit rejects optimized Python and does not execute Lean.

This is a single-author, point-in-time source/artifact review with inherited
project, package, transitive and dynamic provider limitations. The alias
equality and residue do not supply a compiled controller-unit client, identify
retained coefficient bytes or a displayed equation, establish the actual
rank variation, or prove an iPRA theorem. The live `/tmp` objects are required
to repeat the object checks.
