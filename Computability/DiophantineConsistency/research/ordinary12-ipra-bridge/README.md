# Twelve-variable ordinary-norm internalization: isolated residue prototype

**The fixed ports are different.** The ordinary 12-variable candidate uses
the complete compact44 tuple with `β = 2^590069 − 1`; the audited
13-variable 2011 endpoint uses `β = (2^47)^2011 − 1 = 2^94517 − 1`.
They are not interchangeable. Binding all four compact44 ports and proving
the corresponding internal checker/calibration is a separate prerequisite;
the existing fixed-port 13-variable endpoint cannot be composed directly.

`Ordinary12Residues.lean` is a small finite `ZMod 4` prototype. In particular,
it checks that an even residue squares to zero, an odd `β` and odd `J` make
`q=1+βJ` even, and the ordinary merger factor avoids the negative unit when
its `bn` is even. The exact compilation of the copied bytes actually exited 0
in tool session `4748`; six axiom reports and source/object/compiler/direct
dependency hashes are in `prototype-observation.json`.

The prototype used a fresh isolated source/output directory with the pinned
Lean executable and the historical package-only overlay; no project object
root was deliberately put in `LEAN_PATH`. Its direct `--deps` output was
observed separately. This was not the guarded full-project paired workflow:
transitive package inputs, dynamic loads, inherited environment and temporary
mutations were not fully authenticated. The inherited Foundation build
wrapper's outer exit also remains unobserved. Lean's reported `propext`,
`Classical.choice` and `Quot.sound` are metatheoretic dependencies, not
object-theory axioms.

This finite residue calculation does **not** establish the 12-variable
model-level residual split, early rank recovery, rational integrality,
checker calibration, or existence of an iPRA proof. [PLAN.md](PLAN.md) gives
the next precise proof obligations and the source-pinned historical reuse
boundary. No large project rebuild was started while disk space was near the
existing reserve.
