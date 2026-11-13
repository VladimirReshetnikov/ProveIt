# P64 first-Pell quotient and positive gamma

`P64ConverseResidue.carrier_quotient` derives the P64 carrier quotient from
the first-Pell residue theorem. If `XY² ≥ 1`, `R = 2r + 1`, and
`k = 2 ycoord(r + 1, 2(XY² − 1) + 1)`, it constructs a model element `t`
such that `k = R + 1 + 4XY²t`. `positive_gamma` additionally takes a
positive `gammaOld` and constructs positive `gamma = gammaOld + 4Xt`.
These equations are the distinctive `Y²`-modulus gamma inputs of the
checked `P64ConverseAlgebra.residuals` theorem.

These first-Pell, index, lower-bound and old-gamma hypotheses are explicit;
this module does not itself extract them from the canonical halt data or
build an entire positive graph zero. The other first-root, transport, main,
strong and auxiliary identities remain to be bound to the same tuple.

## Observed check

Source SHA-256:
`b7c11fa0097e7a27d9191e80181954ece873d29b309ab067b9e3073d3209e271`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings, reporting
`[propext, Classical.choice, Quot.sound]` for both theorems and no `sorryAx`.
The command and captured path setup are those in
[`CONVERSE_ALGEBRA.md`](CONVERSE_ALGEBRA.md), with
`MODULE=P64ConverseResidue` after the two prerequisite objects were built.

The resulting object SHA-256 was
`47635958ea31acc2bebe56cfff2fa0de6053b78692237802f3fd230edf26096e`;
the direct `P64ConverseAlgebra.olean` input SHA-256 was
`823bebb12a1c46dfc4141ccabd386988d08293ca9456d63d9fe5354cd951f4f7`.
The selected `ArithmeticPellCongruences.olean` SHA-256 was
`ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664`.
The temporary project, package, dynamic and search-path ancestry was not
independently rebuilt or audited.
