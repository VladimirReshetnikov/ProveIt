# P64 converse witness-transfer inequalities

`P64ConverseTransfer` checks three reusable implications: an exact scaled
transport identity can be cancelled when `q` is nonzero, the first Pell
root exceeds `ell + s` under its stated size hypotheses, and the auxiliary
ordinate exceeds its root under its stated norm and order hypotheses. These
support P64's transport and positive `rho` and `e` coordinates. They retain
their hypotheses and do not by themselves obtain canonical halt data or a
positive graph zero. The existing canonical halt-data theorem already
provides the unscaled transport identity directly.

On 2026-11-04 Lean 4.32.0 checked the source with exit 0 and no warnings.
The transport theorem reported `[propext]`; the two order theorems reported
`[propext, Classical.choice, Quot.sound]`; none reported `sorryAx`. Use the
command in [`CONVERSE_ALGEBRA.md`](CONVERSE_ALGEBRA.md) with
`MODULE=P64ConverseTransfer` after the earlier local objects are built.

Source SHA-256:
`405fbdc1cad6f474bce927f6e69b6ef58dd74602b9fe5fa04d8ab415dc34fd42`;
object SHA-256:
`4b2149c22359cf3130679fa9eccc607f6cbfa8d786dbf219af45017e200f10ff`.
The direct `P64ConverseResidue.olean` input SHA-256 was
`47635958ea31acc2bebe56cfff2fa0de6053b78692237802f3fd230edf26096e`.
Complete ancestry of the temporary providers was not independently rebuilt
or audited.
