# Read-only alternatives after the 13/75/96 unit sphere

This note records algebraic schedule comparisons, not new materialized
candidates, Lean proofs, or executed finite audits. All variables, fixed
ports and definitions below are those of the complete
[unit-sphere proof](thirteen-unit-sphere96/PROOF.md). Its frozen graph has
75 paid operations: 42 multiplications, 18 additions and 15 subtractions.
The factor degrees are `deg P=22`, `deg Q=18`, `deg U=48`, `deg Z=36`.

## Two valid but dominated schedule alternatives

1. Replace `(P*Q)^2+U^2+Z^2-3` by
   `(P*Q*Z)^2+U^2-2`. Integer squares summing to two must both equal one.
   Hence P, Q and Z are units. The retained exclusions `P != -1`,
   `Q != -1`, `Z != -1` force all three to one; Z=1 converts U to a
   square-coefficient Pell norm and excludes U=-1. Conversely the accepted
   zero forces all four factors to one. Thus the same positive assignments
   are zeros in both directions. Relative to the literal 75-row schedule,
   add one multiplication by Z, remove the Z square and remove one sum:
   74 operations, consisting of 42 multiplications, 17 additions and
   15 subtractions. Its degree is 152, from the nonzero leader of
   `(P*Q*Z)^2`; U squared has degree 96, so cannot cancel that leader.

2. Put `B=Delta*(b*i*c^2)^2`, so `Z=f^2-B`, and replace
   `Theta=Delta*(f^2-1)` by `Delta*B=S^2`, with `S=b*i*Delta*c^2`.
   Use `U'=S^2*(V^2-y^2)+y^2` in the same three-square sphere.
   The sphere and negative-unit exclusions force Z=1; then B=f^2-1,
   so U'=U. The converse follows by the same equality. This also preserves
   the entire positive zero set with identity maps. The existing
   `strong_term` row already computes B, so replace the Theta multiplication
   and delete the now-dead `f2minus1` subtraction. The proposed count is
   74 = 42 multiplications + 18 additions + 14 subtractions. Here
   `deg(S^2)=48`, `deg(V^2-y^2)=34`, and `deg U'=82`; its square has
   degree164, exceeding the other two squares and with nonzero leader.

Both 74/152 and 74/164 are dominated by the already accepted 13/72/124
equation at the same full coefficient tuple. Neither warrants a new
candidate packet. These counts concern a zero polynomial with its final
constant subtraction paid, not a differently counted equation with a
nonzero right-hand side.

## The unresolved signed-ordinate boundary

Replacing `L*V` by `V` in
`y=1+4*(b*(m-L*V*G)-G)` would delete one multiplication. Formal degree
bookkeeping gives `deg y=11`, `deg U=36`, and degree80 for the resulting
sphere, dominated by `(P*Q)^2`. This is only an unproved 74/80 lead.

The accepted `ThirteenLVCarrier.mixed_bounds` derives
`L != 0` and `abs V <= L*V <= V^2` from each actual positive zero.
Its `carrier_nonneg` and `subtractive_positive` use the lower bound
`abs V <= A` for the replacement carrier A, together with the derived
bound `abs y < 2*abs V`, to retain positivity of the altered m coordinate.
Taking A=V would need `abs V <= V` (equivalently V>=0; V is nonzero on
these zeros). No retained theorem proves that sign. In particular,
`V=f^2*L-c` with c positive is compatible algebraically with negative L
and V; the existing mixed-product argument deliberately accommodates
that branch. Merely retaining the polynomial substitution identity does
not prove the positive witness maps. This note supplies neither a complete
actual zero with V<0 nor a proof that such zeros cannot occur. Resolving
that sign or finding a different positivity-preserving map is required
before treating this as an equation reduction.

## Exact sources and scope

- `thirteen-unit-sphere96/polynomial.json`:
  `48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1`.
- `thirteen-unit-sphere96/PROOF.md`:
  `b2d4edb3ef89dcd3e4798400d8afe422b7c66552191d31f73c4f3e549bd56a42`.
- `../Lean/DiophantineConsistency/ThirteenLVCarrier.lean`:
  `d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02`;
  relevant declarations are `mixed_bounds`, `carrier_nonneg`,
  `subtractive_positive`, `bounds_of_normal_zero`, `positive_toOld`,
  `positive_toNew` and their accepted72 wrappers.
- `thirteen-lv-carrier122/CERTIFICATE.json`:
  `3b4e66705173eac73939971d166b5db70be467eb85b2ef7d1dde232ed799d118`;
  its README and complete graphs record the accepted 72/124 and 74/122
  tradeoff and the unchanged 47,313-byte ports.

No new code or incoming program was executed, no frozen file was changed,
and no internal HA/ZFC equivalence or global optimality is asserted here.
