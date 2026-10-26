# Finite carry and bounded Pell witnesses: independent root replay

2026-10-26. PASS at the stated leaf scope. Authors: controller_certificate
(carry), circuit_reduction (Pell). Root read all209/86 carry main/check lines,
all105/59 Pell main/check lines, both author receipts, the complete original
NativeCyclicCarry and Common.Pell prerequisites, relevant mathlib subtraction
and recurrence interfaces, and the dependency metadata before replay.

The carry proof is a monotone iteration from zero with a sum potential bounded
by `card(ι)*D`. It establishes equality at that exact step and persistence,
then derives the actual quotient/digit decomposition and resets. Its current
corollary uses D=57 and the unchanged radix47 raw envelope. Empty index types,
D=0, cyclic wraparound and nonunique carry assignments are retained. The
chosen witness uses no least-fixed-point existence theorem, although the
imported earlier module also contains an unused general lattice proof.

The Pell proof uses only indices0 through m² in a finite set of m² residue
pairs. Two equal pairs at s<t yield a divisible ordinate at t−s by the
exact subtraction identity, with `0<t−s≤m²`. The positive quotient in the
strong-seed corollary is derived from ordinate positivity, and the literal
integer norm preserves the coefficient `b*i*c²`. The rank specialization
binds c to the already fixed outer Pell ordinate. The modulus-zero control
correctly rules out removing the positive-modulus assumption.

The new private replay directory `/tmp/finite-carry-pell-root-peer-a7zrxc2t`
initially held just two authenticated custom prerequisites, NativeCyclicCarry
and Common.Pell. Both actual source/object pairs match the previously accepted
receipt pins. All four new leaves were compiled freshly with `lake env lean
-M6000 -j1` and async disabled, each checks leaf after its main. All exited0;
both main logs are empty. The twelve carry and nine Pell axiom reports contain
only standard Lean axioms, matching the authors' reports. All four resulting
objects are byte-identical to the authors' independently compiled objects.

| New source | Source SHA-256 | Fresh object SHA-256 |
|---|---|---|
| NativeFiniteCarry | `7c001a01899b691a3288586da781d3338307bd5fa8a8bb90e460e9399babd48a` | `4f524a64546064ab875f084363f60e6114a9157704f3e316cfcd755197777222` |
| NativeFiniteCarryChecks | `c4af30ec2a9f5c7407f083bb71e05302b8123f970cece36383d7184c775140d2` | `cddf87a6cec1d1e4bffc05d56186f286541562b28c604fdb9d8d974d3cabe500` |
| BoundedPellDivisibility | `4a11cced68e3c38747921c1fb9ed1244669862779e95f7dd7a232ae9aa81e69b` | `a846c93bf531eee33c48e32cc53a7f47795c238214c831facc6ed8be40eaeef2` |
| BoundedPellDivisibilityChecks | `6cdc93b9a2cf5294c12a64312a6f43a9f5898380d20c1616f8cc795f424e2ba3` | `1264369dfa4e00acce71f8e8a4488b56dab804b0034fdefaf19b8ae0b2a94759` |

The reused prerequisite source hashes are
`25c08e2b6b10e72fe9b3d4df81078e4e1e5ede8e3e94b9666dc5616dcfebc72e`
and `e5fdac7c9062eb7cbdaa5d649290fbac16c2415f1fbaf0ab3415454b55ec3560`;
their object hashes are
`37e63fd379abc9eeaad12f152925eb0a71aec671b7eeceb19c03759a5671d41b`
and `e6757e9422347464783c7eb98ab814ee4bc7929a18be07d026050532b0a717d0`.
No prerequisite, shared object or accepted source was overwritten; no full
dependency rebuild is claimed. These are bounded standard-arithmetic
constructions, useful for internalization. They are not yet encoded HA
derivations or a complete bound on every current-equation witness. The
frozen current construction and equation artifacts remain unchanged.
