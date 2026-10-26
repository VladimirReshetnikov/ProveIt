# Reverse construction: clauses, power dimensions and orbit transport

Date: 2026-10-26. ROOT read all six new source/check files and the two
agent author receipts before fresh replay. All six final bounded builds
passed. This review leaves the full arithmetic converse open.

## Exact sources

Paths are relative to `Lean/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentWordClause2011.lean` | 180 | `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc` |
| `CurrentWordClause2011Checks.lean` | 81 | `68de30948d89ff90409aa6cf1a5c49c7d5ee81661347c9bcca775a7440041615` |
| `WangTiles942PowerDimensions.lean` | 64 | `1021a39e8106c9a493986ee72aa0d2f85addff0a2d3ee822ca44a8a6441ae283` |
| `WangTiles942PowerDimensionsChecks.lean` | 51 | `89ec6c7ca99cecb41fed606f4db6a455589fd5f0b626330924e5265d70275c25` |
| `ControllerOrbitTransport.lean` | 108 | `4cd2008e9489074c1a83e9321dde3ef6b8e02b38561bec4511eee9ef762918af` |
| `ControllerOrbitTransportChecks.lean` | 97 | `817774226b87003323581361fcdc0700f6aa663071fa7aaf859432178fab1874` |

ROOT independently reviewed the new clause composition by
`controller_certificate`, while disclosing authorship of its earlier
literal clause and carry-composition prerequisites. The reflected
geometry, physical permutation and word/cell construction prerequisites
have separate earlier reviews. ROOT authored the power-dimension
composition and its geometric prerequisites; that part is an author
self-review and has a separate independent peer receipt. ROOT authored
neither the new orbit transport nor its interval prerequisite, both by
`circuit_reduction`.

## Proved scope

The actual reflected clause equals `2^45+2+localDigit(a j,1)`, retaining
the bare selector1 collision and permitting arbitrary numeric controls.
For Boolean controls, the proved physical count one resets every carry
in fields0..1004, for every binary phase. For whole-cell displacement
`47*(2011*s)`, the clause's temporal source is absent. The actual
recurrence therefore gives that exact normalized digit and zero outgoing
carry. Its actual high-mask digit passes. Its positivity and slack also
prove `0<F<radix^(N*2011)-1` for the same constructed normalized word,
with no supplied positive F, global mask, matching or controller premise.
The checks retain non-Boolean raw controls, selected physical1, N=1,
many-period subtraction, phase46, zero stride and the literal transport.

The power-dimension composition combines the actual canonical quotient's
marked and unique-Start properties for every independently sufficiently
large width and height. Explicit positive exponents meet arbitrary
independent dimension bounds for every base p>1. The word retains its
product modulus `p^rw*p^rh`; equality to `p^(rw+rh)` is returned explicitly.
This avoids rewriting dependent nonzero instances. Geometry needs no
prime, coprimality, controller or desired-uniqueness premise. Checks cover
composite bases, T=0 arithmetic, independent auxiliary-base bounds, base1
failure and the full conditional machine-halt endpoint. No halt at0 is
asserted. Development attempts to rewrite the dependent modulus failed;
the final product interface preserves the same mathematical equality.

The orbit packet constructs the image of the actual target interval under
an explicit coordinate injection. It proves cardinality and transports
any additive affine weight formula. Multiplication by C0 descends through
`ZMod.lift`, making coordinates modulo T additive modulo C0*T. The integer
sum is congruent to `a+C0*u.val`, with C0=0 and T=1 retained. A coordinate
injection and weight formula are structural premises; a desired subset is
never supplied. Checks include nonidentity reindexing, negative integer
representatives, wrap, modulus multiples and cardinality collapse without
injection. Actual power-orbit/LTE/CRT identification remains open.

## Fresh replay evidence

Each main and its checks ran sequentially using `lake env lean -M6000 -j1`
and declared `Elab.async false`, writing their named objects. Existing
prerequisite objects were reused. No full closure or umbrella rebuild is
claimed. All main logs were empty and all23 axiom reports were standard:
11 clause,3 dimension,9 orbit. The clause/orbit objects match their authors'
final objects. The dimension peer independently rebuilt both targets in
an isolated overlay and obtained byte-identical objects.

| Root log | SHA-256 |
| --- | --- |
| `/tmp/current-word-clause2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-word-clause2011-root-checks.log` | `3485839f5869eb2715766c8988d98fb082d1bd018807f7649782f45853804799` |
| `/tmp/wang-tiles942-power-dimensions-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-tiles942-power-dimensions-root-checks.log` | `d3ed29a1e897a791d6188e51c37ca64e04281625338f4dc964d61701b2315f42` |
| `/tmp/controller-orbit-transport-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/controller-orbit-transport-root-checks.log` | `fd539991cce47a40f6e3be3f01c96fd67db6c75418e6b96e5cd9fcc73dddd196` |

There is no `sorry`, `admit`, `native_decide` or new axiom in the reviewed
sources. The agent author receipts disclose prerequisite authorship and
development failures. Equation display, decimal numeral, fixed coefficients
and toolchain are unchanged. Whole masks, stronger boxes, actual orbit
classification, safe rank mutations, positive polynomial witnesses and
internal-ZFC derivation remain necessary.
