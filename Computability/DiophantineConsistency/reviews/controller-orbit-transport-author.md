# Controller affine-orbit subset transport: author receipt

Date: 2026-10-26. Author: `circuit_reduction`. Both new sources are frozen after
full self-review and fresh bounded main/check builds. This is an author receipt,
not an independent peer review.

## Exact sources and dependencies

Source paths are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `ControllerOrbitTransport.lean` | 108 | 5380 | `4cd2008e9489074c1a83e9321dde3ef6b8e02b38561bec4511eee9ef762918af` |
| `ControllerOrbitTransportChecks.lean` | 97 | 4382 | `817774226b87003323581361fcdc0700f6aa663071fa7aaf859432178fab1874` |

The sole direct main import is the unchanged `ControllerIntervalSums`,
SHA-256 `aecbb4d39a0f6efc6173d9f38ced30e131cff421dd89d5a747a1e94ba530461a`.
I authored that interval prerequisite. I read the complete ordinary controller
section11 in `research/padding-staircase-independent/PROOF.md`
(SHA-256 `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`),
the full interval module/checks, and the relevant pinned mathlib `ZMod.lift`,
integer-cast congruence, additive multiplication-map and finite-sum APIs.
`Mathlib/Data/ZMod/Basic.lean` has SHA-256
`9a57047615cf4231f3561aef5c75ededf5a6ed6559308f31e241d1d27b2bc00c`.

The pinned toolchain is Lean4.32.0. `lean-toolchain` has SHA-256
`2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`,
and `lake-manifest.json` has SHA-256
`95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
Existing prerequisite objects were reused; no fresh replay of their closure is
claimed and no prerequisite bundle was overwritten.

## Constructed subset and proved formulas

For an arbitrary decidable domain `α`, an explicit injection
`e : ZMod T → α`, and the already-constructed target interval, define

```text
targetSubset e a h u = (targetInterval a h u).image e.
```

The positive modulus is expressed by `[NeZero T]`; `h : Nat.Coprime a T`
and `a ≤ T` are explicit. The subset itself is a definition, not a supplied
existential witness. `targetSubset_card` proves its cardinality is exactly `a`.
No surjectivity of `e`, ambient finiteness of `α`, or complete-orbit premise is
required: only the actual coordinate injection is used.

For any additive commutative monoid `R`, base `b : R`, additive homomorphism
`L : ZMod T →+ R`, and literal weight equation
`weight (e z) = b + L z`, `targetSubset_sum` proves

```text
sum_{x in targetSubset e a h u} weight x = a • b + L u.
```

It transports the finite sum using injection, distributes the affine formula,
and applies the exact previously proved interval sum. An existential wrapper
returns this very subset and its cardinality/sum; it does not ask the caller to
find a desired subset first.

`scaledCoordinate C0 T` constructs the additive map from `ZMod T` to
`ZMod (C0*T)` induced by `z ↦ C0*z` on integers. The relation needed for
`ZMod.lift` is proved because `C0*T=0` in the target modulus. Its value theorem is

```text
scaledCoordinate C0 T z = C0 * z.val    in ZMod(C0*T).
```

The representative is a natural value cast into the larger modulus; it is not
an unsupported ring homomorphism from `ZMod T`. Multiplication by `C0` makes the
formula invariant under a wrap by `T`. Both integer representatives and the
least nonnegative representative are proved to agree.

`targetSubset_modular_sum` specializes the affine theorem to
`weight(e z)=1+C0*z.val` and obtains the exact sum `a+C0*u.val` in
`ZMod(C0*T)`. `targetSubset_integer_sum` permits integer weights satisfying
only that residue formula and proves the corresponding ordinary integer sum
congruent to `a+C0*u.val` modulo `C0*T`. `exists_subset_integer_sum` returns the
concrete finite subset with both its size and congruence.

The definitions and conclusions retain `C0=0`: then the coordinate map is zero
into `ZMod0`, and the integer congruence modulo zero is an equality. `T=1`
also remains valid, including the coprime lengths `a=0` and `a=1`. No claim of
injectivity of `scaledCoordinate` is made at `C0=0`; the independent domain map
`e` is the map whose injection is required.

This completes only the ordinary controller's affine-coordinate subset step.
It does not prove that the actual powers of `B^kappa` enumerate the affine orbit,
LTE/order/CRT facts, the auxiliary epsilon choice, rank corrections, safe native
increments, or the equation converse. The explicit coordinate formula is a
structural interface still to be discharged for actual powers, not an assumed
target-subset conclusion.

## Fresh checks

I read both complete sources before execution and reread both final sources
in full after the corrections. The final sequential commands were:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ControllerOrbitTransport.lean -o .lake/build/lib/lean/DiophantineConsistency/ControllerOrbitTransport.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ControllerOrbitTransportChecks.lean -o .lake/build/lib/lean/DiophantineConsistency/ControllerOrbitTransportChecks.olean
```

Both sources set `Elab.async false`. Both final builds exited zero without Lean
warnings or errors. Main elapsed3.82 seconds, peak3192304KiB; checks elapsed3.69
seconds, peak3186932KiB. All nine printed axiom reports contain only the standard
`propext`, `Classical.choice`, and `Quot.sound`. Neither final source contains
`sorry`, `admit`, a new axiom, or `native_decide`.

The focused checks cover wrap and the failure of an unscaled representative
map to be additive, negative integer representatives, a nonidentity coordinate
injection with integer weights, adding full-modulus multiples to those weights,
`C0=0`, both lengths at `T=1`, collapse of cardinality without injection, and the
full symbolic endpoint without an assumed subset. The prior interval checks
already cover the length bound and the noncoprime-interval obstruction.

Development fixes were limited to elaboration of an integer-to-natural cast in
`ZMod.lift`, complete simplification of a zero multiplier, and explicit numeral
representative/cast simplification in focused checks. No theorem premise was
strengthened or desired conclusion assumed to bypass a failed proof.

| Output | SHA-256 |
| --- | --- |
| Main `.olean` | `83185f4ef37e02a556499c663f19a7f7b08248b02fbe2ff1e674d1bb9e3e618e` |
| Checks `.olean` | `1005af83c3a1d893840ef44e01ada1fc27a8a07dfc932687dc87d6941e97256c` |
| `/tmp/controller-orbit-transport-main-stage3.log` | `75d23f52b3fc5d500717ac1600fc508a6cfb79b9b3b684bb9f5e8b156b79eecc` |
| `/tmp/controller-orbit-transport-checks-stage3.log` | `82cb327580506ff97d953e196c9bd5c821aa3f7c0901f67dc29e13e7077b0291` |

Only the assigned new module, checks and this author receipt were added for this
implementation. No frozen source, shared status documentation, or git state was
changed.
