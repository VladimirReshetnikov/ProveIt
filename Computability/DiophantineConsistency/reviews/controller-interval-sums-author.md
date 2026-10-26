# Modular interval subset sums: author receipt

Status: frozen, freshly checked. Author: `circuit_reduction`. This is an
author receipt, not an independent review. Only the new module, checks, and
this receipt were written; no existing source, shared document, or git state
was modified.

## Frozen sources

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/ControllerIntervalSums.lean` | 83 | `aecbb4d39a0f6efc6173d9f38ced30e131cff421dd89d5a747a1e94ba530461a` |
| `Lean/DiophantineConsistency/ControllerIntervalSumsChecks.lean` | 90 | `79668160d975e1e8b5bf6c872e24213cea3880af187e3b7bcc6560f5056efaf3` |

Direct imports are `Mathlib.Data.ZMod.Basic`,
`Mathlib.Algebra.BigOperators.Intervals`, and `Mathlib.Tactic`. No local
machine, kernel, controller, or arithmetic-front module is imported.
The relevant pinned API sources were inspected before implementation:

| Source | SHA256 |
| --- | --- |
| `.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean` | `9a57047615cf4231f3561aef5c75ededf5a6ed6559308f31e241d1d27b2bc00c` |
| `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Intervals.lean` | `c969bea5adca8855d8dd38d6cc80523edb8ee2fd41dcda77a7b47b09fa710570` |
| `.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Defs.lean` | `09489226154d6558ad44614501b55883f0dc31b4504f1bb29e6190b2df456bce` |

The complete ordinary controller section11 of
`research/padding-staircase-independent/PROOF.md` was read; its source SHA256
is `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
The packet formalizes its consecutive-coordinate equation only.

## Exact construction and scope

`interval start a` is the actual finite image of `Finset.range a` under
`j ↦ start+(j:ZMod T)`. For positiveT (expressed by `NeZero T`) and a≤T,
`interval_injOn` uses canonical values j,k<T to prove that image injectivity.
`interval_card` therefore gives exact cardinalitya, including intervals
crossing zero and the endpointa=T.

`interval_sum` proves

```text
sum (interval start a) = (a : ZMod T)*start + ((a*(a-1)/2 : Nat) : ZMod T).
```

The image sum is rewritten to the source range using that proved
injectivity. The constant sum and natural Gauss formula finish the proof.
The triangular number is computed over natural numbers before the cast;
there is no division by2 in the residue ring. Thus evenT is permitted.

For `h : Nat.Coprime a T`, `startFor a h u` explicitly multiplies
`u - triangular(a)` by the inverse unit `ZMod.unitOfCoprime a h`.
`startFor_equation` proves the exact coefficient equation by unit
cancellation, including the zero ringT=1. `targetInterval` is the actual
interval at this start, not a chosen or assumed subset. Its card and sum
are proved, and `exists_interval_sum` / `exists_subset_card_sum` expose
both the interval and general finite-subset interfaces.

The only target-subset assumptions are T>0, a≤T, and gcd(a,T)=1. No subset
realizingu is supplied as a premise. This does not yet identify the actual
B^kappa power orbit with coordinate residues, lift a target through C0,
perform CRT, choose the auxiliary Boolean bit, or transport this subset
to safe dummy positions. It does not assert the entire controller or
construct a positive polynomial solution.

## Focused controls

Checks cover the explicit wrapped set{4,0,1} inZMod5; the actual inverse-unit
start3 producing{3,4,0} with target2; empty intervals; full length4 inZMod4;
and a control showing that replacing natural triangular division by inverse2
inZMod4 gives the wrong result. Both a=0 and a=T=1 are tested atT=1.
ExceedingT is shown to lose cardinality. For noncoprimea=2,T=4, no interval
has sum0; a separate two-element subset{1,3} does. The latter distinguishes
failure of the interval construction from failure of all possible subsets.
The complete symbolic subset endpoint is also checked without any supplied
subset witness.

## Fresh validation

Both entire new sources were read before execution, and final changed
versions were reread. Builds were sequential and bounded with
`Elab.async false`:

```sh
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/ControllerIntervalSums.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/ControllerIntervalSums.lean
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/ControllerIntervalSumsChecks.lean
```

Final main: PASS,3.51seconds, peak3189200KiB, no Lean diagnostics.
Final checks: PASS,3.60seconds, peak3170032KiB, eight intended axiom reports.
`startFor_equation` uses `propext`, `Quot.sound`; the other seven use only
the standard three `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, new axiom, or `native_decide` was added. Existing mathlib
objects were reused; no dependency object was overwritten.

Development corrections were elaboration-only: annotate the image index
asNat rather than allowing inference asZMod; prove the concrete inverse-unit
example by its equation and unit cancellation instead of evaluating an
opaque gcd inverse; use the explicit natural-cast-self lemma for the full
interval check. Statements and mathematical assumptions were unchanged.
No failed elaboration result is used by the final successful checks.

| Output | SHA256 |
| --- | --- |
| `.lake/build/lib/lean/DiophantineConsistency/ControllerIntervalSums.olean` | `833345ce36bcab09fd09ddfa824c4afaca60de68d9bba90516cc246ffb585963` |
| `/tmp/controller-interval-sums-main.log` | `903a888577ded80f4d4e94a07793d8b8273a18608d22343262c1c87eb8b9aba6` |
| `/tmp/controller-interval-sums-checks.log` | `7d06234686f9dce16b5009496094f949e172079fdd0f6fec51239a98d419b73f` |
