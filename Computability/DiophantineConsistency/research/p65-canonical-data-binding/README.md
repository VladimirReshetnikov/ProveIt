# Canonical halt-side converse for package 65

`P65CanonicalHaltConverse.halt_positive_zero` proves, for each model `V`
of IΣ₁ and each internal `T` with `ArithmeticCantor.first
(ArithmeticMachineRun215.run T) = 0`, the existence of fourteen strictly
positive coordinates at which the package-65 graph output vanishes. The
four ports are exactly the Lean expression
`CompactSymbolicPortProjections.portsInt (paramKernel rho)`; the theorem
has no extra port-equality or rank hypotheses.

The source adapts the halt-data extraction in the pinned `P72Converse`
source. It builds the tuple
`![j,F,alpha,z,f,delta a*i,auxT,X-q,Y,tau-(ell+sY),eta,zeta,y-auxw,gammaOld+t4-wX]`.
The crucial strong-norm coordinate is `delta a*i`. The companion lemma
packet proves the additional positivity of `j` and `X-q`. The other
coordinates and all five graph residuals are discharged using the canonical
halt data, the model rank/port bindings and `P65ConverseAlgebra.residuals_zero`.

This is a captured-provider check of the halt-to-zero **model direction**.
It is not by itself the reverse zero-to-halt direction, an iPRA derivation,
a correspondence proof for a displayed PDF, or a clean rebuild of current
source and transitive dependencies. External finite payload checks and the
source/object provenance of the baseline provider are separate obligations.
The theorem uses `P65GraphShim`, whose body is byte-identical to the pinned
canonical `P65Graph` after the documented import substitution. The arithmetic
shim's theorem bodies similarly match current `P72ConvArith` exactly after
its recorded import substitution; `check-shim.py` checks that correspondence.

Lean 4.32.0 compiled the theorem in actual session 44359 with exit 0, no
warnings, and `#print axioms` reporting only `[propext, Classical.choice,
Quot.sound]`. It used the already compiled companion objects listed below:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/p65-canonical-data-binding \
  research/p65-canonical-data-binding/P65CanonicalHaltConverse.lean \
  -o /tmp/P65CanonicalHaltConverse.olean
python3 -I -S -B research/p65-canonical-data-binding/check-shim.py
```

The compiler reports the direct imports `FreeJHaltModelZero`,
`CompactSymbolicPortProjections`, `P72ConvArithShim`,
`P65HaltPositiveCoordinates`, `P65ConverseAlgebra`, and
`Mathlib.Tactic.LinearCombination`; the first two come from the captured
flat provider. Rebuilding the complete dependency chain against the canonical
namespaced sources is required to remove the provider qualification.

```text
P65CanonicalHaltConverse.lean    3563e1fe528271f1bfebc38d83e810651d54a5adb702f02a4791d2d0e0863f74
P65CanonicalHaltConverse.olean   71f656cc6aa711bebcb22daa6b76a5ef9f6f31b6bd34d0bbaae70ce281805776
P72ConvArithShim.lean            b80e2933eb70db9341898a8cb7cc44be7296d78892dbcb5e72362bcc5346e890
P72ConvArithShim.olean           c5f4ab84861a86ce4fd3f9cc54210a74030bb101ead7edcb73fa05f06c0ba27a
P72ConvArith.lean                8427fda2445abaa8b87ae09ce8b99f4c2d5e332e5e14b7cb8b78c66c8dacbb75
P72Converse.lean                 61f0ca45d30e6269d001c33a1c9f3d85b3433ba0e28fcb95f7ddbd28e50a1a1c
P65GraphShim.lean                83e122b6ce29a9f9eeee5538ac0a8dff4962f470baef8f532e095fd0ed4399e1
P65GraphShim.olean               7bd2902eeffa586418aedef1aded667be68d32c0aeb6f3946a09d277db3dc19c
P65Graph.lean                    78a40f3bab902668e739e0068407808d094780409a002326f9dd745c53656338
P65ConverseAlgebra.lean          23d74ea1c92ec8d008069256719360ef2900639e8f89f5844a6ccd063a06566a
P65ConverseAlgebra.olean         609392439dd1fd47ac947fd380be490e9f8a43a33ca80c6b842db0116c33bac7
P65HaltPositiveCoordinates.lean  bfcecea98a254434a6bacd611e39fa99f0ef19857b5fd2150fdeae44c907802c
P65HaltPositiveCoordinates.olean f3a73c566b7099bb54f026d3658086efe14f1132407f210a186ef1ee623328f2
```
