# Package 52's checked numerical ratio and literal finalizer

[`NativeNineRatio52.lean`](Lean/DiophantineConsistency/NativeNineRatio52.lean)
uses six natural witnesses `h,s,w,phi,i,j`. The witnesses `h,s,w,i` are
positive in the numerical ratio theorems; `phi,j` may be zero. Every register
independent of `j` is taken literally from the existing
`Jones1982.Nine.Vars.ofNat` interface with old `j=0`. The new registers are

```
Hnew = C+F*(B'+j*C)
Inew = (Gp^2-1)*Hnew^2+1.
```

Its four conditions are precisely the two square tests, `J | Q`, and the
positive margin. `exists_conditions_iff` proves their equivalence with the
old conditions after existentially quantifying the respective indices.
The proof transports the later square test as a predicate of the unchanged
`H`, using `RatioReparameterization.exists_old_iff_new`.
The explicit `toOldIndex` also comes with positivity and actual-H equality.

The numerical contracts are inherited exactly from the checked Jones ratio
theorems. Under `R,N>=8`, `0<b<=R,N`, positive `cap,h,s,w,i`, the new
conditions imply `N^2 | choose(2R,R)`, that `b` is a power of two, and
`8*g<cap`. Conversely those first two conclusions and the stronger bound
`32*g<cap` construct all six witnesses. The different constants in the two
directions remain explicit.

[`NativeNineFinalizer52.lean`](Lean/DiophantineConsistency/NativeNineFinalizer52.lean)
exports the computable integer `NewVars.finalValue`. It is exactly package
52's polynomial F9, with `Omega=J*m`, the unshifted offset `V0+V1`, and
the second-order majorant `V1=k*(8D^2-4D-1)*Gp*Hnew`.
`finalValue_eq` exposes the literal expanded norm formula.
`exists_finalValue_zero_iff_conditions` proves that a natural final witness
exists exactly when the four new conditions hold. All strict majorants,
`Q<V1`, and conditional radical separation are derived from the actual
register definitions and primitive input bounds. Neither `j`, `phi`, nor
the final witness `n` receives an extra positivity restriction.

`finalizer_sound` and `finalizer_complete` compose the literal polynomial
with the existing numerical ratio results. These close the package-52
arithmetic tail. The source packing, carry equivalence, fixed coefficient
binding, and calibration to ZFC refutations remain separate stages.

Both modules and their regression files compile. Checks include the
`phi=j=0` boundary, exact old/new H preservation, and an actual negative
margin assignment excluded for every natural final witness. Axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`.
