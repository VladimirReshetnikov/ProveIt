# Adaptive canonical converse and current endpoint: exact staged plan

Read-only planning checkpoint, 2026-10-26. The accepted
`NativeAdaptiveGraph` packet remains unchanged. No Lean process, prerequisite
refresh, cache copy, incoming program, or equation-metric audit was run here.
This supplements the frozen `adaptive-graph-converse2011-proposal.md`; it
narrows its proposed canonical import and authenticates both later closures.

## 1. Smallest next coherent leaf

Propose `NativeAdaptiveCanonical.lean` and focused Checks, importing exactly:

```lean
import DiophantineConsistency.NativeAdaptiveGraph
import DiophantineConsistency.Carrier66Source
```

The principal constructor can use the weaker `PortBox` plus `beta >= 15`:

```lean
theorem canonical_adaptive_zero (p : Fin 4 → ℤ)
    (hp : NativePellBootstrap.PortBox p) (hbeta : 15 ≤ p 0)
    (v : Fin 15 → ℤ) (hv : ∀ j, 0 < v j)
    (hc : Carrier66.Canonical p v) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧
      NativeAdaptiveGraph.value p x = 0 ∧
      x 0 = v 0 ∧ x 1 = v 1 ∧ x 2 = v 2 ∧
      x 3 = v 4 ∧ x 4 = (Carrier66.core p v).delta * v 6 ∧
      x 5 = v 7 ∧ x 6 = (Carrier66.core p v).X ∧
      x 7 = (Carrier66.core p v).Y ∧
      x 9 = v 11 ∧ x 10 = v 12 ∧
      (NativeAdaptiveGraph.core p x).y = v 13 ∧
      (NativeAdaptiveGraph.core p x).rank = (Carrier66.core p v).rank
```

The displayed signature is a proposal, not a compiled declaration. Its
canonical premise is appropriate for this construction only. The public
reverse client from an arbitrary positive Carrier65 zero must retain:

```lean
theorem carrier_zero_adaptive_zero (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : Carrier65.value p v = 0) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧
      NativeAdaptiveGraph.value p x = 0 ∧
      x 0 = v 0 ∧ x 1 = v 1 ∧ x 2 = v 2
```

`Carrier66.positive_zero_restores_canonical` derives the positive parent
from this actual zero. The six `PortBounds` fields are beta>=31, K>0,
0<MC<beta, and beta<MF_source<2beta. They imply `PortBox` and beta>=15;
neither a weaker Interface nor bare positivity replaces those fields.
There is no supplied source, restored index, power, parity, or rank-bound
premise in this Carrier65 client.

## 2. Remove the shifted-source adapter from the canonical import

The earlier proposal used `NativeShiftedSourceAdapter.source_old_z_gt_one`.
That works, but unnecessarily brings its complete current endpoint and
three additional legacy/adapter modules into this first construction.
The following source-bound proof already lies in `Carrier66Source`'s imports.

Let `n = Carrier66Source.sourceNat p v`. Its `sourceNat_pos`,
`sourceNat_rows`, `sourceNat_cast`, `sourceQ_eq`, and `nativeRank_eq` all
refer to the same canonical parent. Write `q = sourceQ p n`, `w = n 10`.

1. `NativePellScaleBounds.source_q_cube_dvd_X p hp hbeta n hn hrows`
   proves `q^3 | n 21`. Since `n 21>0`, `Nat.le_of_dvd` gives `q^3≤n 21`.
2. `NativeBinaryScale.source_X_eq_q_mul` proves `n 21=q*w`.
   Positivity of J and beta gives `q>1`; cancel the positive q in the
   inequality to obtain `q^2≤w`, hence `q<w`.
3. `NativeSourceMask.source_gap_bounds` gives `C>0` and `F=n 1<q`.
   `NativeSourceWindow.source_transport_identity` gives
   `(K+w)*C=F+(n 3-1)*(q-1)` over naturals, with K interpreted by toNat.
   If `n 3=1`, its right side is F, while its left side is at least
   `w>q>F`, a contradiction. Thus `n 3>1`, and the cast identity gives
   the parent's old `z=v 3>1`.

These APIs need only the displayed PortBox/beta bound and an already proved
positive old source. They do not need the finite mask Interface, MC mod4,
or the shifted source theorem. Applying them here is noncircular: the
canonical parent gives every old source row before any adaptive witness is
chosen. They must not be used as assumptions in the adaptive-zero forward
bootstrap, which is already separately proved in `NativeAdaptiveGraph`.

## 3. Exact witness map and bounded first index

Set `B=Carrier66.core p v`, and abbreviate the positive parent coordinates
as J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gammaOld in their literal Fin15
order. Then X=q*w, Y=q^3*s, E=XY, k=eta+zeta, c=kY+eta,
ell=XkY^2, R=B.rank. Define b=q*(z-1); the preceding bound gives b>=q>=2.
The parent's W=1 transport yields the graph's exact `Bt=(q-1)*b`.

Use the actual source's `NativePellFirstIndex.source_first_pair`:
it returns `r0>=12`, `R.toNat=2*r0+1`, and
`k=2*Pell.yn_(2*firstQ(n)+1)(r0+1)`. Here firstQ(n)=XY^2, by the
literal restored source fields. Put m=r0+1; then m>=13 and `2*m=R+1`
after the justified positive-rank integer cast. In particular, no arbitrary
Pell index or unproved oddness premise is introduced.

`NativeAdaptivePowerProjection.first_difference_four` now proves
`4*X*Y^2 | k-R-1`. The canonical index equation independently gives
`k-R-1=E*h>0`. Choose integer l>=1 with

```
k-R-1 = 4*X*Y^2*l.
t = 4*q^2*w*s*l.
```

No division is used in t's definition. Substitution of X=q*w and Y=q^3*s
gives `k-R-1=(q^2*Y)*t`. Since q>=2 and w,s,l>=1, t>w. Also
k=R+1+E*h>E, while E>=Y>=s, so k>s without another growth estimate.
The positive first norm tau^2=1+ell*(ell+k) gives tau>ell.

With `Wfirst=(q-1)*k+1`, choose

```
rAdaptive = Wfirst*b + tau - ell - k - s
uAdaptive = y - B.V
gammaAdaptive = gammaOld - w + t
x = [J,F,alpha,f,B.delta*i,T,X,Y,rAdaptive,eta,zeta,uAdaptive,gammaAdaptive].
```

Here rAdaptive>0 because Wfirst>=k+1, b>=2, tau-ell>=1, k>s.
For uAdaptive, the canonical source's positive slots26 and27 give V>0
and y^2-V^2>0; the positive parent ordinate y then gives y>V.
Gamma positivity follows from t>w. All other thirteen coordinates are
unchanged positive fields or positive products. The i coordinate is
**B.delta*i**, exactly the canonical ordinary-source multiplier.

The four required literal identities are:

```
firstZ = q^3*(q-1)*tau
Dstar  = q^2*Y*B.D
Fs     = 1
Fa     = 1.
```

The first two follow from the chosen rAdaptive/t and the exact transport;
the canonical P=Q=1 give A0=A1=0. The last two use
`Carrier66Source.canonical_strong_error`,
`f^2-1=B.delta*i^2*c^4`, and the parent's U=1 with
`B.S=B.delta*i*c^2`. The graph's signed cut equivalence then gives value0.
This is an existence map preserving the listed visible fields and rank;
it is not a pointwise inverse on arbitrary private source coordinates.

## 4. Separate generic/current equivalence leaf

After the canonical pair freezes, propose `NativeAdaptiveCurrent2011`
and Checks with only:

```lean
import DiophantineConsistency.NativeAdaptiveCanonical
import DiophantineConsistency.NativeOrdinarySourceConstruction
```

The generic statement keeps all three interfaces explicitly:

```lean
theorem positive_zero_iff_carrier (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF)
    (hMC4 : MC % 4 = 2) (hp : Carrier65Witness.PortBounds p) :
    (∃ x : Fin 13 → ℤ, (∀ j, 0 < x j) ∧ NativeAdaptiveGraph.value p x = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧ Carrier65.value p v = 0)
```

Forward: accepted Graph.positive_zero_source using hi.portBox, hi.width,
hi.beta, then `NativeOrdinarySourceConstruction.source_constructs_carrier65`
using hi and hMC4. That existing theorem rebuilds private Pell witnesses;
the adaptive private f/i need not be preserved. Reverse: the first leaf's
arbitrary-positive Carrier65 client using hp. MvPolynomial versions use
the two existing evaluation identities, not another evaluator.

For the actual current polynomial set
`currentPolynomial := NativeAdaptiveGraph.polynomial
  (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))`.
Discharge hi by `CurrentWindowCarry2011.interface`, hMC4 by
`CurrentMasks2011.lowPort_four`, and hp by
`CurrentCarrierArithmetic2011.portBounds _ CurrentKernel2011.K_pos`
with the ordinary natural/integer cast. The width remains 47*2011=94517;
the fourth port is highPort+beta exactly once. Obtain
`PositiveZero currentPolynomial ↔ PositiveZero CurrentPolynomialWindow2011.polynomial`,
then the accepted `CurrentPositiveZero2011.positive_zero_iff_not_conZFC`
and `no_positive_zero_iff_conZFC` give the actual external equivalences.
No Bridge placeholder, internal HA claim, historical coefficient tuple, or
new 88/51 metric certificate is part of either proposed pair.

## 5. Complete current source/object authentication

The new audit script was fully read before its sole execution. It only
reads metadata/source/object bytes and writes its own new JSON. The exact
import DAG is recomputed from source, including implicit Init. All selected
source hashes, original accepted object hashes, selected private-cache
object hashes, and every named external source/companion hash agree.

| Proposed stage | Existing custom | External names | External companions |
|---|---:|---:|---:|
| Graph + Carrier66Source, canonical pair | 75 | 38 | 114 |
| Above + NativeOrdinarySourceConstruction, current pair | 376 | 64 | 192 |

The second count excludes the not-yet-written Canonical main. Once that
main is independently accepted, its second-pair dependency count is377.
No Checks module belongs to either dependency count. All25 overlapping
modules agree in both source and object hashes;1,438 distinct observed
paths were rehashed. There is no unknown custom import or external name.

Preferred accepted providers:

- Graph ROOT `/tmp/native-adaptive-graph-root-udoy897i/lib` supplies36
  existing modules. Its ROOT JSON SHA is
  `be6d8ffe03204ca88e739bac4df4f44e39f96748b5ce81cc5672e287de40b4c7`.
  Graph source SHA `4b0e17f6e72a179c95450500bea12dd6fd770fb2a76ee5b2652c3080ff1413fc`,
  object `fe1f2ef3f8fd2e2cc9668896e9d4a0cd1de67a93aeef523d71abf166be08a7e1`.
- Ordinary ROOT `/tmp/native-ordinary-source-root-7cz0jxs2/lib` supplies
  the other39 canonical modules, or340 for the complete current union.
  ROOT JSON SHA `6c1fec344ba36d5f65db8aeaab0d20e4c70af88320ebdea5dc936a400d33cdbf`;
  Ordinary source SHA `95e7a8cd4d2dd8f64554cbd9273d96e9629d12583f111cc0b89bee325712838b`,
  object `67c28fd51812ecf959df72aaa46cbdaa243ea629c860ffd57fe5808fe6fc49d8`.
- `Carrier66Source` source SHA
  `c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388`,
  object `8468f6ebb7a79d0ed128630c4c6bc314206a99d02fc5e53a0190b3b1e44f6dfc`.
- `NativePellScaleBounds` source SHA
  `9a2716b017ebf1fd35042e233a165e80d44924c1a6ce09bb6cbe7f37e1b365b3`,
  object `50cee7b7f2c94cb48f7988f46c5faed48abf5fdd4612180930619a499c63d72f`.

The complete paths/hashes/topological lists for all376 custom modules,
all64 external names and192 companions, both exact input inventories and
the Lean4.32 executable are in `adaptive-canonical2011-cache-plan.json`,
SHA `e4f5488109fb5fcb719352e0c4af1043b7446c2928adedb8f2793a059155012a`.
Its audit script SHA is
`334041dbc3cab28b40438d7d851f039661a609cafbba5a46453c679d46df4ad4`.
The JSON covers the full current union and explicitly records the smaller
canonical subclosure, rather than authenticating representative modules.

Package internals are inherited authenticated boundaries, not a new
whole-package/whole-native replay. No Foundation source is selected for
refresh and no prerequisite needs a fresh build. Planned execution after
separate approval is two private regular output objects per pair, fresh
main then Checks, Lean4.32 `-M6000 -j1 -DElab.async=false`, a512MiB reserve,
full source/driver read, and retained failed attempts. This note authorizes
no execution; all frozen Graph and parent files stay unchanged.
