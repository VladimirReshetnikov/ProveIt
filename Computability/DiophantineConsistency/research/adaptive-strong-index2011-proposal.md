# Literal adaptive strong norms: proposed exact main-index bridge

Read-only proposal. No new proof source, compiler, historical generator or
candidate evaluator was executed. The proposed next packet is
`NativeAdaptiveStrongIndex.lean` and focused checks, importing only the
frozen `NativeAdaptiveRankWindow`. It would prove the next soundness step
for the unrestricted-J thirteen-positive graph, without a restored source
or canonical witness premise.

## Exact cuts and the missing adapter

The inspected complete `p13_free_J.json` has positive inputs
`J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma`. Keep its exact cuts:

```
k = eta+zeta, c = kY+eta, a = Y(X+1), A = a+2,
Delta = A^2-1, I = i*c^2, Q = Delta*(f^2-1),
V = f^2*(c*T-R)-c, y = V+u,
Fs = 1+I^2-Q, Fa = Q*V^2+(1-Q)*y^2.
```

The graph computes `Fa` as `y^2-Q*(y^2-V^2)`, exactly the same integer
polynomial. Its `r0` is `k-R-1`; its positive input `r` belongs to A0 and
is a different quantity. The target uses `ports 3` already shifted once.
The input multiplier `J` remains unrestricted and positive. In the
existing StepDown theorem, the formal parameter named `J` must instead be
instantiated with `R.toNat`; these two names must not be conflated.

RankWindow derives `c=yn_A(p)`, `A*(A^2-1)^2<c`, `2*p<c`, `2*R<c`,
and `R>0`, directly from the literal A0/A1 cuts and the port box. The two
additional hypotheses for this packet are **literal** `Fs=1` and `Fa=1`.
They are not replaced by assumed source equations. The already separate
unit-factor theorem can later derive these from the complete product
zero, but no such graph-binding or product endpoint is required here.

`source_index_of_strong` needs `V=j*c-R` and `V=o*f-c`. The second is
immediate with `o=f*(c*T-R)`. The first is not immediate: the literal
expression initially gives `V=-R*f^2` modulo c. The required new adapter
is `c^2 | f^2-1`, derived from the ordinary strong theorem, before index
recovery. Cancelling Delta from the strong norm would be unjustified.

## Noncircular proof

1. `Fs=1` gives `I^2=Delta*(f^2-1)`. Since `i,c>0`, its left side is
   positive; since `f>0`, this excludes `f=1` and gives `f>=2`. Cast to
   the exact natural strong norm only after recording `A>=2`, `f>=1` and
   all relevant `Int.toNat` equalities.
2. Apply `Jones1980.relaxed_aux` to the classified main pair and the
   already-derived large-c bound. It returns an m with
   `f=xn_A(m)`, `p|m`, `c|m`, and `i*c^2=Delta*yn_A(m)`. It assumes
   neither `p=R` nor an auxiliary congruence.
3. `Pell.y_dvd_iff hA p m` and `c=yn_A(p)` give `c|yn_A(m)` from
   `p|m`. Write `yn_A(m)=c*t`. `Diophantine.χ_sq hA m` then gives
   `f^2-1=Delta*c^2*t^2`, hence `c^2|f^2-1`. This is a consequence of
   integral Pell classification, not cancellation in the original norm.
4. Set `S=c*T-R`. As `T>=1`, `c>2R` gives `2S>c>0`. Since `f^2>=4`,
   the identity
   `V-c=(f^2-4)*S+2*(2S-c)` proves **V>c>0**. Thus the actual graph
   ordinate `y=V+u` is positive and `o=f*S>0`. No sign of V is assumed.
5. Write `f^2-1=c^2*h` over the integers and set
   `j=f^2*T-R*c*h-1`. Direct ring identities give
   `V=j*c-R=o*f-c`. Because `j*c=V+R>0` and `c>0`, also `j>0`.
   Positivity of j/o is useful future data, but StepDown itself permits
   signed j/o and requires neither of these positivity assertions.
6. Replace Q by I² in `Fa=1`. This gives exactly
   `I^2*V^2-(I^2-1)*y^2=1`. Cast only positive `y` to its natural
   representative. Call `NativePellStepDown.source_index_of_strong`
   with target `R.toNat`, the unchanged actual f/i/c and signed V/j/o.
   Its main classification, large-c and both half-modulus premises are
   RankWindow conclusions. Therefore `p=R.toNat`, hence `(p:Z)=R`.

There is no new oddness hypothesis. The existing signed step-down proof
derives the auxiliary odd index internally; its `eq_of_residues` uses
both strict half bounds to remove the negative residue alternative.
There is no reconstruction of i by division by Delta. The same supplied
positive i, f, T, u and actual y are retained.

## Suggested precise interfaces

The following are proposed signatures, not already checked declarations.
Use natural parameters for the generic existing-Pell client and explicit
integer casts for the literal auxiliary expression.

```
strong_square_divisibility {A c f i p : Nat}
  (hA : 1<A) (hp : 0<p) (hcp : c=Pell.yn hA p)
  (hi : 0<i) (hf : 0<f)
  (hs : (i*c^2)^2=(A^2-1)*(f^2-1))
  (hbig : A*(A^2-1)^2<c) : c^2 | f^2-1
```

For the next helper abbreviate integer
`Delta=(A:Z)^2-1`, `Q=Delta*((f:Z)^2-1)`,
`V=(f:Z)^2*((c:Z)*T-R)-c`, `y=V+u`:

```
literal_index_of_strong {A c f i R p : Nat} {T u : Int}
  (hA : 1<A) (hp : 0<p) (hR : 0<R)
  (hcp : c=Pell.yn hA p) (hi : 0<i) (hf : 0<f)
  (hbig : A*(A^2-1)^2<c) (hpc : 2*p<c) (hRc : 2*R<c)
  (hT : 0<T) (hu : 0<u)
  (hs : (i*c^2)^2=(A^2-1)*(f^2-1))
  (ha : Q*V^2+(1-Q)*y^2=1) :
  p=R and c^2 | f^2-1 and (c:Int)<V and 0<y and
  exists j o : Int, 0<j and 0<o and V=j*c-R and V=o*f-c
```

The public literal wrapper `adaptive_main_index_exact` should copy every
input/positivity/port/A0/A1 premise of `adaptive_early_bounds`, add only
`f,i,T,u:Int`, their four strict positivity assumptions, and the two
literal `Fs=1`, `Fa=1` equalities above. It should derive the first/main
classifications by calling RankWindow, not accept them as new hypotheses.
Its final result can be:

```
exists D:Int, 0<D and
  mainDstar q X Y k eta gamma (k-R-1)=q^2*Y*D and
  D=(Pell.xn (by omega : 1<a.toNat+2) R.toNat : Int) and
  c=(Pell.yn (by omega : 1<a.toNat+2) R.toNat : Int) and
  c^2 | f^2-1 and c<V and 0<y and
  exists j o:Int, 0<j and 0<o and V=j*c-R and V=o*f-c
```

Here a/c/V/y are exactly the integer graph cuts above. The optional
positive j/o conclusions bind two useful future rows but are not a full
source certificate. A focused test should expose the arithmetic adapter
with `f^2-1=c^2*h` and apply the public wrapper without a classification
premise. All public endpoints should receive axiom audits.

## Existing contracts and scope limits

* `Jones1980.relaxed_aux` (`PellRelaxedMain.lean:47`) has exactly the
  main classification, positive i/f, strong norm and large-c hypotheses
  listed above. Its conclusion includes p|m as well as c|m.
* `Pell.y_dvd_iff` (`PellMatiyasevic.lean:406`) transfers index
  divisibility to ordinate divisibility. `Diophantine.χ_sq`
  (`Common/Pell.lean:71`) supplies the additive natural Pell identity.
* `NativePellStepDown.source_index_of_strong` (line164) consumes the
  natural strong norm, signed auxiliary norm, positive y, exact two V
  equations, main classification, large-c and the two half bounds.
  Its internal call to `relaxed_aux` may duplicate that theorem's use in
  the adapter; it need not duplicate the underlying proof or introduce a
  new theorem assumption.
* `NativePellStepDown.source_index`/`signed_index_residues` internally
  use absolute-value auxiliary classification and `Jones1980.step_down`;
  the native wrapper does not need a new Pell theorem.

This packet would advance all-positive **soundness** of the actual
unrestricted-J thirteen-variable cuts. It does not yet bind every gate of
the complete product, prove the strong-factor converse from canonical
current witnesses, transfer the twelve-variable rational elimination,
restore the first index, recover X=2^R, eliminate the free-J factor3,
or restore all source rows. In particular historical completeness and
historical compact44 calibration are not premises. The historical metric
88/51 is not a newly certified current-port endpoint here.

## Source pins and prospective cache

| Source | SHA-256 |
| --- | --- |
| `NativeAdaptiveRankWindow.lean` | `f536f9324408a9660967e62baf10f01d85ed45ef7e4619e1c9f32710c6bd9b52` |
| `NativePellStepDown.lean` | `8fc2fb01654786bf8d7a9e104e84593dc43f74f73de53862ff411433fb482814` |
| `PellRelaxedMain.lean` | `8a18a6a953b8c529c35362c394e67065e943bbe17c2c22348d64d5eecbd898a4` |
| `Common/Pell.lean` | `e5fdac7c9062eb7cbdaa5d649290fbac16c2415f1fbaf0ab3415454b55ec3560` |
| `PellMatiyasevic.lean` | `a8ea2ddf5167a9163f3af19309eed96213848b632b58f8e5857535b3a1412341` |
| Complete `p13_free_J.json` | `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8` |
| Free-J ordinary `PROOF.md` | `4ce1e588973c7f703dea6a3c60ce747f6f0416544a522fe408d7d81a78a08dcf` |
| `ordinary-unit-products/ORDINARY13.md` | `de53d3340d41f0e24b1dfaaded5f166137d44b563f935fb6a4eddaf3bf395dbf` |
| `ordinary-unit-products/README.md` | `8dec2ab7b99257e97cbd3cb9e32f34dcd901e488727f9b7b837943bc5cf1c265` |

The companion `adaptive-strong-index2011-cache-audit.json`, SHA
`7af0cc253f39890be243192bdc7f427d0f4bd258835a8d641d312a02ed6b0055`,
rehashes all 29 prospective custom source/object pairs: the earlier28
plus the frozen RankWindow main. The exact22 actual external names and
66 object companions are unchanged. No new boundary or prerequisite
build is required. The provider is the final author RankWindow overlay
`/tmp/native-adaptive-window-o0wgi9j6/lib`; root's independent acceptance
was pending when this read-only audit was made. The inventory records
that distinction rather than calling this a new independent replay.

The only proposed future compilation is the new main/check pair under
the same pinned4.32.0 compiler, 6000 MiB/one-job/async-false caps and
512 MiB reserve. This proposal authorizes no compilation itself.
