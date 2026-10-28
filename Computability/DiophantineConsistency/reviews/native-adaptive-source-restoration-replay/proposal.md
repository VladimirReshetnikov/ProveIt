# Restoring the ordinary source after adaptive power recovery

Read-only proposal, 2026-10-26. No new Lean source or compiler execution belongs
to this checkpoint. The first requested implementation is the positive scalar
recovery and complete 31-coordinate old-source restoration described below.
Literal graph binding and canonical completeness are separate next checkpoints.
No historical compact44 coefficient or cofinality assertion is used as a premise.

## Exact input and what is already proved

Keep the historical graph's positive input order
`[J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma]`, with four parameter ports
`[beta,K,MC,MF]`. `MF` is the source high port, already shifted once.
The literal cuts are

```
q=beta*J+1; C=q-F-alpha; k=eta+zeta; E=X*Y;
c=k*Y+eta; a=Y*(X+1); delta=(a+2)^2-1; H=4*a+3;
ell=X*k*Y^2; U=q^2*Y; v=k-R-1;
R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J;
Bt=(q*K+X)*C-q*F;
V=f^2*(c*T-R)-c; y=V+u; I=i*c^2.
```

The assumptions are only these definitions, positivity of all thirteen inputs,
`NativePellBootstrap.PortBox ports`, `beta=2^d-1`, `4<=d`, and the four
literal factor conditions `firstA0=0`, `mainA1=0`, `Fs=1`, `Fa=1`.
`beta>=15` follows from the displayed width, rather than being an additional
mathematical restriction. No restored source, parity, classified index,
divisibility of X, or deleted quotient is an input.

Accepted results, with the exact namespaces:

* `NativeAdaptiveCarrierBootstrap.first_carrier_integral_positive` gives
  positive integers `s,b`, a signed `tau0`, `Y=q^3*s`, `Bt=(q-1)*b`,
  `tau0^2=1+ell*(ell+k)`, and `0<|tau0|`.
  Its `transport_positive` gives `C>0` from this same `Bt`.
* `NativeAdaptiveRankWindow.adaptive_early_bounds` gives the large-c estimate
  `(a+2)*((a+2)^2-1)^2<c` and positive classified main root.
* `NativeAdaptiveStrongIndex.adaptive_main_index_exact` gives positive `D`,
  `Dstar=U*D`, both main coordinates at the actual target `R`, and positive
  `j,o` with `V=j*c-R=o*f-c`; it also gives `c<V` and `y>0`.
* `NativeAdaptivePowerProjection.adaptive_projection` gives the same first
  index `n>=25`, `2*n=R+1`, `k=2*yn_(2*X*Y^2+1)(n)`,
  `4*X*Y^2 | v` and `U | v`.
* `NativeAdaptiveMersenne.adaptive_q_power_radix` derives `X=2^R.toNat`,
  `q|X` and `q=(2^d)^N`, `N>0`, from the literal assumptions. The accepted
  fixed-width wrapper is `current_width_q_power_radix`, at `d=94517`.

These inputs are sufficient for every deleted source coordinate. The proof
does not need a further Pell-index or growth theorem.

## The remaining positive quotients

1. **Spatial quotient.** Obtain `X=q*w` from `q|X`. Since `q,X>0`, `w>0`.
   Retain the exact equality, not just a source-equivalent replacement.

2. **Index quotient.** For the recovered `n>=25`, use the existing generic
   `Diophantine.lt_yn_of_two_le` (also used by
   `NativeOuterSeedConstruction.exists_outer_seed`) to obtain `n<yn_P(n)`.
   Thus `v=k-R-1=2*(yn_P(n)-n)>0`. The already proved
   `4*X*Y^2|v` supplies a positive integer `h` with `v=X*Y*h`.
   Separately retain a positive `t` with `v=U*t`; this is not assumed equal
   to the source coordinate `h`.

3. **Transport quotient.** Let `A=(K+w)*C-F`. The same literal transport gives
   `q*A=Bt=(q-1)*b`. Define `z=A` nowhere: the correct quotient is
   `z=b-A`. Then the equality itself gives `b=q*z`, with no gcd import.
   Since `b,q>0`, `z>0`, and cancellation gives
   `(K+w)*C=F+(q-1)*z`. The old source coordinate is `zOld=z+1>1`.
   This derivation uses the first-carrier positivity, not a future native
   window or spatial-bound theorem.

4. **Ordinary main gamma.** Define `gammaOld=gamma+w-t`. Expansion of the
   literal `Dstar=U*D`, followed by cancellation of positive `U`, gives
   `D=X+a*c+H*gammaOld`. Its sign is not inferred from the definition.
   We have `a>X` because `Y>=1`; the existing large-c bound gives `c>a+2`,
   hence `c>X`. The main norm gives the exact identity

   `D^2-((a+1)*c)^2 = 1+2*(a+1)*c^2 > 0`.

   Since `D,(a+1)*c>0`, it follows that `D>(a+1)*c`. Therefore
   `H*gammaOld=D-X-a*c>c-X>0`, and `H>0` proves `gammaOld>0`.
   This avoids an extra predecessor-Pell identity. The arithmetic was also
   challenged independently by the controller agent, without compilation.

5. **The remaining witnesses.** Set `tau=|tau0|`, preserving the first norm
   and obtaining a positive source ordinate even when the first signed
   carrier root is negative. Keep the original positive `f,i,eta,zeta`.
   Use the existing positive `j,o`; put `g=y^2-V^2=u*(2*V+u)>0` and
   `I=i*c^2>0`. `Fs=1` gives `I^2=delta*(f^2-1)` and `Fa=1` gives
   `y^2-I^2*g=1`. No canonical multiplier divisibility is needed.

The adaptive `r` has already done its work in first-carrier positivity. It is
not an old-source coordinate and is discarded in this direction. No sign for
the original signed first-carrier root is asserted.

## Complete source and proposed first public endpoint

Use exactly `SplitCertificate59.sourceRows`, not the shifted report52 rows.
The restored integer vector, in its authoritative order, is

```
[ J,F,alpha,z+1,f,h,i,o,j,s,w,tau,eta,zeta,y,gammaOld,
  q^3,E,k+ell,c,a,X,D,c^2,q^2-1,f^2,V,g,I,I^2,delta ].
```

All 31 entries have just been proved positive. The 22 source equations reduce
to the following complete ledger; numbers are zero-based source row indices.

| Rows | Identity used |
|---|---|
| 0,1,2 | `q=beta*J+1`, the definitions of `q^2-1,q^3`, and `X=q*w` |
| 3,4 | `Y=q^3*s`, `a=E+Y`, and `E=X*Y` |
| 5,6 | `c=k*Y+eta`, `k=eta+zeta`, and `ell=E*k*Y` |
| 7 | `tau^2=1+ell*(ell+k)` |
| 8 | `D=X+a*c+H*gammaOld` |
| 9,10,11 | the definitions of `delta,c^2` and the positive main norm |
| 12 | `k=1+R+E*h` and `c*j-V=R` |
| 13 | the same `R` equals the literal target with once-shifted `MF` |
| 14 | `(K+w)*C=F+(q-1)*z`, with source coordinate `zOld=z+1` |
| 15,16,17 | `f^2`, `V=f*o-c`, and `g=y^2-V^2` |
| 18,19,20,21 | `I=i*c^2`, `I^2`, the strong norm, and `y^2-I^2*g=1` |

Proposed new pair: `NativeAdaptiveSourceRestoration.lean` and its Checks,
sole import `NativeAdaptiveMersenne`. Suggested public theorem
`adaptive_positive_source` retains the exact parameter/positivity list of
`adaptive_q_power_radix`, not a supplied scalar-recovery certificate. It returns

```
exists x : Fin 31 -> Nat,
  (forall j, 0 < x j) and
  (forall j, SplitCertificate59.sourceRows ports (fun j => (x j : Int)) j = 0) and
  (x 0 : Int)=J and (x 1 : Int)=F and (x 2 : Int)=alpha and
  (x 4 : Int)=f and (x 6 : Int)=i and
  (x 12 : Int)=eta and (x 13 : Int)=zeta and
  (x 21 : Int)=X and (x 26 : Int)=V and
  (x 14 : Int)=V+u and NativePellBootstrap.nativeRank x=R.
```

An internal recovered-coordinate ledger can expose `w,z,h,t,gammaOld,tau,D,j,o`
and their exact equations before filling the vector. Converting positive
integers to naturals is last; the ring ledger is checked over integers first.
If the proof exceeds a manageable leaf, split only the scalar positivity lemma
from the complete row map, preserving this full objective and premise list.
This endpoint supplies the missing source rather than assuming one.

## Next small graph/soundness binding, not part of that first pair

`NativeAdaptiveUnitFactors.product_one_iff` already excludes all four negative
units over arbitrary signed integers. It is generic; it has no Fin13 evaluator
or binding to the delivered graph. A new literal value/polynomial definition
must identify the cuts above with every node of the inert `p13_free_J.json`:
`F0=1+A0`, `F1=1+A1`, `Fa=y^2-delta*(f^2-1)*(y^2-V^2)`, and `Fs` as above.
The graph multiplication order is `Fs*(Fa*(F0*F1))-1`; associativity and
commutativity bind the existing unit theorem. It then gives all four actual
cut hypotheses from a zero, for every positive assignment.

After restoration, `NativeOrdinarySourceConstruction.source_constructs_carrier65`
is exactly the downstream map needed. It derives packing/population from the
newly constructed source and rebuilds private Pell witnesses; it does not
preserve the supplied ordinary `f` or `i`. It retains `J,F,alpha,zOld,w` and
uses the same rank. Its `Interface` and `MC%4=2` are discharged by the accepted
current2011 constants. Thus the forward actual-current implication needs no
new native calibration proof. A graph evaluator/whole-current-tuple audit is
still required before claiming historical 13/88/51 metrics at the current
47313-byte tuple. Nothing in this proposal establishes those metrics.

## Canonical completeness: a concrete separate route

Do not invert an arbitrary old source while pretending it contains `T`.
Instead, start with an actual current Carrier65 zero, use
`Carrier66.positive_zero_restores_canonical`, and retain that positive Fin15
parent. `Carrier66Source.source` then gives a proved positive ordinary source
while the parent still supplies `T=v 7`.

Let its block values be `q,X,Y,k,c,a,V,R,D`; the prospective adaptive inputs are
the same `J,F,alpha,f,T,X,Y,eta,zeta`, together with

```
iAdaptive = delta * iParent;
uAdaptive = yParent-V;
gammaAdaptive = gammaOld-w+t,       where U*t=k-R-1;
rAdaptive = ((q-1)*k+1)*b+tau-ell-k-s,
            where b=q*(zOld-1), Y=q^3*s.
```

The necessary positivity has an explicit noncircular route:

* `Carrier66Source.source_pos` gives `V>0` and `yParent^2-V^2>0`, so with
  positive `yParent`, `uAdaptive>0`. Its source multiplier is precisely
  `delta*iParent`; using `iParent` unchanged would be wrong.
* `NativeShiftedSourceAdapter.source_old_z_gt_one` supplies `zOld-1>0`
  from the actual interface. This uses the already restored canonical source
  only in the converse direction, never in forward bootstrap.
* `NativePellFirstIndex.source_first_pair` gives the first Pell pair and
  `2*n=R+1`. Applying the generic
  `NativeAdaptivePowerProjection.first_difference_four` gives
  `4*X*Y^2 | v`. The positive old source index row already gives `v>0`.
  Write `v=4*X*Y^2*l`, `l>=1`. With `X=q*w,Y=q^3*s`, the exact quotient is
  `t=4*q^2*w*s*l>w`. Hence `gammaAdaptive>0`, and substitution makes
  `Dstar=U*D` without assuming the adaptive A1 equation.
* The positive source first norm gives `tau>ell`. Its first index is at
  least thirteen, so monotonicity and `yn_P(2)=2*P` give `k>s`.
  Since `b>=q>=2`, `((q-1)*k+1)*b>=2*k+2`, making `rAdaptive>0`.
  Substitution then gives `firstZ=q^3*(q-1)*tau` and actual `A0=0`.
* The parent's canonical strong norm and source multiplier make `Fs=1`;
  retaining its exact `V=f^2*(c*T-R)-c` and ordinate gives `Fa=1`.

This is an existence map through the proved canonical parent. It is not a
pointwise inverse on arbitrary source private coordinates. It may reuse the
accepted canonical/source APIs; it does not require historical cofinality or
a new half-binomial construction. This route remains to be implemented and
audited separately before an equivalence claim.

## Source/cache scope and pins

The adjacent `adaptive-source-restoration2011-cache-audit.json` authenticates
all **33 custom source/object pairs**, **22 external source imports** and their
**66 object companions**, totaling 154 fresh hash observations. It adds only
the accepted Mersenne main to its authenticated 32-module parent. The accepted
provider is `/tmp/native-adaptive-mersenne-root-gah0zove/lib`; its ROOT receipt
is `1d94b06188bd72dbee9cf0cd495e3aeb2a8d6d671411d6e087729eea211bac21`.
No custom prerequisite or Foundation build is needed for the proposed first
pair, and no new external boundary is introduced.

The native endpoint later adds the ordinary-source closure. Its module-name
union with this narrow closure is 373 modules before new leaves and UnitFactors;
this is an inventory only, not a fresh authentication of all 373 modules.
The canonical reverse adds the already accepted shifted-source adapter and its
dependencies if its strict-z theorem is imported. Those later boundaries must
be reauthenticated before execution; this proposal does not authorize them.

Source pins for the exact generic unit theorem, ordinary/shifted source adapters,
canonical source, first-index theorem, source constructors, inert graph and
ordinary proof are included in the adjacent audit. Important fixed inputs are:

* Mersenne main: `555c1c5cf659d00499b1f7d0952483e9269754fd965f4f56aaa06d7e875a978c`.
* Ordinary source adapter: `95e7a8cd4d2dd8f64554cbd9273d96e9629d12583f111cc0b89bee325712838b`.
* Mersenne accepted object: `66e0eb6f9a8838fb32110c3046a5615418588b9237050aaf12c7551c3dc6020b`.

Any approved build remains two new private leaves with Lean4.32,
`-M6000 -j1 -DElab.async=false`, a 512MiB reserve, exact input authentication,
full source/driver reads, all attempt snapshots, and axiom reports. No shared
object, frozen proof, equation display or Git mutation is proposed.
