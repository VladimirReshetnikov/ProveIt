# Actual first/main index recovery: read-only proposal

27 October 2026. This is a proposed next internal arithmetic checkpoint,
not a Lean implementation or compilation claim. The frozen HalfIndex,
FirstNorm and all other accepted sources remain unchanged.

## Proposed pair and exact scope

`ArithmeticPellFirstIndex.lean` and focused Checks, with only imports
`ArithmeticPellHalfIndex` and `ArithmeticPellFirstNorm`.
Work throughout in arbitrary `V`, `[ORingStructure V]` and
`[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`. Every index, input and quotient is internal.
Write `X_j(a)=xcoord j a`, `Y_j(a)=ycoord j a`, `D(a)=delta a`.
Thus the base is `a+2`, and `D(a)+1=(a+2)²`.

The pair would contain a window-level theorem and a literal scalar client.
The latter removes the window premises using actual transport and port
inequalities, with no additional imports. Both derive the two indices;
neither assumes a source certificate, classified coordinates, oddness,
large-ordinate bound, half-window or desired index. The relation is
**`2*nFirst=R+1`, not `nFirst=R`**; the main index is `R`.

No power recovery, cofinal construction, canonical converse, complete
polynomial/source translation or final PA/HA consistency claim is proposed.

## Window-level public endpoint

For internal inputs `E,Y,k,eta,N,d,f,i,R,y,T`, put

```
Q = E*Y              B = 2*(Q-1)+1
a = E+Y             c = k*Y+eta
tau = E*N+k-R       I = D(a)*i*c*c
u = absdiff (f*f*c*T) (f*f*R+c).
```

Retained scalar premises are `0<E`, `2≤Y`, `0<k`, `0<eta`, `0<N`,
`0<f`, `0<i`, `0<y`, `8≤R`, and `R+2<E`. No positivity of `d` or `u`
is needed. `T` may be arbitrary natural-model data in this generic theorem.
The four literal additive norm premises are

```
tau*tau = 1 + Q*(Q+1)*k*k
d*d     = 1 + D(a)*c*c
f*f     = 1 + D(a)*(i*c*c)*(i*c*c)
I*I*u*u + y*y = 1 + I*I*y*y.
```

Proposed conclusion (`first_main_indices`):

```
∃ nFirst h,
  5≤nFirst ∧ nFirst<R ∧ 2*nFirst=R+1 ∧
  tau=X_nFirst(B) ∧ k=2*Y_nFirst(B) ∧
  d=X_R(a) ∧ c=Y_R(a) ∧
  (a+2)*D(a)*D(a)<c ∧ 2*R<c ∧
  0<h ∧ k=R+1+(4*E*Y)*h.
```

The optional transparent output `hSource=4*Y*h>0` gives
`k=R+1+E*hSource`. It restores the omitted positive source quotient;
it does not assert the other source rows. An odd witness for `R` follows
from the derived index identity, with justified subtraction `nFirst-1`.

## Noncircular proof route

1. Since `N≥1` and `E>R+2`, derive `E*N+k>R`, `tau>0` and the
   exact additive equation `tau+R=E*N+k`. No sign premise for the
   original integer expression is smuggled into the natural subtraction.
   `Q>0` justifies `Q-1+1=Q` and the literal FirstNorm parameter.

2. Apply `ArithmeticPellFirstNorm.solution_residues` at `q=Q-1`.
   The *same* derived index and quotient witnesses give
   `tau=X_nFirst(B)`, `k=2*Y_nFirst(B)`,
   `tau=1+2*Q*r`, `k=2*nFirst+4*Q*h`. There is no separately
   supplied first classification, parity or residue oracle.

3. Reduce the additive carrier equation modulo positive `E`.
   The two quotient identities give
   `k%E=(R+1)%E=(2*nFirst)%E`.
   Since `R+1<E`, canonical remainder and `mod_le` imply both
   `R+1≤k` and `R+1≤2*nFirst`. Hence `nFirst≥5` from `R≥8`.
   Since `Y≥2` and `eta>0`, `c>2*k≥2*(R+1)>2*R`.
   Thus the needed half-window is derived immediately, without an
   external exponential-growth estimate or an assumed main index.

4. Prove joint base monotonicity by a genuine represented Sigma1
   successor induction on the conjunction
   `X_t(a)≤X_t(b) ∧ Y_t(a)≤Y_t(b)` for fixed `a≤b`.
   Use both accepted successor formulas, positivity, and monotonicity
   of `D(a)=(a+1)*(a+3)`. This is internal induction at every `t`.
   Here `a≤B`, equivalently `E+Y+2≤2*E*Y+1`, follows from
   the guarded identity
   `2*E*Y-E-Y-1=(E-1)*(2*Y-1)+(Y-2)≥0`.
   The formal proof should use its additive form to avoid unguarded
   truncated subtraction.

5. Classify the actual main norm by `ArithmeticPellClassification.solution_index`,
   obtaining `d=X_p(a)`, `c=Y_p(a)` with `p>0` since `c>0`.
   If `p≤nFirst`, index monotonicity and base monotonicity give
   `c≤Y_nFirst(a)≤Y_nFirst(B)≤k<c`, impossible.
   Therefore `nFirst<p`, so `p≥6`.

6. Six literal recurrence steps yield the exact positive polynomial
   `Y_6(a)=32*A*D²+32*A*D+6*A`, where `A=a+2`, `D=D(a)`.
   Consequently `A*D²<Y_6(a)≤Y_p(a)=c`.
   The equivalent identity `Y_6=A*D²+31*A³*D+A³+5*A`
   was separately challenged algebraically; the first form is simpler
   for the nonnegative model. This finite calculation is not a
   standard-index induction or external growth theorem.

7. Invoke the accepted `ArithmeticPellHalfIndex.literal_half_index`
   with the *derived* large-ordinate and half-window bounds.
   It uses the full relaxed coefficient `D(a)*i`, derives both signed
   residues of the absolute difference and derives the auxiliary
   indices itself. Its conclusion is `d=X_R(a)`, `c=Y_R(a)`.
   `ArithmeticPellCongruences.index_unique` now gives `p=R`, hence
   `nFirst<R`. No circular use of `p=R` occurs in steps 1–6.

8. Finish `2*nFirst=R+1` without assuming `2*nFirst<E`.
   Write the actual division equation
   `2*nFirst=E*j+(R+1)` using the established remainder.
   Negative difference is already excluded by `R+1≤2*nFirst`.
   If `j>0`, then `2*nFirst≥E+R+1`; but `nFirst<R` and
   `R+1<E` give `2*nFirst<2*R<E+R+1`, a contradiction.
   Thus `j=0`. This explicitly excludes the positive `+E` alternative
   that a two-small-residues argument would fail to address.

9. Since `nFirst≥2`, monotonicity and the actual value
   `Y_2(B)=2*(B+2)` give `k≥4*(2*Q+1)>E`.
   The earlier quotient `k=2*nFirst+4*Q*h`, now with
   `2*nFirst=R+1<E`, forces `h>0`. No positive omitted quotient
   was assumed. All needed natural subtractions have explicit bounds.

## Literal scalar client: proposed within the same pair

This client supplies the preceding window from actual maintained fields.
Inputs are ports `beta,K,MC,MF_source` and the fourteen positive variables
`J,F,alpha,z,f,i,T,s,w,N,eta,zeta,y,gamma`, in exactly Carrier65's order.
Require only `0<beta`, `MC<beta`, `MF_source<2*beta` among the
natural ports; `K≥0`, `MC≥0`, `MF_source≥0` hold in the model.
Actual current PortBounds are stronger. Define literally

```
q=beta*J+1; X=w*q; Y=s*q³; E=X*Y=w*s*q⁴;
k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3;
d=X+a*c+gamma*H;
R=((q-1)*(q-F)+alpha)*(q²-1)+(MC+q*MF_source)*J;
tau=E*N+k-R; I=D(a)*i*c*c;
u=absdiff (f*f*c*T) (f*f*R+c).
```

Retain the four displayed actual norm equalities, and actual transport
in the subtraction-free form

```
(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q-1)+1.
```

This is the natural additive translation of
`(K+w)*(q-F-alpha)+(q-F)-z*(q-1)=1`.
No premise asserts a source row package, positive gap, window or index.
The client returns the same index/restored-quotient conclusion above.

Scalar argument: `q≥2` from positive `beta,J`. If `q≤F+alpha`,
the right side of transport is at least `(K+w)*q+q+1`, since `z,F≥1`.
Contradiction. Thus `q>F+alpha`, `C=q-F-alpha>0`, `q≥3`,
and every subtraction in the rank is now justified by an ordinary bound.
`q-F≥2`, `alpha≥1` imply the rank's leading coefficient is at least
`2*q-1≥q`; hence `R≥q*(q²-1)≥24` (the port mass is nonnegative).
For the upper bound prove this exact natural slack identity:

```
R + q³+q+1
  + q*(q²-1)*(F-1) + (q²-1)*(C-1) + (q+1)*(J-1)
  + J*((beta-MC-1)+q*(2*beta-MF_source-1)) = q⁴.
```

Every term is nonnegative; the strict port inequalities justify the
two port subtractions before expansion. The identity uses only
`beta*J=q-1` and `F+alpha+C=q`. It yields `R+2<q⁴≤E`.
Also `Y≥q³≥27`, so the generic endpoint's `Y≥2` holds.
This client is pure ordered arithmetic; it needs no extra import/provider.
If implementation size requires a helper split, report it before any
third leaf or import change; do not weaken this proposed public scope.

## Exact maintained binding and remaining caller obligations

`Carrier65.core` has `ell=E*k*Y`, so its first factor is exactly
`tau²-Q*(Q+1)*k²`. Its main factor is `d²-D(a)*c²`.
Its strict factor gives `f²=1+D(a)*(i*c²)²` after positive-delta
cancellation. Its auxiliary factor is the last displayed additive norm,
with signed `V=f²*(c*T-R)-c`; `absdiff` represents `|V|`, not its sign.
Thus the proposed client accepts the actual cut equalities, not historical
canonical-source data. Translation of an object-language polynomial zero
to these positive natural-model equalities is a later caller obligation;
no external Carrier65 zero theorem is imported as an internal oracle.

Current ports are `![beta,K,lowPort,highPort+beta]`, with
`beta=(2^47)^2011-1=2^94517-1`. `MF_source=highPort+beta` is
already shifted **exactly once** in the rank. No further `+beta` is added.
`CurrentCarrierArithmetic2011.portBounds` verifies the external current
inequalities; internal object-language constant/port certification is
outside this generic two-import pair. No historical compact44 tuple enters.

## Source and cache boundary

The accompanying read-only auditor and JSON pin all relevant sources,
source headers, exact accepted objects, manifests and actual first providers.
The HalfIndex ROOT packet is `de4ed3e2…`, provider
`/tmp/arithmetic-pell-half-index-root-qso00172/lib`.
FirstNorm uses the ROOT-accepted independent provider
`/tmp/arithmetic-pell-first-norm-peer-fr9mlele/lib` (commit `ad92d07c8a`),
peer packet `56ac5af7…` and ROOT authentication manifest `52c89d4c…`.
All 98 FirstNorm prerequisites already occur in HalfIndex's closure;
their complete source/header/object pins agree. Only these two accepted
main modules are added; Checks are evidence, not imported dependencies.

Exact proposed cached closure: **108 custom modules, 95 Foundation,
393 custom artifacts, 38 package boundaries, 114 total boundary artifacts
(38 primaries plus 76 companions), 507 actual first providers, zero refresh**.
The historical FirstNorm field named `external_companions=114` is retained
unchanged in its frozen plan; it counts total boundary artifacts.
All existing package/trace provenance qualifications remain inherited.
This reauthentication is not a fresh compilation of those prerequisites.

The read-only audit passed 4,153 pin observations across 1,064 paths.
It created no overlay and invoked no compiler or old builder.
Any later approved pair would use pinned Lean 4.32, `-M6000 -j1
-DElab.async=false`, a 512MiB reserve and fresh regular private outputs,
with both inputs and every failed attempt preserved. No new proof source,
compiler command, Git mutation or accepted-source edit occurs in this plan.
