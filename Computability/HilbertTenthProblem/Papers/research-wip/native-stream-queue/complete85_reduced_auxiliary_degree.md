# A complete universal polynomial in 85 operations and degree 155

The [complete source and receipt](complete85_reduced_auxiliary_degree.json)
give **85=47M+38A operations**, **18 strictly positive witnesses**, and
**uniform exact degree155** on the inherited valid fixed-program slices.
The entire supplied positive integer zero set is identical to that of the
[complete84 parent](complete84_scaled_strong_output.md), with ordinary input
and every witness unchanged.

One additional subtraction replaces the auxiliary factor's degree46
coefficient by a degree14 coefficient, reducing that factor's degree from
60 to28. This improves the existing85-operation degree point from175 to155.
The minimum operation result remains84/187; lower-degree choices such as
86/131 remain available. No unrestricted operation lower bound is claimed.

## 1. Actual source values and the one-gate change

Write

    a = R12, c = R10a, Delta = A = (a+1)(a+3),
    R = r_lhs, T = auxiliary_quotient,
    V = aux_u_rhs = c(Tf-1)-Rf²,
    S = aux_coefficient_root = Delta*i*c²,
    Qaux = R16 = S²,
    u = scaled_f_square = Delta*f²,
    Ns = norm_strong = u-Qaux.

The symbol Qaux is the actual auxiliary coefficient; it is distinct from
the leading-form abbreviation Q0 in Section4. The normalized strong
polynomial is

    Nstrong = f²-Delta*i²*c⁴,
    Ns = Delta*Nstrong.                                (1)

The old auxiliary factor is

    Na = Qaux*(V²-y_aux²)+y_aux².

Insert the new paid subtraction immediately before L17 and change L17's
coefficient operand:

```text
auxiliary_reduced_coefficient = scaled_f_square - A
L17 = auxiliary_reduced_coefficient * aux_square_gap
```

Thus the new auxiliary factor is

    Na_new = Delta*(f²-1)*(V²-y_aux²)+y_aux².             (2)

The existing `norm_aux=L17+aux_y2` row remains literal. Every other one of
the original84 definitions remains literal, including all seven finalizer
rows. There is no removed source row. R16 remains live as an operand of
`norm_strong`, and the supplied witness i remains live through that same
factor. All squares, products and norm comparisons retain their paid
producers. The source adds one subtraction and one computed register.

The helper authenticates the complete parent array, guards all actual
coefficient and discriminant definitions, and verifies both source graphs'
acyclic schedules, sequential operand availability and full liveness.
It does not treat c², Delta*c², f², V or a source coefficient as an unpaid
independent input.

## 2. Exact full-polynomial correction

Let P5 denote, for proof only, the product of the first, main, input, index
and transport factors. The paid full finalizers still compute

    F84  = P5*Na*Ns-Delta,
    Fnew = P5*Na_new*Ns-Delta.

No extra P5 register or alternative free finalization is introduced.
Using (1), the changed auxiliary factor obeys the all-value identity

    Na_new-Na = (Ns-Delta)*(V²-y_aux²).

Therefore the complete outputs obey

    Fnew-F84 = P5*Ns*(Ns-Delta)*(V²-y_aux²).              (3)

This is an identity over every commutative ring at identical supplied
coordinates. The polynomials themselves differ. The helper expands both
actual complete finalizers at the five unchanged factors and the actual
coefficient/ordinate cuts, obtaining all ten nonzero monomials of the
correction. It separately proves (1) through the literal c², Ac2, S and
f² producers and proves (2) through the changed coefficient producer.
The cuts are bound to their actual computed source values; all unchanged
factor cones are literal.

## 3. Identical positive zeros before any auxiliary decoding

Fix an admissible compiler-numeral recipe and strictly positive supplied
witnesses and ordinary input x. The retained source gives, before imposing
any equation,

    q=Bm1*Jrep+1>0,
    X=wq>0, Y=sq³>0,
    a=Y(X+1)>0,
    Delta=(a+1)(a+3)>0.                                (4)

At a zero of Fnew, divide the integer equality Fnew=0 by this known
nonzero Delta, using (1). The result is

    P5*Na_new*Nstrong=1.

Every factor is an integer, so Nstrong is +1 or -1. This statement does
not assume that the seven original scaled factors are all units.

For every integer a, Delta=(a+2)²-1 is0 or3 modulo4. Both f² and
(i*c²)² are square residues,0 or1. Consequently

    Nstrong=f²-Delta*(i*c²)²

can never be3 modulo4, and hence cannot equal -1. Thus Nstrong=1 and
Ns=Delta. It follows immediately that

    Qaux=u-Delta=auxiliary_reduced_coefficient,
    Na_new=Na.

Every factor and the full output now agree with F84 at the same tuple,
so F84=0. This argument establishes the strong sign before using any
auxiliary sign, Pell rank, native typing or accepting-history conclusion.

Conversely, at an F84 positive zero, the identical normalization gives
P5*Na*Nstrong=1. The same modulo4 argument yields Nstrong=1 and Ns=Delta.
Therefore Na_new=Na and Fnew=0 on that same tuple.

This proves equality of the **entire supplied positive integer zero sets**
with the identity coordinate map. Applying the parent's established
ordinary-input theorem on exactly its existing fixed-program recipes
proves universality of the new source. Its six fixed numeral ports remain
`Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`, with the same shifted-mask
and compiler conditions; arbitrary numerical coefficient assignments are
not being certified as valid programs. No new witness restoration,
positive-coordinate chart or native completeness argument is needed.

There is also an exact **integer-zero equivalence** for any integral
assignment to all supplied ports. If Delta is nonzero, the same cancellation
and modulo4 argument applies without any positivity assumption and forces
Ns=Delta. If Delta=0, the literal identities
Qaux=Delta²*i²*c⁴ and u=Delta*f² give Qaux=u=Ns=0, so both complete outputs
are0. The helper separately expands both full outputs at their normalized
cuts and checks their zero specialization at Delta=0. Thus Fnew and F84
have identical integer zero sets, although their polynomials differ.
This corollary makes no universality claim on arbitrary fixed numeral
assignments. It compares the new deformation directly to F84, not to the
different historical normalized85 polynomial.

## 4. Uniform exact degree155 from the actual source

Every witness and x has degree1. Each of the six fixed compiler numerals
has degree0, but remains a symbolic coefficient in the proof. Define

    Q0=Bm1*Jrep,
    k0=eta+zeta,
    gamma0=rho+sigma,
    C1=Q0-F-Z-alpha-twice_cell_bits*x,
    Ttransport=w*C1-transport_quotient*Q0.

The witness `alpha` in C1 is the unchanged source witness, not the new
auxiliary coefficient. The source gives the following leading forms:

    X_top = w*Q0,
    a_top = w*s*Q0⁴,             deg(a)=6,
    c_top = k0*s*Q0³,            deg(c)=5,
    Delta_top = w²*s²*Q0⁸,       deg(Delta)=12,
    V_top = k0*s*Q0³*T*f,        deg(V)=7.

In particular r_lhs has degree4, so its R*f² term in V has degree6,
strictly below the displayed degree7 term. The new coefficient has
leading form Delta_top*f² and exact degree14; multiplication by the
square-gap leader V_top² gives auxiliary degree28.

The two retained norm cancellations are checked as exact polynomial
identities through their literal computed cuts. Both have the form

    (X+a*c+G)²-(a²+H)c²
      = X²+2acX+2GX+2acG+G²-Hc².                      (5)

For the main norm, use X=wn2, a=R12, c=R10a, G=gam and H=a4m5.
For the input norm, use X=W, a=R12, c=index_rhs,
G=modulus_multiple and H=a4m5. The main leader comes from2acG;
the input leader comes from-Hc². Neither cancellation is a relation
imposed at polynomial zeros.

The helper propagates exact homogeneous leading polynomials through all85
rows, using (5) at the two guarded norms. The seven factors have these
full leading forms:

| Factor | Degree | Leading homogeneous form |
|---|---:|---|
| First |22|`-w²*s⁴*Q0^14*k0²`|
| Main |18|`8*w²*s³*Q0^11*k0*gamma0`|
| Input |32|`-4*delta²*w⁵*s⁵*Q0^20`|
| New auxiliary |28|`w²*s⁴*Q0^14*k0²*T²*f⁴`|
| Index |7|`-h*w*s*Q0⁴`|
| Transport |2|`Ttransport`|
| Scaled strong |46|`-i²*w⁴*s⁸*Q0^28*k0⁴`|

Their degrees sum to155. The complete leading form is

    32*Q0^91*h*gamma0*delta²*i²*k0^9*w^16*s^25
       *Ttransport*T²*f⁴.                             (6)

The final subtraction has degree12 and cannot cancel (6). The fresh
symbolic calculation expands (6) into120 integer-coefficient monomials,
keeping all fixed numeral variables symbolic. Its monomial

    Jrep^92*h*rho*delta²*i²*eta^9*w^16*s^25
       *transport_quotient*T²*f⁴

has coefficient **-32*Bm1^92**. No other symbolic coefficient monomial
contributes to this same dynamic monomial. Since Bm1>0 on every
admissible fixed-program slice, the coefficient never vanishes there.
This proves exact degree155 uniformly, not just at one numerical slice.

Naive gatewise degree propagation gives165 because it misses the two
norm cancellations. Two complete univariate coefficient
executions in the fresh helper attain155, recover all seven factor
degrees, check (3) against the degree187 parent, and match (6). Their
numeral assignments are algebra diagnostics, not alleged compiler
programs or positive native zeros. They supplement the uniform symbolic
proof rather than replace it.

## 5. Complete ledger and scope

| Part | M | A | Total |
|---|---:|---:|---:|
| Seven-factor producer core |41|37|78|
| Six product multiplications and final subtraction |6|1|7|
| Complete polynomial |**47**|**38**|**85**|

The receipt saves the entire85-row source, all25 supplied ports, the18
positive witnesses, source and helper hashes, the exact correction,
256 exhaustive modulo4 cases, both guarded norm identities, every row's
degree bound, all seven leading forms and the120-term complete leader.
All rows and all supplied ports remain live. The dense diagnostics also
verify all77 unaffected parent register values; changed finalizer values
are accounted for by the exact correction, not assumed equal off zero.

This is a new point on the operation/degree tradeoff,85/155. It improves
85/175 at the same operation count, but does not supersede86/131 or other
lower-degree choices. It does not lower the operation count84, change the
comparison-system result, or establish a general circuit minimum.

## 6. Provenance and replay

The new [standard-library helper](complete85_reduced_auxiliary_degree.py)
authenticates these six inert dependencies:

| Dependency | SHA-256 |
|---|---|
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| `review_complete84_scaled_strong_output.md` | `6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330` |
| `review_complete85_auxiliary_bezout_source.md` | `d8e8720f5287ef1069ce46f52369c532fb551d9611935065aa56210295ab2cd9` |
| `review_complete85_auxiliary_bezout_math.md` | `77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d` |

The motivating internal note `complete84_joint_norm_finalizer_scout.md`,
SHA-256 `ef8bf180e9bcd1fa1617c5f0aef53ddd39455c11502e76195205ffe2a2b3658f`,
was read inertly and left unchanged. Its t=1 deformation is instantiated
here as a complete source with a new uniform degree proof. Its separate
formal four-port lower bound is not needed for this construction. The
proof above is self-contained relative to the established parent theorem;
the internal note is not an extra executable dependency.

The helper rejects duplicate JSON keys and noninteger encodings, uses
explicit guards under optimization, leaves parent data unchanged and
writes receipts only to fresh paths. Normal and optimized replay require
exact type-sensitive receipt equality. No frozen helper is executed or
imported, no archived suite runs, and no enormous native Pell/history
fixture is claimed. No repository file was edited by this author.

The writer and fresh normal/optimized exact replays from `/` passed:

```sh
python3 /tmp/complete85_reduced_auxiliary_degree.py --root ABS_WIP \
  --expect /tmp/complete85_reduced_auxiliary_degree.json
python3 -O /tmp/complete85_reduced_auxiliary_degree.py --root ABS_WIP \
  --expect /tmp/complete85_reduced_auxiliary_degree.json
```

Helper SHA-256:
`2d3348d2148ad7bd9c95129bf197dbba2033f2bc735c5d2691473ca6c4aea7a1`.
Receipt SHA-256:
`eac8cfd977ac4d932b38aa5ecdfe0d52b6adf72f52a0d63d856589f62012f8c9`.
