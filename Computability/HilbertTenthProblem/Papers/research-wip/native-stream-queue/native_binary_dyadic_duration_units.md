# Norm units for the complete dyadic-duration recoder

The [137-operation dyadic-duration certificate](native_binary_dyadic_duration_recoder.md)
has a **191=93M+98A** polynomial successor, with **39 positive
existential coordinates** and exact total degree **382** at width2.
Its certificate costs **147=78M+69A**, with **15 comparisons**.
The option retaining the two old strong comparisons gives a
**193=91M+102A** polynomial of degree **244**, with143 certificate
operations,17 comparisons and the same39 witnesses. The old244-operation
SOS polynomial of degree64 remains another degree alternative.

Both new options preserve the complete ordinary-input and actual-duration
contract: on every positive zero, for a dyadic n>=2,

    duration=n, q=2^n, Q=q^k=2^(kn), 0<x<q,
    z=spread_k(x), P=B^n, B=2^(k-1)Q,
    J=(B^n-1)/(B-1).                                (1)

Conversely every such x,n has a full positive extension. In particular
the duration is the actual exponent of the recoder geometry. Its low-bit
test remains paid, as do both kernels and all input, output, ratio and
geometry bounds. No universal tag composition or new universal
operation bound is asserted.

The [source](native_binary_dyadic_duration_units.py) and
[receipt](native_binary_dyadic_duration_units.json) are new wrappers;
the frozen parents are unchanged. The source provides `build(width=k,
normalize_strong=True)`, `rewrite(raw_packet, normalize_strong=True)`,
`polynomial_source`, `lift_to_raw`, `audit_identity`, `ledger`, and
`degree_audit`. Width k is any fixed integer at least2.

## 1. Joined ports and positive definitions

Keep the raw recoder's notation S=qP,H=xJ,A=Ahat-1. Its joined relation is

    (BH+ell) AND (BK+ell-1)=BA, at scale BS,
    (B-1)v+ell=J, ell+g=B-1.                        (2)

The actual fused ports, explicitly checked by this wrapper, are

    C=16B, q_native=C*S,
    padded_A=C*H+16ell+12,
    padded_B=C*K+16ell-6,
    F3=C*Ahat-C+8=C*(Ahat-1)+8.                    (3)

These are not the old unjoined recoder ports. In particular F3 is now
of higher polynomial degree. It remains at least8 on every positive
tuple, so the AND packed index is positive before any typing theorem.
The raw proof applies the geometry theorem before AND scale typing,
then synchronizes the repunit duration, and only then separates (2).
The present proof restores that entire raw source before importing its
theorem; it does not reorder or weaken the bootstrap.

Apply the established [recoder unit rewrite](native_binary_input_dilation_unit179.md)
with prefixes `geo__` and `and__`. Its literal assertions concern the
native norm rows, checksum and positive definitions, not the old external
padding expressions. The new wrapper additionally asserts (3) and both
duration comparisons. The exact thirteen projected coordinates are

    q=x+input_slack, P=(B-1)J+1,
    s=2*odd_half+1, k=eta+zeta,
    c=kY+eta, a=XY+Y, d=X+ac+ga*(4a+3)

in each core for the last five, and the AND index

    r=F0+q_native*F1+q_native^2*F2+q_native^3*F3.    (4)

Every projected value is positive on every positive supplied tuple.
Indeed q>=2 implies B>=8, so P>0. The two X=wq0,Y=sq0 use positive
q0, and the three supplied Boolean fields and computed F3 are positive.
All these expressions are already paid gates. Aliasing removes their
coordinates and comparisons, with no new arithmetic or free copy gates.
The topological source ordering is checked.

The two supplied first roots are replaced by positive gaps as follows.
For either core put E=XY,V=XY^2 and let k denote that core's Pell
coordinate. The old triangular equation and new factor are

    V(V+1)k^2=tau(tau+1),
    N0=g0^2+4Vk(g0-k),
    g0=2tau+1-2Vk, tau=Vk+(g0-1)/2.                (5)

On an old positive zero, `(2tau+1)^2>(2Vk)^2`, so g0>0. On a new
zero with N0=1, g0 is odd, and the inverse root in (5) is a positive
integer. The six-gate rewrite has the same4M+2A cost as the old block.
Both positive ratio slacks are retained. These facts require no bit
typing or index decoding.

## 2. The seven-factor option and the single unrestricted checksum

For each core write

    Delta=(a+2)^2-1, T=i*c^2, U=j*c-(2r+1),
    K=Delta*(f^2-1),
    N1=d^2-Delta*c^2,
    N3=K*(U^2-y^2)+y^2.                            (6)

The old full strong comparison T^2=K is retained in this option.
Replacing the auxiliary coefficient T^2 by the already paid K is
cost-neutral and is an identity only when that comparison holds.
The exact correction is checked off zero, not ignored.

All six factors N0,N1,N3 exclude -1 modulo4 independently:
N0 is g0^2 modulo4; Delta is0 or3, so N1 is a square or a sum of two
squares modulo4; and K is0 or1, making N3 either y^2 or U^2 modulo4.
There is exactly one unrestricted factor,

    Qc=q_native-(F0+F1+F2+F3).                    (7)

Its old comparison is Qc=1. Define W as the product of these seven
integer factors. The source pays six multiplications for the product.
The equation W=1 makes each factor a unit; the six independent norm
sign exclusions force all six norm factors to1, and then Qc=1.
There is no multiplication of two independent unrestricted checksums.
The geometry's odd scale remains the explicit positive definition
s=2*odd_half+1.

All other old comparisons, including both strong equations and the
two new duration equations, remain. Thus W=1 plus these comparisons
restores the raw positive recoder through (4)--(5), before invoking
its power or population theorem. Conversely, every raw zero has the
unique positive projected values and gaps in (4)--(5). This option
has a positive coordinate bijection with the raw source after its
thirteen graph definitions are restored.

For residuals R_j of the retained comparisons, the final polynomial is

    W*(1+sum_j R_j^2)-1.                           (8)

Since all quantities are integers and the second factor is a positive
integer, (8)=0 forces W=1 and every R_j=0. It is equivalent to the
certificate without assuming any signs of the unrestricted checksum.
It is not claimed identical to the raw SOS polynomial off zero.

## 3. Two normalized strong units

The default additionally applies the
[single-core strong normalization](pcp_normalized_strong_history_units.md)
once to each core. It retains the supplied positive i but now computes

    t=i*c^2, Qs=Delta*t^2, Kstar=Delta*Qs,
    Ns=f^2-Qs,
    N3star=Kstar*(U^2-y^2)+y^2.                   (9)

The two Ns factors are appended to W, and the two old strong comparisons
are removed. Each application adds exactly2M to the certificate: one
for Qs and one for adjoining Ns to the product. The preexisting subtraction
f^2-1 is repurposed as f^2-Qs, and the K multiplication is repurposed
as Delta*Qs. The source imports the existing consumer checks for i,
t,t^2,K and the old f^2-1 register.

Soundness first uses a sign fact that needs no kernel theorem: Ns cannot
be -1 modulo4 because Delta is0 or3. The nine-factor product equaling1
therefore forces both Ns=1. In each core restore

    i_old=Delta*i.                                (10)

This value is positive before typing. The exact identities are

    old_strong_residual=Delta*(1-Ns),
    N3star=N3_old+old_strong_residual*(U^2-y^2).    (11)

Thus Ns=1 restores both the complete old strong comparison and its
auxiliary coefficient. Every other factor and surviving comparison
agrees with the seven-factor parent. Removing the two unit factors
equal to1 restores that parent's W=1, and Section2 restores the entire
raw positive source. In particular no proof here assumes the Boolean
checksum or dyadic duration before restoring the native equations.

For the converse, begin with a seven-factor zero and restore its raw
coordinates. Each complete native theorem gives

    c=psi_A(Jnative), A=a+2,
    Jnative=2r+1=3 modulo4.                        (12)

In geometry r=J is its odd repunit/population index. In the joined AND
core, r is the actual padded four-field index at scale16BS. The complete
AND theorem applies at this new scale; (12) follows exactly as in its
parent theorem. The proof does not reuse witnesses from the smaller
unjoined scale.

For each core choose the fresh canonical auxiliaries at m=2c*Jnative:

    f=chi_A(m), i_new=psi_A(m)/c^2,
    Tcanonical=Delta*psi_A(m),
    y=psi_Tcanonical(Jnative),
    U=chi_Tcanonical(Jnative)/Tcanonical,
    j=(U+Jnative)/c, o=(U+c)/f.                    (13)

The divisibility c^2|psi_A(2c*Jnative) follows directly by expanding
`(chi_A(Jnative)+c*sqrt(Delta))^(2c)`: its first odd term contributes
`2c^2*chi_A(Jnative)^(2c-1)`, and every subsequent odd term contains
c^3. All other integrality, positivity and minus-congruence facts in
(13) are the full canonical converse proved in the cited normalization
and raw native packets, using Jnative=3 modulo4. Thus the rebuilt
coordinates satisfy every equation in (9) and each auxiliary linear
comparison.

Only f,i,j,o,y in each core are rebuilt: ten coordinates in total.
A transitive dependency audit proves that these fields affect no outer
equation, no duration equation, no joined port and no other norm factor.
The cores have disjoint namespaces. All other29 supplied coordinates,
including both root gaps and all ratio slacks, remain fixed. This proves
the same positive outer projection, but not a bijection between every
old and new positive witness tuple. The lift (10) is an embedding in
the soundness direction; completeness uses the fresh choices (13).

## 4. Exact literal ledgers

At width2 the raw137 certificate has36 comparisons and52 witnesses.
The seven-factor rewrite adds6M, combines seven equations into one,
and projects thirteen positive definitions. This gives143 gates,
17 comparisons and39 witnesses. The default two-core normalization
adds4M and removes two comparisons. The integer-product finalizer
always costs3E-1 operations for E comparisons, including W=1.

|Width2 option|Certificate|Comparisons|Witnesses|Polynomial|Degree|
|---|---:|---:|---:|---:|---:|
|Raw parent|137=68M+69A|36|52|244=104M+140A|64|
|Seven factors, old strong equations|143=74M+69A|17|39|193=91M+102A|244|
|Nine factors, normalized strong units|147=78M+69A|15|39|191=93M+98A|382|

For fixed k>=3 put mu(k)=floor(log2 k)+popcount(k)-1. The old-strength
option has142+mu(k) certificate operations and192+mu(k) polynomial
operations. The normalized option has146+mu(k) certificate operations
and190+mu(k) polynomial operations. The comparison and witness counts
are unchanged from their width2 rows. These are actual schedules;
mu(k) is not asserted to be an optimal power-chain length.

## 5. Degree and the changed AND ports

Here the degree calculation treats every remaining supplied coordinate
as degree1. To support later composition, it also audits a substituted
ordinary-input expression of degree e=2 with a nonzero leading form;
the present complete recoder has e=1. The source checks all formulas
at both e=1 and e=2. Define

    v=(2k+1)e+1, b=ke+1, Rdegree=3v+b.             (14)

After projection, q has degree e, B degree ke, and P degree ke+1.
Consequently the **joined** native scale has degree v, F3 has degree b,
and the AND packed index has degree Rdegree. These replace the old
unjoined degree formulas. Its highest terms are

    q_native_top=16*B_top*q_top*P_top,
    F3_top=16*B_top*Ahat,
    r_top=q_native_top^3*F3_top.                   (15)

For a core whose scale has degree z, the computed a,c have degrees
2z+2,z+2. The main norm has the essential cancellation

    (X+ac+G)^2-(a^2+4a+3)c^2,
    G=ga*(4a+3),

leaving degree5z+7 and highest form8ga*a_top^2*c_top. The source
asserts every row in this identity and the strict degree inequalities
against all other expanded terms. The first norm unit has degree3z+5.
The following table includes every product factor; the checksum is
present only for the AND core.

|Factor|Geometry|AND|
|---|---:|---:|
|Main N1|5e+7|5v+7|
|First N0|3e+5|3v+5|
|Old-strength N3|6e+12|10v+2ke+8|
|Normalized N3star|14e+24|18v+2ke+20|
|Normalized Ns|8e+14|8v+14|
|Checksum Qc|—|v|

For clarity, the highest forms of the auxiliary and strong factors are

    N3_old_top=a_top^2*f^2*U_top^2,
    N3star_top=a_top^4*i^2*c_top^4*U_top^2,
    Ns_top=-a_top^2*i^2*c_top^4.                    (16)

In geometry U_top=j*c_top; in the AND core U_top=-2r_top. These
forms are nonzero. They are checked against actual polynomial
evaluations, including the changed F3 term in (15).

With old strong comparisons the product degree is
`14e+19v+2ke+44`. The unique largest outer residual is the AND strong
equation, of degree4v+10 and highest form i^2*c_top^4. The final degree is

    (56k+41)e+91; at e=1, 56k+132.                (17)

After normalization the product degree is
`30e+35v+2ke+96`. The three largest outer residuals are the AND index,
upper-X bound and auxiliary linear relation, each of degree3v+ke+1;
their squared highest forms sum to6r_top^2. The two duration residuals
and every other outer comparison have smaller degree. The final degree is

    (86k+71)e+139; at e=1, 86k+210.               (18)

The polynomial has the form (8), so its highest form is the nonzero
product of all factor highest forms and the stated positive sum of
outer squares. No expansion of that whole polynomial is needed to
certify the degree. The optional ordinary SOS conversion is also
available, with degree twice the larger of the product degree and
outer residual degree; it is not the degree reported in (17)--(18).

For a larger composed packet, added equations and expressions must
receive a fresh degree audit; (17)--(18) describe this recoder and its
explicit degree-e input substitution. Its public `Q`, `modulus`,
`duration`, `z` and native scale registers remain available to such a
paid composition.

## 6. Executable evidence and scope

The receipt covers both options at widths2,3,4,8,16,64,160. It checks
672 complete correction/output identities, including336 signed
assignments. These compose the exact seven-factor raw lift with the
two strong corrections (11), compare every surviving residual and
verify all joined ports. The identities do not incorrectly assert
equality of the old and new off-zero polynomials.
The restored first roots may be half-integral off zero; exact rational
evaluation checks those cases, while the unit signs prove integrality
on every positive zero.

Fourteen width/option ledgers include degree audits for both ordinary
and quadratic-loaded inputs. Twelve independent exact polynomial
evaluations of all factors and outer residuals check the cancellations
and leading forms at widths2,3,4. Four separate small canonical Pell
fixtures check the local divisibility construction. They are not
materialized full recoder zeros; those positive extensions are proved
parametrically by Sections1--3.

Run the receipt with

```sh
/tmp/diophantine-research-venv/bin/python native_binary_dyadic_duration_units.py
```

The author writer and latest fresh default pass. Root's independent
full proof/source review found no mathematical issue; its two API/audit
findings were fixed by keeping both returned metadata graphs acyclic
and asserting the complete fused A/B port rows. These fixes changed no
source gate, comparison or receipt ledger, and both options are checked
for serializable metadata.

Native independently reviewed the final proof/source and replayed the
latest default: PASS, with no findings. A separate direct scalar evaluator
passed384 complete factor/residual/output identities, including192
signed cases, at widths2,5,11 with both options;146 restored positive
roots were deliberately half-integral off zero. Additional exact
factor/outer-leading-coefficient audits at width5 with input degree2
gave degrees733 and1141 for the old-strength and normalized options,
respectively, agreeing with (17)--(18).
