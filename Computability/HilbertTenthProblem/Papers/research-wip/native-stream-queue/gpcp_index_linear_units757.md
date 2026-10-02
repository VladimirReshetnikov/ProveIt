# Fixed-target index and linear units give a 757-operation complete GPCP compiler

The [literal source](gpcp_index_linear_units757.py) reduces the selected
[first-padding763 compiler](gpcp_first_padding_units763.md) to
**757=352M+405A**, with731 certificate operations,9 comparisons,125 positive
witnesses, three fixed positive program parameters and ordinary positive input.
Its exact formal degree is214883. The supplied-initial interface costs760
operations with126 witnesses and exact degree9223. The
[receipt](gpcp_index_linear_units757.json) includes the complete polynomial
source, costs, degree certificates and literal-source hash for all48 forms:
two parents, eight initial-interface/bound configurations, and three local
conversion choices. The optional [765 parent](gpcp_upper_transport_unit765.md)
becomes759 operations under the same six conversions.

For each selected parent and configuration, the new and old polynomials have
**the same full supplied positive zero set, on identical supplied coordinates,
for every positive value of the program parameters**. Every added local sign
is forced+1 before recovering a checksum, padding, history or global-bound
sign. This transfers the existing universal relation on its program slices;
the independent75-certificate/87-polynomial universal bound is unchanged.
No integer-zero, zero-inclusive natural-zero or off-zero polynomial equality
is asserted. The fixed target below is2r+2, not twice the variable first index.

## 1. Literal private rows and charged changes

The three core prefixes are `geo__`, `and__` and `hist__and__`. In one core
write r for `J` in geometry or `bs_packed` in either AND component. Use

    E=XY, k=eta+zeta, c=Yk+eta,
    a=Y(X+1), A=a+2, Delta=A²−1,
    d=X+ac+gamma(4a+3), V=of−c.

Here A is mathematical notation for the Pell parameter. The actual source
register named `A` holds Delta. The ratio coordinates eta,zeta are supplied
positive, so Yk<c<(Y+1)k on every positive tuple.

The old private rows are

    r1=r+1, tr1=r1+r=2r+1,
    hpm1=hE, R11=r1+hpm1,
    jc=j*c, H17=jc−tr1=U, H2=U²,
    aux_u_rhs=of−c=V.

The old comparisons are k=R11 and U=V. Full canonical guards verify these
rows and their consumers in the imported actual763/765 sources. In particular,
R11 and V have no source consumer; tr1 feeds only H17; H17 feeds only H2;
r1 feeds only R11 and tr1. The unchanged normalized strong rows are also
guarded, including their actual `(ic²)²` square.

For an index conversion, replace R11 by k−hE and append

    Nk=R11−r=k−hE−r,
    index_product=previous_product*Nk.

Delete the old index comparison. For a linear conversion, replace the three
private definitions and append

    tr1=r1+r1=2r+2,
    H17=V−jc, H2=V²,
    Nl=H17+tr1=V−jc+2r+2,
    linear_product=previous_product*Nl.

Delete the old linear comparison. Both source changes are essential: the
auxiliary norm now uses the genuine V² before either new sign is recovered.
No supplied coordinate is inserted, removed or reinterpreted.

The complete anchored finalizer is `W*(1+sum R²)−1`, where W is the complete
factor product and the R are its remaining ordinary residuals. Each conversion
reuses paid private rows, adds one addition/subtraction and one multiplication,
and removes one subtraction, one square and one sum addition from the finalizer.
It therefore saves exactly one addition and no multiplication. Index-only and
linear-only each convert three cores and save3A; both save6A. Every arithmetic
operation, including numerical multiplication, is charged in this literal model.
The source auditor checks that every emitted gate reaches the final output.

|Selected parent, computed initial, both bounds|Conversions|Polynomial operations|Comparisons|Exact degree|
|---|---|---:|---:|---:|
|763|index only|760=352M+408A|12|251460|
|763|linear only|760=352M+408A|12|223861|
|763|both, default|757=352M+405A|9|214883|
|765|index only|762=352M+410A|14|246903|
|765|linear only|762=352M+410A|14|219304|
|765|both|759=352M+407A|11|210326|

## 2. Establish the weak scalar cone before recovering any new sign

At an integer zero, W and1+sum R² are integer factors of1. The latter is
positive, so all ordinary residuals vanish, W=1, and each integer factor
of W is±1. This argument does not require W to be positive off zero.

The weak scalar cone inherited from the actual bound and history definitions
uses neither deleted comparison. In geometry, q=x+input_slack>=2 and
B=2^63*q^64>=2^127. The ordinary bounds give X>r=J>B; an enabled bound
unit only weakens these to X>=r>=B. Also Y=q(2*odd_half+1)>=6.

In either AND core, F0,F1,F2 are supplied positive. The computed F3 is
at least8 before history typing:16*Ahat−8 in the recoder and16*Z+8 in
history. The positive selector hats give nonnegative decoded selectors;
the actual history expression has J_h>=0,P_h>=1, nonnegative decoded
masks and joined Z>=0 for every positive program parameter. These are
the unconditional scalar definitions from
[the affine history proof](pcp_uniform_affine_pair_units.md#2-six-positive-definitions-before-kernel-use),
not a claim that an off-zero tuple is already a valid history. Both native
scales q are positive multiples of16. Consequently

    r=F0+qF1+q²F2+q³F3>q, r>=9, Y>=3q>=48.

For763 let C be the checksum unit and sigma the first-padding unit. The
retained second padding and computed F3 give the four low-residue cases

|C|sigma|(F0,F1,F2,F3) modulo16|
|---:|---:|---|
|+1|+1|(1,4,2,8)|
|−1|+1|(3,4,2,8)|
|+1|−1|(15,6,2,8)|
|−1|−1|(1,6,2,8)|

For765 use only the sigma=+1 rows because its original first padding is
retained. Thus r is odd and nonzero modulo16 in every sign case, while
X is a multiple of16. If the native bound is ordinary it already gives
X>r. If it is a unit H, its positive beta gives X−r=beta+H>=0, and the
residues exclude equality. This proves X>r without selecting C or sigma.

The deliberately weaker common cone suffices in all three cores:

    r>=9, X>=r, Y>=6,
    E=XY>2r+3, 0<r−1<=r+1<E,
    Y(r−1)>2(2r+3), P0=2XY²+1>A=Y(X+1)+2>1.       (1)

The argument uses no valid-program slice, field disjointness, population
identity, global-bound sign, upper-transport sign or recovered local sign.
Calling the complete parent theorem before establishing these facts would
be circular; only its unchanged scalar definitions are being used here.

## 3. Positive norms and the weak first-index bootstrap

The four actual native factors in a core are

    N0=g²+4XY²k(g−k),
    N1=d²−Delta*c²,
    Ns=f²−Delta*(ic²)²,
    N3=Delta²*(ic²)²*(V²−y²)+y².                  (2)

When linear conversion is disabled, its retained ordinary comparison first
identifies the old auxiliary square U² with V². N0 is a square modulo4;
Delta is0 or3 modulo4; and the coefficient in N3 is a square. Thus none
of these four factors can be−1 modulo4, and all are+1. This conclusion
needs neither V>0 nor a sign for Nk or Nl.

Write epsilon=Nk and lambda=Nl when those conversions are enabled. For
a disabled conversion set its sign to+1 using the retained old comparison.
Then epsilon,lambda are±1 and

    k=r+epsilon+hE,
    V=jc−Jstar, Jstar=2r+2−lambda in{2r+1,2r+3}.   (3)

The actual g is positive. N0=1 makes it odd, and the positive first-root
inverse tau=XY²k+(g−1)/2 yields

    k=psi_P0(n), n>=1.

Here chi_A(t)+psi_A(t)*sqrt(A²−1)=(A+sqrt(A²−1))^t. Since P0=1 modulo E,
the Pell recurrence gives n=k=r+epsilon modulo E. The residue window(1)
therefore gives **n>=r−1**, not the stronger bound that would already assume
epsilon=+1. Positive d and N1=1 give c=psi_A(p),d=chi_A(p),p>=1.
Because P0>A and c>k, parameter/index monotonicity forces p>n, hence
p>=r>=9. Before either new sign is recovered, Pell growth and the ratio give

    c>(2A−1)^(p−1)>A^8>A*Delta²,
    c>2p,
    c>Yk>=Y(r−1)>2(2r+3).                         (4)

## 4. The complete normalized strong factor makes V positive

The retained Ns=1 is the full normalized equation, with supplied i>0.
It gives f=chi_A(m),psi_A(m)=ic²,m>=1. Strong divisibility of psi implies
p divides m. Write m=pb. Expanding the multiple-index identity modulo c
gives

    psi_A(pb)/c = b*d^(b−1) modulo c.

The left side is divisible by c, and gcd(c,d)=1 from N1=1. Hence c divides b:

    pc divides m.                                 (5)

This derives the exact rank condition from the actual normalized source;
no theorem for a relaxed divisibility witness and no fresh strong witness
is substituted. The large c in(4) gives m>2p+1 and

    f>2chi_A(2p)>2c.

Since o is supplied positive, V=of−c>0. This is established independently
of the sign or target in(3), which is why the genuine V² in(2) matters.

## 5. Strict auxiliary stepdown fixes the target

Put L=Delta*psi_A(m)>1. The auxiliary norm N3=1 is

    (LV)²−(L²−1)y²=1.

Positive Pell classification gives LV=chi_L(ell) for ell>=1. Its index
is odd, since chi_L(2t)=(-1)^t modulo L. The odd quotient polynomial
identity, with L²=1−A² modulo f and c dividing L, gives

    V=(-1)^((ell−1)/2)*psi_A(ell) modulo f,
    V=(-1)^((ell−1)/2)*ell modulo c.                (6)

The first congruence and V=−c modulo f, followed by the chi doubling
identity, imply chi_A(2ell)=chi_A(2p) modulo f=chi_A(m).
For the strict stepdown, choose a nearest multiple of m and write
ell=±z+jm,0<=z<=m/2. The Pell pair at2m is(-1,0) modulo f, so the left
side is(-1)^j*chi_A(2z) modulo f. If2z=m its residue is0, impossible
because0<chi_A(2p)<f. Otherwise

    chi_A(2z)<=chi_A(m−1)<f/3,
    chi_A(2p)<f/2.

Odd j would make a strictly positive sum below f divisible by f. Even j
forces equality of the small positive chi values, hence z=p. Therefore
ell=±p modulo m. By(5) the same holds modulo c. The second congruence(6)
and V=−Jstar modulo c now give Jstar=±p modulo c. The already proved
bounds(4) place both p and Jstar strictly between0 and c/2, so

    p=Jstar=2r+2−lambda.                            (7)

As p<=2r+3<E and n<p, the earlier first-index congruence has no wrap:

    n=r+epsilon.                                   (8)

The odd quotient identity and the strict stepdown are also recorded in
[the normalized native proof, Section3](tseytin_computed_fields401.md#3-recover-the-local-norm-and-linear-signs-in-order).
Here their hypotheses were derived with n>=r−1 and the present fixed target,
before restoring any inherited checksum or padding theorem.

## 6. Pell duplication excludes all wrong signs locally

Let A2=2A²−1. Direct arithmetic gives A2>P0 and2A>Y+1. Duplication and
parameter monotonicity give

    psi_A(2n)=2A*psi_A2(n)>(Y+1)*psi_P0(n)=(Y+1)k.  (9)

Equations(7)–(8) yield every possible case:

|epsilon|lambda|p relative to2n|
|---:|---:|---|
|+1|+1|2n−1|
|+1|−1|2n+1|
|−1|+1|2n+3|
|−1|−1|2n+5|

In each of the three unwanted cases, p>=2n+1; (9) then contradicts the
unchanged ratio c=psi_A(p)<(Y+1)k. Thus epsilon=lambda=+1 separately in
every core. This also proves the index-only and linear-only cases, with
the disabled sign supplied by its old comparison. No product of these
signs or checksum conclusion is needed. Replacing2r+2 by2K for K=k−hE
changes this table and is outside the present result.

At a new positive zero every deleted index and linear comparison is now
restored. In particular V=jc−(2r+1), so the old auxiliary square and factor
agree with the new ones. Every added factor is1, every remaining old factor
and residual agrees, and the complete old product is1. This is an old
positive zero on the identical supplied tuple. The private R11,tr1,H17
register values themselves may differ and are recomputed by the old source.

Conversely, an old positive zero makes each enabled Nk,Nl exactly1 from
its old comparisons, and U=V identifies the two auxiliary squares. The
new complete product and all remaining comparisons therefore give a new
zero on the same tuple. These two implications prove full positive-zero
equality for all positive program parameters. Only after this restoration
does the selected parent's established checksum/padding/history proof apply.

## 7. Off-zero correction and exact formal degree

The positive-zero theorem is not a polynomial identity. At every integer
assignment, with old residuals Rk=k−R11_old and Rl=U−V,

    Nk=1+Rk, Nl=1−Rl,
    N3_new=N3_old+R16_old*(V²−U²),
    R16_old=Delta²*(ic²)².                         (10)

Apply the N3 correction only where the linear conversion is enabled.
Every other old factor and every retained ordinary residual has its old
value. Let D be the sum of squares of the deleted ordinary residuals,
S the remaining ordinary SOS, Wold the old product, and Wnew the product
of the corrected old factors and all enabled new factors. Then, without
division or an imposed zero condition,

    Fold=Wold*(1+S+D)−1,
    Fnew=Wnew*(1+S)−1,
    Fnew−Fold=(Wnew−Wold)*(1+S)−Wold*D.             (11)

The receipt checks(10)–(11) using the complete actual sources on both signed
and positive off-zero assignments, including all-zero decoded history-selector
contexts. It also compares every unaffected old register.

Degree propagation uses the complete polynomial schedule and the three
guarded expanded main-norm identities from the shared-selector parent.
At each R15, the exactly expanded highest term is2*cam2*gam, whose degree
strictly exceeds each other expanded term; the code checks these inequalities
and every literal row supporting the identity. All other gates use ordinary
product/max degree propagation. This gives an upper bound without expanding
the huge full polynomial.

To certify equality, assign the leading homogeneous input coordinates their
source-order values2,3,..., except each core's tau_gap,eta,zeta are1. Propagate
the highest homogeneous values modulo each of1000000007 and1000000009,
including the expanded R15 leading term. In all48 forms the final leading
value and every factor's leading value are nonzero for both primes. A nonzero
evaluation of the top homogeneous part proves that it is not the zero
polynomial over the integers, so each recorded final degree is exact. The
receipt records the residues, factor degrees and both certificates. These
are formal degrees with program parameters still indeterminate; a particular
fixed program specialization can lower them.

For the default, unit_degree=205773 and maximum_outer_degree=4555, giving
205773+2*4555=214883. For supplied initial data the corresponding numbers
are8953 and135, giving9223.

|Parent|Initial interface|Enabled bound pairs|Both conversions: operations|Comparisons|Positive witnesses|Exact degree|
|---:|---|---|---:|---:|---:|---:|
|763|supplied|none|764=353M+411A|14|126|9235|
|763|supplied|geometry|762=353M+409A|12|126|9301|
|763|supplied|AND|762=353M+409A|12|126|9157|
|763|supplied|both|760=353M+407A|10|126|9223|
|763|computed|none|761=352M+409A|13|125|223800|
|763|computed|geometry|759=352M+407A|11|125|223866|
|763|computed|AND|759=352M+407A|11|125|214817|
|763|computed|both|757=352M+405A|9|125|214883|
|765|supplied|none|766=353M+413A|16|126|9098|
|765|supplied|geometry|764=353M+411A|14|126|9164|
|765|supplied|AND|764=353M+411A|14|126|9020|
|765|supplied|both|762=353M+409A|12|126|9086|
|765|computed|none|763=352M+411A|15|125|219243|
|765|computed|geometry|761=352M+409A|13|125|219309|
|765|computed|AND|761=352M+409A|13|125|210260|
|765|computed|both|759=352M+407A|11|125|210326|

## 8. Guards, replay and review scope

The public build options require exact Boolean switches and exact integer
parent_stage763 or765. Both unit switches cannot be disabled. `rewrite`
compares the entire supplied parent, including history metadata, to its
selected canonical source with recursive type-sensitive equality. Tuple
dictionary keys are also compared with their types preserved. `checked`,
`polynomial_source`, `degree_dictionary`, `degree_audit` and `ledger` require
the complete canonical successor, not merely matching costs or source rows.
Float/Boolean substitutions for equal-valued integer constants and list/tuple
substitutions are rejected. Builds and the public `canonical_parent` accessor
return isolated copies of cached packets. Independent review found that the
first accessor version exposed its mutable guard reference. The repaired
version keeps the holder private, validates exact option types and returns
a defensive copy; the regression changes the parent's numerical B coefficient
before any successor cache exists, rejects that parent, and verifies that
fresh construction remains canonical.

The current packet preserves the active fixed program, history, bound,
padding and native interfaces, along with its immediate parent source,
comparisons and factors. Earlier full ancestry stays in the imported parent
modules; it is not presented as the current source. Each new local interface
records the changed definitions and fixed packed-index target explicitly.

Author writer and fresh replay cover48 ledgers and96 exact-degree certificates;
576 complete register/factor/output corrections,288 signed assignments and144
zero-selector contexts;1,128 malformed caller/packet rejections;512 sign-table
cases including384 wrong-sign duplication exclusions;12 weakest-cone margins;
409 exact normalized pc-divisibility antecedents;23 signed AND cones and4
geometry cones. Run from this directory with the research Python environment:

```sh
/tmp/diophantine-research-venv/bin/python gpcp_index_linear_units757.py
```

Independent mathematical review checked all16 parent shapes and the entire
bootstrap/rank/stepdown/sign chain. Its separate exact component replay passed
48 source-consumer checks,2,145 wrong-sign ratio exclusions,75 weak geometry
margins,144 growth cases,31,500 rank cases,47,712 strict-stepdown cases and162
odd quotient congruences. Independent final-source review used a separate
executor and passed48 ledgers,96 leading certificates,384 complete output
corrections with192 signed assignments and96 zero-selector maps,768 malformed
packet rejections,96 numerical-type rejections,48 cache-isolation checks and10
bad callers. The reviews reported no unresolved finding. Their temporary
records are `/tmp/review_gpcp_index_linear757_math.md`,
`/tmp/review_gpcp_index_linear757_check.{py,json}` and
`/tmp/review_gpcp757_source.{py,json}`; these are session provenance, not
portable dependencies of the checked-in replay.

After the cache repair, the root reran the complete independent source oracle
successfully on the final source. The separate API reviewer also passed343
malformed-input checks, two cold-cache parent-mutation regressions,1,008 active
metadata comparisons,288 interface checks,144 literal local formulas and48
nested build-isolation checks. The final source SHA-256 is
`a8b213386863857dae8c98f06a2ab41b297e05e6742b91217f538efaf7087774`.
Its author writer and fresh read-only receipt replay passed. No unresolved
mathematical, source or API finding remains within the stated review scope.

The finite checks support the literal algebra and the universal proof; they
do not substitute finite sampling for positive-zero equality. No complete
enormous compiled Pell witness is materialized. The theorem is relative to
the selected frozen parent universality theorem, and the operation figures
describe the emitted schedule rather than arithmetic lower bounds or optimality.
