# Two locally forced checksum signs give a771-operation universal compiler

The complete [normalized ordered U15,2 compiler774](gpcp_shared_selectors774.md)
has a successor costing **771=352M+419A**, with125 positive witnesses,
22 comparisons, three fixed positive program parameters and ordinary positive
input. Its exact degree is209782. Supplying the initial history value instead
gives774=353M+421A,126 witnesses,23 comparisons and exact degree8672.
The [literal source](gpcp_checksum_global_units771.py) and
[receipt](gpcp_checksum_global_units771.json) emit both complete interfaces.

The source first moves the history checksum into the existing native product,
saving two additions. This intermediate772-operation form has exactly the same
full supplied positive zeros as774. It then moves the global history bound into
the product, saving one further addition. The final positive zero sets are in
bijection by adding1 to `hist__global_bound` to obtain the parent tuple, with all
other coordinates unchanged. Neither step is an off-zero polynomial identity.

The new sign argument applies to the actual supplied truth fields of both AND
cores. It does not require computing or removing those fields. It is related to
the reserved-bit arguments in the [group joint-bound unit](group_projective_joint_bound_unit.md)
and the [C2 global-bound unit](tseytin_global_bound_unit385.md), but here the
possible negative sign belongs to a checksum: the packed index itself is not
shifted. Exact native index and linear comparisons remain paid.

All fixed U15,2 transitions,57 tiles, input recoder, program frame, ordinary-input
padding convention and positive domains remain as in774. Thus its actual universal
program slices are preserved. These counts improve that instantiated route;
the established75-certificate/87-polynomial bounds remain separate.

## 1. Literal changes and complete ledgers

The old complete product W has13 factors: four norm factors in each of the
`geo__`, `and__` and `hist__and__` namespaces, and the recoder checksum C_r.
The history checksum C_h remains an ordinary comparison. Both checksums have
the same literal form

    C_j=q_j−(F0_j+F1_j+F2_j+F3_j).                     (1)

Append the multiplication W_c=W*C_h and remove C_h=1. The old checksum register
is already paid; this adds one certificate multiplication and removes the
three finalizer gates associated with that comparison. The net saving is two
additions. All other source rows and all supplied coordinates stay fixed.

For the final variant write D for the history height, B=131072D,
J=sum_(i=0..56)(Shat_i−1) and P=(B−1)J+1. Let Sigma be the sum of the ten positive
ports H_U,H_V and the eight selected-product hats. Retain the existing paid
sum Sigma+beta and append

    G=P−(Sigma+beta),       W_g=W_c*G.                  (2)

Remove the comparison Sigma+beta=P. This adds one subtraction and one
multiplication while removing three finalizer gates, saving one addition.
All fixed-numeral multiplications are charged.

|Initial value|New unit factors|Complete operations|M|A|Certificate|Comparisons|Witnesses|Exact degree|
|---|---|---:|---:|---:|---:|---:|---:|---:|
|computed|history checksum|772|352|420|704|23|125|209715|
|computed|history checksum and global bound|771|352|419|706|22|125|209782|
|supplied|history checksum|775|353|422|704|24|126|8670|
|supplied|history checksum and global bound|774|353|421|706|23|126|8672|

The704-gate certificates have329M+375A; the706-gate certificates have330M+376A.
The finalizer is always a unit product times1 plus the sum of its remaining
ordinary residual squares, minus1:

    F=U*(1+sum R_i²)−1.                                (3)

Here U=W_c or W_g. Over integers, F=0 forces U=1 and every R_i=0.
Consequently every displayed factor of U is an integer unit. The proof must
still distinguish their possible signs; multiplying two unrestricted checksums
alone would not suffice.

## 2. Positive native quantities before any checksum or global sign

The existing [three-core normalized source](gpcp_normalized_strong_compiler.md)
retains exact first-index, auxiliary linear, positive X-bound and padded-input
comparisons in both AND cores. Its normalized strong and auxiliary factors are,
with A=a+2, Delta=A²−1 and t=ic²,

    N_s=f²−Delta*t²,
    N_3=Delta²*t²*(V²−y²)+y².                         (4)

For integer a, Delta is0 or3 modulo4. Thus the main and strong norms cannot
be−1. The coefficient Delta²*t² in N_3 is a square, making that norm a square
modulo4 as well. Each first norm is the positive-root-gap expression

    N_0=g²+4XY²k(g−k),

which is g² modulo4. Therefore all12 norm factors are+1, independently of
either checksum sign and independently of G. This restores the complete strong
equation in each core before invoking rank or auxiliary-root classification.
The positive first-root inverse is tau=XY²k+(g−1)/2; N_0=1 makes g odd.

In each AND core, F0,F1,F2 are supplied positive integers. The recoder's computed
fourth field is F3=16*Ahat−8>=8. The history's is F3=16*Z+8>=8. The latter
positivity is unconditional: positive selector hats give J>=0 and P>=1,
and the decoded masks and selected unhat words are nonnegative. Their joined
Z is nonnegative. This actual source projection is established in
[the affine-history unit proof, Section2](pcp_uniform_affine_pair_units.md#2-six-positive-definitions-before-kernel-use).
It uses neither the global comparison nor an AND or Pell conclusion.

The computed initial program frame also has positive coefficients in positive
supplied values; the supplied-initial interface has a positive coordinate
instead. The actual D is the sum of the initial value, two final values and its
positive height slack, hence D>=4. In particular B>1, P>=1 and the prescribed
history scale q=16P^69 is positive. The recoder scale is also a positive multiple
of16. Thus, in each core, before checksum typing,

    F_i>0, F3>=8, q>=16,
    r=F0+qF1+q²F2+q³F3>q, r>=9,
    X=wq=r+bound_beta>r,
    Y=q(2*odd_half+1)>=3q.                             (5)

The padded comparisons, still ordinary and paid, give

    F1+F3=16H+12, F2+F3=16M+10,
    F1=4, F2=2, F3=8 modulo16.                        (6)

No upper bound on the four fields has yet been assumed. No completed recoder,
history interpretation or valid-program word property is needed for(5)–(6).

## 3. Exact local indices and population without a checksum

This section records the local kernel argument needed before deciding either
checksum sign. Suppress the core suffix. Put E=XY, P0=2XY²+1 and A=Y(X+1)+2.
The positive ratio slacks give

    Y<c/k<Y+1.

The first norm and its retained exact index comparison give

    k=psi_P0(n), k=r+1+hE, n=r+1 modulo E.

Since0<r+1<E, n>=r+1. The main positive norm gives c=psi_A(p), d=chi_A(p).
Here P0>A and c>k, so parameter monotonicity forces p>n. In particular p>=r+2,
and the elementary Pell growth bounds give

    c>A*Delta², c>2p, c>Yk>2(2r+1).                   (7)

The normalized strong equation gives psi_A(m)=ic² and f=chi_A(m).
Strong divisibility implies p divides m. Write m=pb. The multiple-index
identity yields psi_A(pb)/c=b*chi_A(p)^(b−1) modulo c; since the left side is
divisible by c and gcd(chi_A(p),c)=1, c divides b. Hence pc divides m, so
m>2p+1 and f>2chi_A(2p)>2c. The retained auxiliary comparison identifies

    V=of−c=jc−(2r+1)>0.                               (8)

Now the auxiliary norm in(4) is a genuine positive Pell equation with
coefficient L²−1, where L=Delta*psi_A(m)>1. Its root LV=chi_L(ell) has odd
index ell. The usual odd quotient identities give V modulo f and c. Using
V=−c modulo f, the strict step-down modulo f gives ell=±p modulo m and thus
modulo c. Consequently V=±p modulo c. Combining this with(8), while both
p and2r+1 lie strictly between0 and c/2 by(7), forces

    p=2r+1.

This is the same strict step-down used in the
[computed-field rank proof](tseytin_computed_fields401.md#3-recover-the-local-norm-and-linear-signs-in-order);
here its linear target is an exact retained comparison, so there is no
unknown linear unit sign. Since p<E and n<p, the earlier congruence also gives
n=r+1 exactly. These steps used only the norm equations and retained local
comparisons, not either checksum or the global comparison.

At these indices set xi=(X+1)^(2r)/X^r. Apply only the scalar ratio and population
part of the [raw geometry proof](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq),
not that wrapper's separate J>B interface. The precise chain is

    xi<c/k<xi*(1+2/a)^(2r),
    Y>=X^r, a=Y(X+1)>X^(r+1)>2^(2r+1).

The paid main-root definition and the Pell recurrence give X=2^(2r+1) modulo
4a+3. Both representatives lie strictly between0 and a, hence X=2^(2r+1).
The ratio error is below16r/(X+1)<1/2 and the fractional tail of xi below1/4.
Therefore

    Y=binom(2r,r)+sum_(j=1..r)binom(2r,r+j)*X^j.       (9)

Since q divides X, q=2^t. The bound r>q ensures2q divides X. Odd Y/q and(9)
then force t=v2(binom(2r,r))=popcount(r). This is a scalar native conclusion;
no field disjointness or Boolean interpretation was used to obtain it.

## 4. Both checksum signs are positive

Each checksum is an integer unit because it appears in the new complete
product. Suppose one is−1. Then(1) gives sum F_i=q+1. Four strictly positive
fields imply F_i<=q−2<q for each i. From(6) and q=0 modulo16 their residues are

    (F0,F1,F2,F3)=(3,4,2,8) modulo16.                 (10)

Write q=16Q and F_i=16a_i+l_i using these four low residues. Their sum is17
and their total binary population is5. Thus sum a_i=Q−1. Since q is dyadic,
the four base-q blocks in r do not overlap, so

    popcount(r)=sum popcount(F_i)
               =sum popcount(a_i)+5
               >=popcount(Q−1)+5=t+1.                (11)

This contradicts popcount(r)=t from Section3. The formula also covers q=16,
where Q=1 and all high parts are zero. It uses population subadditivity under
ordinary addition, without assuming disjoint bits among the fields themselves.

The argument applies independently to C_r and C_h. Both are+1. All old factors
are therefore+1. In the checksum-only source this restores precisely the old
product and its deleted history-checksum comparison. Conversely any old positive
zero already has all12 norms and both checksums+1, so it is a new zero with
identical supplied coordinates. This proves full positive-zero equality.

In the global variant, the product now forces G=1 as well. The order is important:
its sign was not used in proving native positivity, either local rank conclusion
or either checksum sign. For comparison with the original scalar history cone,
G=±1 would already give Sigma+beta<=P+1, so Sigma<=P and each of its ten positive
ports is<P. J=0 would force P=1, contradicting Sigma>=10. Thus the usual weak
scalar bound also holds, although it is not needed for the sign proof above.

## 5. Full positive inverse for the global unit

At a new positive zero G=1 gives Sigma+beta_new=P−1. Set

    beta_parent=beta_new+1,

retaining every other supplied coordinate. The source guards that this beta
has only its global-sum consumer. Hence no native quantity, checksum, transport,
program frame, recoder value or other comparison changes. The parent global
comparison and full product are restored, giving a positive parent zero.

Conversely take any parent positive zero. Its established affine-history
soundness gives digits in[0,D) and one selected tile per row. On each side the
four nonbaseline slope classes are disjoint. Their selected unhat words therefore
sum to at most that side's history. Restoring the eight hats gives

    Sigma<=2(H_U+H_V)+8<=4(D−1)J+8.

The exact repunit yields

    beta_parent=P−Sigma >=(131068D+3)J−7>1,            (12)

with J>=1. Thus beta_new=beta_parent−1 is positive, makes G=1, and retains all
other equations and factors. These affine maps are inverse on the entire supplied
positive zero sets of the two canonical interfaces. In particular the proof does
not need the program numerals to encode a valid universal program: arbitrary
positive program values still have the positive frame and the same typed affine
history theorem. Restricting afterward to the parent's valid program recipes
preserves its complete ordinary-input universal interpretation.

The source's formal map functions act on arbitrary integers, but their positivity
claims have exactly the zero-set scope just proved. No native auxiliaries are
rebuilt, and no program reparameterization is introduced.

## 6. Literal source guards, exact degree and checks

`rewrite` accepts only the complete canonical774 packet for one of the two
initial interfaces. It checks literal checksum/packing rows, positive port forms,
retained index/linear/bound comparisons, history radix and repunit rows, the
unit-product layout and the sole global-beta consumer. The public `build` checks
actual Boolean types before entering its cache. Every emission, degree and ledger
API requires equality with the complete current canonical packet; an altered
source, domain, comparison, program or theorem-scope record is rejected.

No old source definition changes. New rows are appended after all their operands,
and all source gates must reach the complete output. Historical parent records
remain provenance; active product and comparison metadata name the new factors.
The checksum-only identity claim refers to positive zero sets, not complete
integer polynomials. The global variant records the different affine-coordinate
bijection explicitly.

All retained propagated degree entries equal the parent's entries, including
its three guarded main-norm cancellations. Let d be the history q degree and nu
the history P degree. They are(d,nu)=(4623,67) for the computed initial value and
(138,2) for the supplied value. The history fourth-field degrees4423/133 and the
three supplied-field degrees1 are strictly below d. Thus the highest homogeneous
part of C_h is exactly that of q. Similarly the highest part of G is that of P,
since nu>1 and all its subtracted supplied ports have degree1.

The removed checksum/global residual degrees are strictly below the parent's
maximal ordinary residual degree,18292 or547. All three residuals attaining that
maximum remain literally unchanged, as does their nonzero sum-of-squares highest
form. Multiplying the old unit highest form by the nonzero q highest form, and
also by the nonzero P highest form when G is enabled, cannot cancel it. Therefore
these are **exact degrees**:

    degree_checksum=degree_parent+d,
    degree_global=degree_parent+d+nu.                  (13)

This explains the table's larger degrees as well as its smaller operation counts.
It is not an optimization claim over all arithmetic representations.

For arbitrary integer assignments in the global variant, evaluate the parent
at beta_parent=beta_new+1. Let W be its old13-factor product, C=C_h and S the sum
of retained ordinary squares. The complete outputs are

    F_parent=W[1+S+(C−1)²+(G−1)²]−1,
    F_new=W*C*G*(1+S)−1.

Their difference is W[(CG−1)(1+S)−(C−1)²−(G−1)²]. In the checksum-only variant
the corresponding difference is W(C−1)(S−C+2). The checker verifies every retained
register and these full-output corrections on both positive and signed tuples,
including zero decoded-selector cases. It does not assert off-zero equality.

Default execution recomputes the receipt; `--write` regenerates it. Further
checks cover unconditional computed-port positivity even at J=0, both weak global
endpoints using actual source cones, negative-checksum population obstructions,
actual slope-class disjointness and typed inverse-slack margins, all four complete
opcode/degree/output-closure ledgers, and malformed callers. These fixtures are
finite algebra and component evidence; no complete packed Pell zeros are newly
materialized. The universal projection and positive-zero claims follow from the
full proof above.

Author writer77088 and separate fresh replay85533 passed on the same source and
receipt. The audit covers96 complete retained-register and parent/manual output
corrections,48 signed;12 zero decoded-selector cases;7393 negative-checksum
population cases;160 unconditional positive-port contexts, including16 at J=0;
40 literal weak-global endpoints;256 typed inverse-slack components; and100
malformed callers. All four full ledgers, source closures and exact degree audits
pass, and all nine local links resolve. Independent final reviews are pending.

Root's full proof/source/dependency read and fresh62652 passed with no
findings. Its independent executor checked48 complete retained-register
and parent/manual-output corrections(24 signed), all four exact-degree
increments and complete counts.

Native's independent full proof/source/dependency review and fresh58790
passed with no findings, including the arbitrary-positive-program scope
and exact degree argument. Its separate audit checked128 complete
retained-register/parent/manual-output corrections(64 signed),32
zero-selector cases, eight independent nonzero leading-form certificates
modulo two primes with explicit main-norm expansions, all four complete
opcode/closure/domain ledgers,80 malformed callers and nine local links.
Its earlier independent mathematical audit checked four native contracts,
128 unconditional port contexts(64 at J=0 and32 with huge selected ports),
four actual slope-class lists,704 negative-checksum populations through
q=2^1024, seven exact first/main/Pell/population components and480 typed
inverse-slack margins. No complete compiled Pell zeros were materialized.
