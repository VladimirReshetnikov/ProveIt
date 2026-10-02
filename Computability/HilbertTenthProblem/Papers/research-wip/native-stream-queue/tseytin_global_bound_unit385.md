# A signed global bound gives a385-operation universal polynomial

The [literal source](tseytin_global_bound_unit385.py) replaces one ordinary
comparison of the complete [386 compiler](tseytin_shared_offsets386.md)
with a unit factor. The result is **385=178M+207A**,374 certificate gates,
four comparisons and62 positive witnesses, one fixed positive program
parameter A and ordinary positive input x. The propagated degree bound
is4714. The [receipt](tseytin_global_bound_unit385.json) saves all forms:

|Power products|Finalizer|Operations|M|A|Certificate|Comparisons|Degree bound|
|---|---|---:|---:|---:|---:|---:|---:|
|merged|anchor|385|178|207|374|4|4714|
|merged|SOS|385|178|207|374|4|9400|
|separate|anchor|387|178|209|373|5|4754|
|separate|SOS|387|178|209|373|5|9292|

On valid recompiled program slices there is a **bijection of full supplied
positive zero sets** with386: add1 to `global_bound` to obtain a parent
zero, retaining every other coordinate. The inverse subtracts1. These
are different polynomials and different off-zero bounds; the positive
inverse is proved below. The established75-certificate/87-polynomial
bound remains separate.

## 1. The source change and its initially unknown sign

Let D=`height_slack`, B=65536D, J=sum Shat_i−24 and
P=(B−1)J+1. Let Sigma be the sum of the ten positive ports H_U,H_V and
the eight selected-product hats ZUhat_i,ZVhat_i. The parent ordinary
comparison is Sigma+beta_old=P. Keep its paid sum, but compute

    G=P−(Sigma+beta), beta>0,                            (1)

and multiply G into the word-unit product. Remove that ordinary
comparison. Two certificate gates are added and three finalizer gates
are removed, saving one operation overall. The exponent component,
query comparison, two transport comparisons and every native definition
remain intact. The source guards the whole canonical parent and confirms
that beta has exactly the global sum as its sole consumer.

At an anchored zero, an integer unit product times1 plus a sum of integer
squares is1. Thus all ordinary residuals vanish and the unit product is1.
The SOS finalizer has the same property. Every factor is consequently
an integer unit, including G. Initially write G=+1 or−1. Equation(1) gives

    Sigma+beta=P−G<=P+1, hence Sigma<=P.                 (2)

Because Sigma contains ten strictly positive integer ports, each port
is at most P−9 and thus strictly below P. Also Sigma>=10, so P>=10;
J=0 would give P=1, and J>=0 follows from the positive selector hats.
Therefore J>=1 and B<=P. This includes D=1.

The scalar lane argument in the
[product-scale proof, Section2](tseytin_product_scale412.md#2-scalar-bounds-before-any-binary-typing)
uses only these individual bounds, nonnegative unhat products, class
masks at most(B−1)J and the range coefficient(D−1)J<P. It does not
require the stronger old equation Sigma+beta_old=P. Hence, before any
binary typing or word sign is known, with T=P^34,

    0<=H0,M0,Z<T, H=H0+2T, M=M0+T, q=16BT,
    H−Z>=T+1, M−Z>=1,
    BT−H−M+Z>=(B−5)T+2.                              (3)

Define mathematical fields, with no extra supplied coordinates or gates,

    F0=16(BT−H−M+Z)−15,
    F1=16(H−Z)+4, F2=16(M−Z)+2, F3=16Z+8.             (4)

They are positive, their sum is q−1, and each is below q. In particular
F0>2. Their residues modulo16 are1,4,2,8. The actual paid index satisfies

    r=F0+qF1+q²F2+q³F3=(q−1)S,
    S=(16H+13)+(q+1)[(16M+10)+(q−1)(16Z+8)],
    r>=q³+q²+q+1, r=1 mod16,
    X=q(S+beta_native)>r, Y=q(2s+1)>=3q.               (5)

These are exactly the scalar definitions of the
[computed-fields source](tseytin_computed_fields401.md). They do not
assume that G or the word-unit product is positive.

## 2. Recover the linear sign without using the total word sign

The unchanged exponent52 signed projection and valid program's paid
query residue exclusion force the exponent product to+1, as in the
[permuted-input proof](tseytin_permuted_digits387.md). That argument uses
neither word typing nor the global equality. In the separate-power form
the exponent product is directly constrained to1.

Use the definitions and four norm factors N0,N1,Ns,N3 of computed-fields401
Section3. Each norm is+1 by its modulo4 square obstruction. Write

    E=XY, K=k−hE, Nk=K−r=epsilon,
    Nl=V−jc+2K=lambda, epsilon,lambda in {−1,1}.       (6)

The rank argument there, through the exclusion of lambda=−1, uses only
the individual unit conditions and the bounds(5). For clarity its chain
is: the first norm gives k=psi_P0(n), P0=2XY²+1, n=K+vE with v>=0;
the main norm gives c=psi_A0(p), A0=Y(X+1)+2, p>n. The full normalized
strong norm gives pc dividing its index m, hence c divides m and
m>2p+1. The auxiliary norm and its strict residue windows then give
p=2K−lambda<=2r+3<E. Since n<p, v=0 and n=K. If lambda=−1 then
p=2n+1, contradicting c<k(Y+1) by the double-index growth inequality.
Thus lambda=1 without any appeal to the word product's total sign.

Do not use the next parent step, which inferred epsilon=1 from that
product. At this point we have instead

    n=r+epsilon, p=2rho+1, rho=r+epsilon−1,
    rho=r or r−2, rho>q, rho>=9, X>rho.                (7)

## 3. Reserved low bits exclude the remaining negative index

Apply the scalar ratio, root-projection and population portion of
computed-fields401 Section4 at rho. Its hypotheses are the exact indices
n=rho+1, p=2rho+1, the positive ratio slacks, rho>=9, rho>q, X>rho,
q dividing X and odd Y/q; every one follows from(5)–(7).
It does not require rho to be the original packed word r.
The detailed [raw geometry proof](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
gives

    Y>=X^rho, a=Y(X+1)>X^(rho+1)>2^(2rho+1),
    X=2^(2rho+1),
    Y=binom(2rho,rho)+sum_(j=1..rho)binom(2rho,rho+j)X^j.
                                                               (8)

The root congruence becomes equality because X and2^(2rho+1) are both
between0 and a. The ratio error is below16rho/(X+1)<1/2 and its fractional
tail below1/4, which identifies the displayed integer Y. Since q divides
X, write q=2^t. Since rho>q,2q divides X. Odd Y/q and the central-binomial
valuation then force

    popcount(rho)=t.                                  (9)

Suppose epsilon=−1. Then rho=r−2 has four base-q fields
F0−2,F1,F2,F3. By(3)–(4) they are all positive and below q; no borrowing
crosses a base-q boundary. Their sum is q−3 and their low residues are
15,4,2,8 modulo16. Write q=16Q and these four fields as16A_i+l_i.
Their low residues sum29 and have total population7. Therefore

    sum A_i=Q−2,
    popcount(rho)=sum popcount(A_i)+7
                 >=popcount(Q−2)+7=t+2,               (10)

contradicting(9). Here t>=5 is automatic from q=16BP^34 and B>=65536;
for Q=2^(t−4), popcount(Q−2)=t−5. The inequality is ordinary population
subadditivity under addition. It requires no AND or one-hot conclusion.

Thus epsilon=1. Every individual word factor is now+1 independently
of G. The exponent product is also+1, so the complete unit equation
forces **G=1**. This order is essential: neither the global sign nor
word-product positivity was assumed in the reserved-bit argument.

## 4. Positive inverse and complete equivalence

At any new positive zero on a valid program slice, G=1 makes
Sigma+beta=P−1. Set beta_old=beta+1>0. All other coordinates and
all native, exponent, transport and query values are unchanged. The
parent global equality holds, and every individual factor is1, giving
a complete parent zero in the corresponding merged/separate form.

Conversely, take any parent positive zero. Its established theorem
recovers a typed chronological history. Every history digit is in[0,D).
On each row at most one of the four nonbaseline slope classes is chosen
for each side. Hence the sum of that side's four selected unhat products
is at most its history H_side. Summing both sides and restoring the
eight hats gives

    Sigma<=2(H_U+H_V)+8<=4(D−1)J+8.

The exact parent repunit then gives

    beta_old=P−Sigma >=(65532D+3)J−7>1.               (11)

Thus beta=beta_old−1 is a positive integer. It makes G=1 and retains
all other factor and ordinary conditions. These two affine maps are
inverse on the entire supplied positive zero sets of each valid program
slice. They retain A and the ordinary input x exactly. No private Pell
coordinates need reconstruction, and no recoding is introduced here.

For a later ordinary-strong variant, keep its full strong equality.
Before either linear sign is known, p>n>=r−1 gives p>=r>=4369.
Thus c>(2A0−1)^(p−1)>A0^5>A0*Delta². The ordinary full strong rank
lemma, with exactly this size hypothesis, gives c dividing its Pell
index m, t_aux=Delta*psi_A0(m), and m>=c>2p; see the
[ordinary-strong factor proof, Section3](tseytin_permuted_factor_partitions.md).
These supply the same auxiliary positivity and strict residue windows
used in Section2. Sections1 and3 are unchanged, so the negative-index
exclusion and G=1 hold in this base as well. This observation does not
assert a same-coordinate inverse between the two strong treatments.

## 5. Source audit, degrees and evidence limits

The new factor G has degree2. The six previous word-factor bounds are
760,1804,416,974,345,345; the exponent-factor degrees total54, and the
remaining ordinary residuals have degree at most7. Hence the merged
anchored bound is(4644+2)+54+14=4714. The same guarded norm cancellations
and degree propagation give the other table entries. These are upper
bounds, not exact expanded-degree claims.

For an arbitrary supplied integer tuple, set beta_old=beta+1 and let
W and E be its old word and exponent products. Let S be the sum of the
three retained ordinary squares. Set U=WE and Splus=S in the merged
case, or U=W and Splus=S+(E−1)² in the separate case. The old and new
anchored polynomials are respectively

    U[1+Splus+(G−1)²]−1, U*G*(1+Splus)−1.

Their difference is exactly U(G−1)(Splus−G+2). The corresponding SOS
difference is U²(G²−1)−2U(G−1)−(G−1)². The checker verifies these
full-output identities and every retained parent register on positive
and signed assignments. This is not an assertion of off-zero equality.

Separate component checks exercise G=±1 with every possible large port,
including Sigma=P and D=1, before binary typing; check every actual
computed field and scalar bound; exhaust high-field compositions for
the negative-index population obstruction at q=2^5 through2^10; and
check the positive parent slack margin. Canonical guards, degree ledgers
and full output reachability are audited in all four forms. These finite
fixtures do not materialize complete compiled Pell zeros. Universality
and the positive-zero bijection follow from Sections1–4.

Author writer3622 and fresh20532 passed:320 complete output corrections
(160 signed),160 retained-register maps(80 signed),1,200 emitted weak-bound
contexts(600 with Sigma=P and300 at D=1),152 inverse margins,49,911
negative-index high-field compositions, all four ledgers and13 bad callers.

Gibbs's independent full proof/source/dependency review and fresh50516
passed with no findings. Its separate audit checked192 retained-register
maps(96 signed),384 full-output corrections(192 signed), two symbolic
main-norm expansions, all four degree/opcode/liveness ledgers,20 malformed
callers and eight local links. Its independent concept audit checked560
pretyping corners(280 negative global units,112 at D=1),1,120 raw endpoint
checks,1,280 population/Legendre cases and576 typed inverse margins.

Native's second independent proof/dependency/source review and fresh74167
also passed. It specifically checked the ordinary-strong rank hypothesis
before either sign, plus120 uneven emitted-port contexts(60 negative,
24 at D=1),640 reserved-bit cases through q=2^1024,100 inverse margins
and six ordinary-strong canonical auxiliary blocks. All are component or
algebraic audits, not materialized complete compiled Pell zeros.
