# Residue-one orientation and selectively even Pell indices

## 0. Fixed equation and scope

The principal polynomial is the sum of the squares of all 290 literal quadratic
residuals in `integer442/equation.json`. Its variable order is the order in that
file. It has 442 unrestricted integer variables, exact degree four, 4,652 collected
monomials, and coefficient height 128,446. Every collected coefficient is supplied
in `integer442/expanded_polynomial.json`. The companion `integer446/` has 446
integer variables, 291 residuals, 4,775 monomials and the same height. These are
ordinary fixed integer polynomials, not equations with exponentiation primitives.

The 442-variable source is `../architecture/unified_derived_shell/raw/`; the
446-variable source is `../architecture/unified_slack_shell/raw/`. The former uses
a derived label range, the latter an additional local label coordinate. Their
ordinary natural-domain arithmetic proof is `../architecture/UNIFIED_PRODUCT_PROOF.md`.
It identifies the factorial's binomial with the reciprocal prime-power product:

    t = t0+16, rho=F^2, B=binom(F^2+t,t), V0=(F^2+1)^t,
    F B=V0+s, B=r+s+1, K=2R, N=B^K, q=N^K.

Here these formulas name intended meanings; powers and binomials are not assumed
before their certification. The actual equations have 18 power requests and 15
seed indices. The new compiler keeps the t and K seeds undoubled, doubles the
other thirteen, and leaves the derived t+1 pair as its original one-step Pell
addition. Every one of the eleven `(q+1)^k` requests is among the doubled seeds.
The two other doubled seeds certify q^(y+1) and q^(x+1).

The theorem is an ordinary proof, formalizable in ZFC, that the new polynomial
has an integer zero iff the inherited direct source has a natural zero. Composing
with that source's numerical C222/refutation calibration gives

    ZFC proves: [there is no z in Z^442 with P442(z)=0] iff Con(ZFC).

This is not a proof of consistency, a decision of the equation's solvability,
a globally smallest equation, or a newly emitted full Lean/object-ZFC proof.
The named calibration interfaces remain KEndpoint.c222_iff_zf_refutation and
ConstructibleChoice.zf_refutation_iff_zfc_refutation. The arithmetic route does
not simulate K215 and does not instantiate Jones's universal polynomial.

## 1. The two new interface ideas

### 1.1 Residue one orients a signed square root

Suppose q>=3, k>=1 and m is an integer satisfying

    m^2=(q+1)^(2k),  m=1 (mod q).

The first equality gives m=+(q+1)^k or m=-(q+1)^k. Their residues modulo q are
+1 and -1. Since q does not divide 2, only the positive sign is possible.
Therefore m=(q+1)^k. This needs no nonnegativity guard for m.

The first materialized variant adds the single quadratic row m-1-q*u=0 for each
of eleven outputs, with signed u. The preferred variant builds the same residue
condition into an existing remainder. The actual front equation has one of the
forms

    m=L*(C+q*h)+r,     or     m=N*L*h+r,
    L=r+s+1.

Replace the old remainder r everywhere by 1+q*u, reusing its coordinate as u.
The equations become

    m=L*(C+q*h)+1+q*u,  or  m=N*L*h+1+q*u,
    L=q*u+s+2.

All changed residuals remain quadratic: the old remainder occurs linearly in
every source row, and q is an existing coordinate. The certificate lists every
occurrence and its exact substitution. Once L is proved to be a positive power
of q, the first equation gives m=1 modulo q.

This substitution is NOT a bijective change of arbitrary integer coordinates.
It is an existence-preserving restriction justified at the semantic interface.
For completeness, a genuine terminal power has m=(q+1)^k=1 modulo q and the
old divisor L is q^j with j>=1. Thus its old bounded remainder satisfies
r=1 modulo q, 0<=r<L, hence r>=1; u=(r-1)/q is a nonnegative integer. For
soundness, u>=0 and q>0 give the old nonnegative remainder r=1+q*u. The recovery
of the genuine powers below establishes exactly the required interface.

### 1.2 Weighted interval guards share one sign anchor

For q>0 suppose several pairs satisfy

    q*u_i+s_i=L-2.

Retain u_0>=0 and s_0>=0. They imply L-2>=0. For any other pair,

    [u_i>=0 and s_i>=0] iff u_i*s_i>=0.

Indeed, if either were negative, a nonnegative product would make the other
nonpositive, and q*u_i+s_i would be strictly negative. This contradicts L-2>=0.
The reverse direction is immediate. This weighted lemma is the exact adaptation
of the incoming Structural Compression shared-remainder lemma to the new
remainder coordinates. Seven literal applications replace fourteen individual
sign predicates by seven product predicates. Every pair, retained anchor,
common-bound identity, and row is recorded. The sign of q is established before
using this lemma; it does not depend on a binomial interpretation.

All sign predicates G>=0 are represented by one quadratic row

    G=a^2+b^2+c(c+1),  a,b,c in Z.

This expression takes only nonnegative integer values. Conversely 4G+1 is not
of the excluded three-square shape; Legendre's three-square theorem and parity
put its representation in this form. G is affine or quadratic here, so the
final residuals remain quadratic. There are 38 such predicates in the principal
source and 39 in the companion, including a strict common-ordinate predicate.

## 2. Pell notation and facts used in the compiler

For a>=2 set D=a^2-1 and define

    (a+sqrt(D))^j=chi_a(j)+psi_a(j)*sqrt(D),  j>=0.

They are integer sequences satisfying the usual multiplication recurrence,
with (chi(0),psi(0))=(1,0) and (chi(1),psi(1))=(a,1). Both are strictly
increasing after the zero endpoint, and psi_a(j)>=j. Every integral solution
of x^2-D*y^2=1 has |x|=chi_a(i), |y|=psi_a(i) for one i>=0. To prove this,
reduce a positive norm-one unit by powers of a+sqrt(D); the smallest nontrivial
positive integral ordinate is 1 and its abscissa is a. The standard reduction
therefore leaves only the identity. Independent signs of the coordinates are
allowed.

Two elementary facts supply the finite indexed-Pell relation.

1. If i,h>=1 and psi_a(i)^2 divides psi_a(h), then i divides h and
   psi_a(i) divides h. Write h=li+r with 0<=r<i, x=chi_a(i), y=psi_a(i).
   Modulo y the addition law gives psi_a(h)=x^l psi_a(r). The norm gives
   gcd(x,y)=1; monotonicity forces r=0. Expansion modulo y^2 then gives
   psi_a(li)=l*x^(l-1)*y, so y divides l, hence y divides h. Also i<=h.
2. For 1<=i<=h, if chi_a(j)=+/-chi_a(i) modulo chi_a(h), then
   j=+/-i modulo 2h. Modulo u=chi_a(h), the norm-unit doubling identity gives
   (a+sqrt(D))^(2h)=-1. Reduce j modulo 2h and reflect its remainder about h.
   This leaves +/-chi_a(r) with 0<=r<=h and r=+/-j modulo 2h. Since
   2*chi_a(h-1)<chi_a(h), two coordinates below h cannot add to u.
   Congruence up to sign forces r=i. The endpoint i=h is the unique zero
   residue. In particular congruence to +/-a forces j odd.

These statements are unbounded arithmetic lemmas; finite Pell tests do not
replace their proofs. Polynomial dependence of chi_b(j),psi_b(j) on b permits
base transfer modulo any integer. At b=1 one has chi_1(j)=1, psi_1(j)=j.

## 3. A common square frame and common nonzero ordinate

Let Aset be the distinct actual base, exponent, and output atoms of the eighteen
original power requests, using their exact affine restorations in the contracted
source. Replace the private frame by

    W=2*(2+sum(a^2 for a in Aset)).

Consequently W>=4, |a|<W, a^2<W, and 2|a|<W for each atom. In particular the
requested doubled exponents 2k and squared outputs m^2 are strictly below W.
No sign of a proposed power output is needed for this frame. Its exact affine
atom list and defining row are in the transformation certificate.

Retain A>=0 and Zminus1>=0 and the old frame norm

    A^2-W^3(W+2)*(Zminus1+1)^2=1.

Set Z=Zminus1+1>=1. Pell classification at center W+1 identifies
(A,WZ)=(chi_(W+1)(h),psi_(W+1)(h)) with h>=1. Reduction modulo W gives
psi_(W+1)(h)=h modulo W, so W divides h and h>=W. Therefore

    A >= (W+1)^W > W^W,  A>W^2.

For every positive actual power base 1<=n<W, the existing definition

    T_n=2An-n^2-1

gives T_n>=2A-2>A>W^W. This follows because the quadratic increases on
1<=n<W<A and its minimum is at n=1.

Keep the common norm U^2-(A^2-1)Vaux^2=1, the original product identity

    Vaux=(product over fifteen seeds Y_i^2)*(v+1),

and impose Vaux>=1 directly. Delete the old sign predicate v>=0. The product
and positivity imply all Y_i are nonzero, their squares divide Vaux, and
v+1>0, hence v>=0. Thus this change supplies its own omitted sign before
using the index theorem. The common norm implies |U|>=A>=2.

Retain the constructor Baux=1+4Vaux*(q4+1) with q4>=0 and Baux=A modulo U.
Thus Baux>=5 is odd, and Baux=1 modulo 4|Y_i| for every seed. No auxiliary
comparison coordinate or congruence quotient needs a sign assumption.

## 4. Even seed indices recover their own missing size bounds

For a selected seed, k>=1 is its positive original exponent and e=2k<W.
Keep its three norms and abscissa congruence, but change its ordinate congruence
to

    X^2-(A^2-1)Y^2=1,
    S^2-(Baux^2-1)Raux^2=1,
    S=X (mod U),  Raux=2k (mod 4Y).

The private old row Y=k+slack may be removed with its unconstrained slack.
It has no other occurrence after its sign guard is removed. Its unique inverse
is slack=Y-k; this exact pruning is separately certified.

We already know Y!=0. Suppose |Y|=1. Then |X|=A. Classify the comparison
norm by S=+/-chi_Baux(j), Raux=+/-psi_Baux(j). Transfer Baux=A modulo U
and S=X modulo U. The abscissa residue fact implies that j is odd. Since
Baux is odd, psi_Baux(j)=j modulo 2; hence Raux is odd. But Raux=2k
modulo 4Y makes it even. Contradiction. Therefore |Y|>=2. Its main Pell
index i is at least two, and

    |Y|=psi_A(i)>=psi_A(2)=2A>2k.

Now classify the common norm as |U|=chi_A(h), Vaux=psi_A(h), h>=1.
Squared divisibility gives i<=h and |Y| divides h. The S congruence yields
j=+/-i modulo 2h. Since Baux=1 modulo 4|Y|, the Raux congruence yields
j=+/-2k modulo 4|Y|. Therefore i=+/-2k modulo 2|Y|. But
1<=i<=|Y| and 1<=2k<|Y|; the minus congruence is impossible and the plus
congruence forces i=2k. Thus

    |X|=chi_A(2k), |Y|=psi_A(2k).

For the two undoubled t and K seeds, their retained guards Y>=k>=1 give the
usual same short-interval proof, with positive Y and |X|=chi_A(k).
All exponent positivity is syntactic before power semantics: t>=16, K=2R>0,
t+F^2>0, x+1>0, y+1>0, and every encoded representative plus one is positive.
The derived label J, when present, has a monotone constructor with positive
constant term. Its source certificate supplies the compositional lower bound.

## 5. Squared outputs force positive Pell coordinates

For a doubled seed and a supporting base n>=2, replace its power congruence by

    X+(n-A)Y=m^2+T_n*h.

Set e=2k, N0=n^e, M=m^2, x=chi_A(e), y=psi_A(e). The standard recurrence
and norm give

    H=x+(n-A)y = N0 (mod T_n),
    J=x-(n-A)y,  HJ=1+T_n*y^2.

The four independent signs of X,Y imply respectively that T_n divides

    M-N0,  M+N0,  M*N0-1,  M*N0+1.

The frame has n,e,M<W. Hence N0<W^(W-1), M*N0<W^W<A<T_n, and
M+N0<W+W^(W-1)<W^W<T_n. The second and fourth divisibilities are impossible
by strict positivity. The third is impossible because N0>=4 and M is a
nonnegative integer, so M*N0 cannot equal one. Only X=x,Y=y remains, and
the first congruence gives M=N0 exactly. Thus m=+/-n^k and the actual main
Pell coordinates are positive, even before the sign of m is resolved.

For q-power outputs already known positive from their remainder bounds, this
immediately gives the intended power. For terminal successor-base outputs,
Section 1.1 gives the positive sign once their front division yields m=1 modulo q.
No factorial or binomial value is assumed to obtain this orientation.

## 6. The noncircular soundness order

The exact sign-inference certificate uses only integer polynomial identities,
positive monomials, and identified affine squares. Its omitted paired predicates
are restored first by the weighted interval lemma. The needed q>0 is independent:
the unchanged factorial remainder/slack predicates give

    B=fact_remainder+fact_slack+1>=1,
    q=B+choose_oslack+1>=2.

The retained anchor for the binomial remainder gives

    L=q*u+choose_rslack+2>=2.

Every other interval anchor is positive in the same way. No power is interpreted
in these statements. After all seven pair restorations, the emitted algebraic
closure has every required ordinary front sign. Its selected Y-slacks, comparison
coordinates, ordinary division quotients, and power outputs need no such sign.

1. The retained t-seed guard identifies Y=psi_A(t)>0 and X=+/-chi_A(t).
   Its request at base q has output L>=2. The signed power residue excludes the
   negative X: multiplying by q^t would force L*q^t=-1 under the strict frame
   bound, impossible. Hence L=q^t and this t pair is positively oriented.
2. The other t request now gives V0=(F^2+1)^t>0, even if the base was initially
   one. The literal ceiling F*B=V0+fact_slack and B>=1 imply F>=1. Moreover
   V0=(F^2+1)^t>=F^2+1, so F*B>=F^2+1 and B>F>=1. Thus B>=2 and q>=3.
   This precedes interpreting B as a binomial.
3. The retained K-seed guard and request N=B^K at base B>=2 orient that pair
   by the ordinary signed-output small-residue argument. Its other request is
   then q=N^K at positive base N>=2. Both equalities are now genuine.
4. The derived t+1 pair is still the original one-step addition from the
   positively oriented t pair. Its q^(t+1) output is correct. The two selected
   q-power seeds use Section 5 and their positive interval outputs to recover
   q^(y+1) and q^(x+1). All front divisors L are therefore positive powers of q
   of exponent at least one, and hence divisible by q.
5. Apply Sections 4-5 to the remaining eleven selected seeds. Their outputs
   have |m|=(q+1)^k. Every front digit/division equation gives m=1 modulo q
   through the explicit substituted remainder. Since q>=3, the negative sign
   is impossible. All eighteen original power equalities have been recovered.
6. Restore each original front remainder r=1+q*u>=1. Its exact old bound is
   r+s+1=L, so it is nonnegative and bounded. The original high-digit and range
   quotients, though initially signed, are nonnegative whenever required:
   m=L(C+q*h)+r, 0<=C<q, 0<=r<L and m>0 exclude h<=-1; similarly
   m=N*L*h+r with N>=1 excludes h<=-1. All remaining front meanings follow
   in the source's factorial, exact-binomial, prime-power lifting, CRT-range,
   and direct-calculus order.

For reference, the ordinary signed-output exclusion used in steps 1 and 3
needs no sign of the candidate m. With positive Y=psi_A(k), negative X would
give m*n^k=-1 after the small-residue argument. This is impossible for n>=2.
The frame bounds |m|,n,k<W ensure |m*n^k+1|<T_n. Positive X then gives
m=n^k. The exceptional base n=1 is used only after the pair is already oriented.

This recovers a genuine semantic front tuple. If the source theorem requires
its old private Pell witnesses rather than just the semantic interface, rebuild
fresh ones at its original indices and frame by Section 7. No pointwise claim
that doubled Pell coordinates solve an undoubled system is made.

## 7. Complete witness construction in the reverse direction

Begin with a genuine semantic front tuple supplied by the inherited natural
source, not with a hypothetical standard-model consistency assumption. Keep
its logical/arithmetic coordinates, and perform the following finite choices.

1. For each terminal successor-base division, take its genuine old remainder
   r and set u=(r-1)/q. As proved in Section 1.1, this is a nonnegative integer.
   Keep its old slack s. The new front equations and weighted sign predicates
   hold. Choose the frame W from the original base/exponent/output atoms.
2. Put A=chi_(W+1)(W), Z=psi_(W+1)(W)/W. The recurrence modulo W proves
   that Z is a positive integer. Set Zminus1=Z-1. This supplies the common
   frame norm and all positive moduli T_n.
3. For each of the two undoubled seeds choose (X,Y)=(chi_A(k),psi_A(k));
   for each of thirteen selected seeds choose (chi_A(2k),psi_A(2k)).
   Derive the t+1 pair by the unchanged one-step recurrence. Let
   P be the product of all fifteen seed ordinates squared.
4. In the finite ring (Z/(4P)Z)[s]/(s^2-(A^2-1)), A+s is invertible,
   with inverse A-s. A positive power is one. Its integer Pell coordinates
   give U=1 modulo 4P, Vaux=0 modulo 4P, U>0, Vaux>0. Thus P divides
   Vaux, and v=Vaux/P-1>=0. The Pell norm gives gcd(U,Vaux)=1; U is odd,
   so gcd(U,4Vaux)=1.
5. CRT supplies Baux=A modulo U, Baux=1 modulo 4Vaux. Increase it along
   that progression until Baux>A and Baux>1+4Vaux. Its two exact quotient
   witnesses and q4 are then nonnegative. For each actual requested index e,
   set S=chi_Baux(e), Raux=psi_Baux(e). Polynomial base transfer supplies
   S=X modulo U and Raux=e modulo 4Y. Their quotient witnesses are integers.
6. Every genuine output makes its unchanged or squared power congruence exact.
   For e=k or 2k the identity

       chi_A(e)+(n-A)psi_A(e)-n^e
         =T_n*sum_{j=0}^{e-1} n^(e-1-j)*psi_A(j)

   supplies the integer quotient directly. Fill every ordinary defining gate
   by its displayed polynomial. The retained t/K index slacks are nonnegative.
   Fill all retained sign triples using the three-square representation.

The choice order is front data, W, A and the main pairs, the common U,Vaux,
Baux, then comparison pairs and quotients. No later-chosen modulus is already
constrained by a residue depending on its future value. The common finite-ring
modulus contains all fifteen ordinate squares, so these choices are simultaneous.
This proves completeness. Using undoubled indices and the old frame gives the
fresh old certificate needed in the soundness map.

## 8. Exact algebra after the semantic change

The guard expansion and private-slack pruning leave a quadratic integer system.
The old Horn product is then factored exactly:

    (product L_i^2)*(Bguard^2+G^2)
      =(product L_i)^2*(Bguard^2+G^2).

The signed product is squared before being added to the two independent beta
squares; no cancellation argument is used. The guarded factor
((c-a)^2*(c-b)^2-(d+1)^2)^2 is likewise computed by first forming the signed
product (c-a)(c-b). The existing round14 factorization certificate records all
changed definitions and verifies that no altered intermediate escapes its
subnetwork. Its proof applies unchanged to the new front source.

Next, monic integral projection deletes only actual rows z-Q=0 (up to sign),
with integral Q of degree at most two. Every substitution is made everywhere
and checked not to increase any residual degree above two. A quadratic Q is
substituted only where z has no nonlinear occurrence outside its defining row.
Reverse substitution restores every deleted coordinate; unused coordinates may
be restored as zero. The separately pruned Y-slacks restore as Y-k.

Finally the final variables undergo integral translations. In particular old
t0=new_t-16, not new_t-1, absorbs the source's new lower-bound offset. The
additional recorded finite centering reduces coefficient height and support.
Every final shift is explicitly listed; old=new+shift and new=old-shift are
inverse maps on all integer tuples. These translations, unlike the remainder
restriction in Section 1, are genuine integral bijections. A deterministic
finite coordinate-descent search found them; no optimality is claimed.

The final polynomial is the sum of the squares of the resulting residuals.
An integer tuple makes that sum zero iff every residual is zero. The whole
collected expansion is regenerated exactly. The highest occurring degree is
four, and every retained variable occurs in the supplied polynomial.

## 9. Reproduction, dependency boundary, and credit

Run the following from the round15 package root:

    python direct/build_residue.py architecture/unified_derived_shell/raw direct/rebuilt_source --reparam
    python direct/center_integer.py direct/rebuilt_source direct/rebuilt_integer442

Only Python's standard library is required. Inputs are literal source JSON;
no upstream historical builder, network fetch, theorem prover, or solution
search is executed. The compiler records source hashes, all selected-index
changes, frame atoms, complete remainder substitutions, guard predicates,
weighted-pair anchors, exact private-slack inverses, Horn factorization,
monic projection, and final translations. The polynomial coefficients are
reconstructible from the printed residual specification and from these files.

The even-index parity argument and shared Pell completeness are credited to
the incoming Carriers and Even Indices package. Ordinary signed-output recovery,
square budgets, Horn factorization and exact sign closure are inherited from
round14 and related signed-power work. Shared remainder predicates are credited
to incoming Structural Compression; the new weighted version accompanies the
new quotient remainder. The unified factorial/product architecture has its own
attribution and proof in the architecture packet. The new contribution here is
their selective composition with residue-one orientation, which avoids a new
nonnegativity triple for each signed terminal power, and its complete smaller
integer quartics. Novelty and comparisons are relative to inspected sources.

Finite checks certify literal algebra and source binding. The unbounded Pell,
integer sign, remainder, factorial, CRT, and refutation arguments prove the
semantic equivalence. The named inherited formal calibration is retained as a
dependency; its full transitive theorem-prover closure was not rebuilt here.
