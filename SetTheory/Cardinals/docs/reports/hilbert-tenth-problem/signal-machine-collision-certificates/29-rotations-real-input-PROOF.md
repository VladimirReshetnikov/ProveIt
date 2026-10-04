# Exact real input obstruction for the five signal return

Companion theorem, 4 October 2026. Conventional mathematical proof, not a proof-assistant certificate. This document does not modify Reports 57–59 or their source packets. The physical construction and its exact chamber are inputs from the independently audited Report 57 construction. No claim of literature priority is made.

## Result and scope

For the audited fixed five-live-signal rational machine and its fixed 138-collision complete word, let V be the set of all positive **real** initial gap triples for which that word repeats legally forever. Then:

1. V is G_delta but not F_sigma, both relative to the positive-gap cone and as a subset of R^3. Its complement relative to the cone is F_sigma but not G_delta.
2. There is no exact certificate for V of the form

       g belongs to V  iff  there exist n in N^k and y in R^m such that Phi(g,n,y),

   valid for every positive real g, where k and m are finite and Phi is a finite Boolean combination of polynomial sign conditions with fixed real coefficients. In particular, no polynomial P(g,n) with a finite natural witness tuple can characterize V by existence of a zero on every positive real input.
3. In the ordinary exact Blum–Shub–Smale real computation model with field operations and sign/equality tests, V is not semidecidable, even if a proposed machine may use finitely many arbitrary fixed real constants. Its complement is semidecidable using rational constants alone. Thus V is properly co-semidecidable in that specified model.

These are exact real-input conclusions. They do not contradict the polynomial-time decision procedure on explicitly encoded rational inputs or the existential-positive integer-input result of Report 58. They assert neither Borel completeness, nor BSS degree completeness, nor Turing undecidability of encoded rational membership.

## 1 The audited mathematical input

For gaps g=(g1,g2,g3) in G=(0,infinity)^3, set

    d=g1+g2+g3,       x=g1,       y=g1+g2,
    xi=x-d/3,        eta=y-2d/3,
    z=(u,v)=(xi/d,eta/d).

The outgoing-section return is

    M=(1/30) [[7,-2,10],[14,11,-10],[-6,6,15]].

In the coordinates (d,xi,eta), it is diag(1/2,R/2), where

    R=[[3/5,-4/5],[4/5,3/5]].

Let C be the open rational polyhedral cone giving the exact complete-word chamber. Its 36 strict linear inequalities are necessary and sufficient; in particular a failed equality guard is a genuine failure of the prescribed complete collision word, not merely exit from a sufficient safety region. Then

    V={g in G: M^n g belongs to C for every integer n>=0}.

The audited normalized description is

    rho^2=4/1845,
    p=(4/205,-26/615),
    S={z in R^2: ||z||=rho},
    E={R^(-n)p: n>=0},
    K={z: ||z||<rho} union (S minus E),
    V={g in G: z(g) belongs to K}.

Here E is countably infinite and dense in S. For completeness, R has infinite order: its complex eigenvalue zeta=(3+4i)/5 cannot be a root of unity, because zeta+zeta^(-1)=6/5 would then be a rational algebraic integer and hence an integer. An infinite-order planar rotation has dense forward and backward orbits on each nonzero circle. In particular, the points of E are distinct.

The physical derivation of M, C and K is the dependency imported from the construction and its audit. All consequences below use these displayed objects; no new physical implementation is assumed.

## 2 The critical circle lies strictly inside the positive-gap domain

The normalized positive-gap domain is the open triangle

    D={(u,v): 1/3+u>0, 1/3+v-u>0, 1/3-v>0}.

The map

    (d,(u,v)) -> d(1/3+u, 1/3+v-u, 1/3-v)

is a homeomorphism from (0,infinity) times D onto G. Its inverse is the normalization in Section 1.

For ||z||<=rho, we have |u|<=rho, |v|<=rho, and |v-u|<=sqrt(2)rho. Since

    rho^2=4/1845 < 1/18,

both rho<1/3 and sqrt(2)rho<1/3. Every point of the closed radius-rho disk therefore belongs to D. This supplies a genuine fixed-scale critical circle entirely within the physically admissible positive-gap inputs.

## 3 Proper Borel class

Recall that F_sigma means a countable union of closed sets and G_delta means a countable intersection of open sets, in the indicated topology.

### Lemma 1

K belongs to Pi^0_2(R^2) minus Sigma^0_2(R^2): it is G_delta and is not F_sigma.

**Proof.** Write e_n=R^(-n)p. Since K is the closed disk with E deleted, its complement is

    R^2 minus K = {z: ||z||>rho} union E.

The exterior is F_sigma, explicitly

    {z: ||z||>rho}=union over m>=1 of {z: ||z||^2>=rho^2+1/m}.

Each set in that union is closed, as is each singleton {e_n}. Hence the complement of K is F_sigma and K is G_delta. An explicit open-set representation is

    K=(intersection over m>=1 of {z: ||z||^2<rho^2+1/m})
      intersect (intersection over n>=0 of (R^2 minus {e_n})).

Suppose K were F_sigma. Intersecting its closed-set decomposition with the closed circle S would make S minus E F_sigma relative to S. Let S minus E be the union of closed subsets F_j of S. Because E is dense in S, no F_j contains a nonempty relatively open arc. Thus each F_j is nowhere dense in S. Each singleton {e_n} is also nowhere dense because a circle has no isolated points. This would express S as a countable union of nowhere dense closed subsets, contrary to the Baire category theorem for the nonempty compact metric space S.

Equivalently, the supposition would make E a dense G_delta subset of S and hence comeager, although E is countable and meager. The Baire theorem forbids S from being both the union of E and its meager complement. This proves the claim. □

Only the elementary compact-space case of Baire is needed. One may prove that case directly: if a nondegenerate closed arc were covered by closed nowhere dense sets N_1,N_2,..., successively choose nonempty closed subarcs I_j inside the relative interior of I_(j-1), disjoint from N_j, with diameters tending to zero. Compactness gives a point of their nested intersection, which is outside every N_j. The same argument can start in any nonempty arc of S.

### Theorem 2

V is G_delta but not F_sigma relative to G, and is G_delta but not F_sigma in R^3.

**Proof.** Normalization g->z(g) is continuous on G. Its inverse image of K is therefore G_delta relative to G. Since G is open in R^3, this is also G_delta in R^3: a relative open-set representation is an intersection of ambient open sets together with G. Alternatively, the exact guard description expresses V as G intersect the countable intersection of the open sets (M^n)^(-1)(C).

For the negative direction, use the continuous fixed-scale embedding

    i:S -> G,
    i(u,v)=(1/3+u,1/3+v-u,1/3-v).

Its range has d=1 and lies in G by Section 2. We have i^(-1)(V)=S minus E. A continuous preimage of an F_sigma set is F_sigma. Thus if V were F_sigma relative to G, then S minus E would be F_sigma in S, contradicting Lemma 1's proof. Ambient F_sigma would imply relative F_sigma, so it is also impossible.

Taking complements gives G minus V in Sigma^0_2(G) minus Pi^0_2(G). Similarly R^3 minus V is F_sigma but not G_delta if nonpositive-gap inputs are classified as invalid. □

The result states a proper Borel class only. No Pi^0_2-completeness or continuous-reduction hardness claim is made.

## 4 Obstruction to finite existential mixed polynomial certificates

### Lemma 3

Every semialgebraic subset of R^a is F_sigma. Every countable union of semialgebraic subsets is consequently F_sigma.

**Proof.** For a real polynomial f,

    {f>0}=union over j>=1 of {f>=1/j},

and each term is closed. The same holds for {f<0}; {f=0}, {f>=0}, and {f<=0} are closed. Resolve complements and write a finite Boolean combination of sign tests as a finite disjunction of finite conjunctions of these atoms. F_sigma sets are closed under finite intersections and finite or countable unions, so the result follows. This proof uses a finite union of basic sign sets; it does not assume that every semialgebraic set is itself locally closed. □

### Theorem 4

There are no finite k,m and finite Boolean polynomial-sign formula Phi(g,n,y), with arbitrary fixed real coefficients, such that for every g in G,

    g in V  iff  exists n in N^k exists y in R^m Phi(g,n,y).

The same impossibility holds with Z^k in place of N^k.

**Proof.** Fix one integer tuple n. The set

    A_n={g in R^3: exists y in R^m Phi(g,n,y)}

is semialgebraic by the Tarski–Seidenberg projection theorem. This theorem applies to arbitrary fixed real coefficients and arbitrary finite Boolean combinations of polynomial signs. It has no boundedness or compactness hypothesis on y.

There are only countably many n in N^k (also in Z^k). The set A=union_n A_n is therefore F_sigma by Lemma 3. If the proposed equivalence held on G, then V=G intersect A would be F_sigma relative to G, contradicting Theorem 2. □

The argument also excludes a countable disjunction of such finite certificates, since a countable union of countable families of semialgebraic sets is still countable. It would even allow arbitrary finite real quantifier blocks after the integer tuple is fixed, since real quantifier elimination still gives a semialgebraic set. It does not address arbitrary alternation of real and integer quantifiers or additional nonpolynomial/oracle predicates.

In the special case

    exists n in N^k P(g,n)=0,

each fixed-n zero locus is already closed; no real projection theorem is needed. This sharpens the bare nonsemialgebraicity conclusion: allowing a finite tuple of unbounded natural witnesses still cannot produce the exact predicate on **all real g**.

This is not an obstruction to an integer-input Diophantine representation. A formula required to agree only for g in N^3 or for a discrete rational encoding can behave differently at the remaining real points. The induced subset of that discrete encoding space is a different definability/computability problem. In particular, Report 58's existential-positive integer-input certificate is outside the hypothesis of Theorem 4.

## 5 BSS semidecision lower bound

We use the standard finite-time exact real BSS model on a fixed finite input dimension. A program has finite control, finitely many fixed real constants, and real registers. Its permitted arithmetic is +, -, multiplication, and division where defined; it can copy/register-shift and branch on exact equality and order comparisons. Its ordinary discrete control and loops are allowed. It does not have a primitive for extracting an infinite digit sequence, performing a completed infinite computation, deciding arbitrary oracle predicates, or casting a real into an unbounded integer word in one step. No digit or floor primitive is assumed. Any finite algorithm expressible in the stated instructions remains allowed.

The formal model and relative semidecidability convention are documented in Gärtner–Ziegler, Section 1.4 and Definition 1.2; the same field-operation and finite-real-parameter model appears in Calvert–Kramer–Miller, Section 1. A set is semidecidable in a domain X if a machine halts on exactly its members among inputs from X. No condition on behavior outside X is necessary for this promised-domain definition.

### Lemma 5

A set A subset R^a semidecidable by such a BSS machine is a countable union of semialgebraic sets, and hence is F_sigma. A set semidecidable relative to G is F_sigma relative to G.

**Proof.** Unroll the finite program into its tree of finite computation paths. A finite path fixes the branch outcomes and all register accesses encountered on that path; it uses finitely many registers and instructions. Inductively, each encountered register value is a rational function of the input coordinates with coefficients in the field generated by the program's finitely many real constants.

The inputs following this path are constrained by the finitely many chosen branch outcomes and by nonvanishing of every divisor used. These constraints are semialgebraic. For example, where b is nonzero, a/b>0 is equivalent to ab>0; a/b=0 is equivalent to a=0 together with b!=0. Iterating such denominator bookkeeping handles rational expressions of any finite depth. Even if an expression admits cancellation, retain the original division-domain restrictions so that undefined intermediate computations are not admitted.

Consequently each finite accepting-path domain is semialgebraic. There are at most countably many finite paths in the finite-branching computation tree. Taking their union gives A. Lemma 3 yields F_sigma. In a promised domain, intersect the accepting-path domains with that domain; for G these intersections remain semialgebraic, and in any case the union is F_sigma relative to G. □

This is the standard path-decomposition argument. Gärtner–Ziegler, Corollary 2.6(a), explicitly records the resulting F_sigma upper bound, including relative domains.

### Corollary 6

V is not BSS-semidecidable in G. This remains true for machines with finitely many arbitrary fixed real constants. It is therefore also not BSS-decidable in G.

**Proof.** Otherwise Lemma 5 would contradict Theorem 2. Fixed real constants merely change polynomial coefficients along each finite path; they do not change semialgebraicity or countability of the paths. □

The claim is model-specific. It is not a theorem about all conceivable exact-real devices, real-oracle computation, infinite-time output conventions, or Type-2 machines receiving Cauchy names.

## 6 Explicit semidecision of invalidity

The complement has a direct rational BSS semidecision independent of any literature theorem. Start with q=g. Repeatedly evaluate the fixed chamber guards on q; halt with the assertion that the complete word is invalid if any strict guard fails; otherwise replace q by Mq and repeat.

Here is a finite exact specification of the chamber test, included so that the semidecision does not conceal a physical simulation or a stored event schedule. Starting from x=q1, y=q1+q2, d=q1+q2+q3, perform an A test, a B test, and another A test:

**A test.** At its current (x,y,d), form

    a0=x,
    a1=x-y/4,
    a2=x-y/4+d/6,
    a3=x-y/2+d/6,
    a4=x-y/2+d/3.

Require 0<y<d and 0<a_j<y for j=0,...,4, then replace x by a4 for purposes of the remaining chamber tests.

**B test.** At its current (x,y,d), form r=d-y and s=d-x, then

    b0=r,
    b1=r+2s/5,
    b2=r+2s/5-4d/15,
    b3=r+4s/5-4d/15,
    b4=r+4s/5-8d/15.

Require 0<s<d and 0<b_j<s for j=0,...,4, then replace y by d-b4 for the remaining A test.

Each block supplies 12 strict comparisons, giving the audited 36 after pullback to q. These local x,y,d updates only evaluate the chamber predicate; the persistent iterate q is separately replaced by Mq once the whole test passes. The contraction contributes no additional guards.

If g is valid, every tested guard remains strictly positive, so no finite prefix makes this procedure halt. If g is invalid, by the exact chamber/return characterization there is a finite n at which some guard of M^n g fails. The procedure reaches that n and halts. Equality is included in failure, which is essential for the excluded tangency orbit. Exact BSS comparisons support this test.

An alternative semidecision follows directly from K: normalize, halt if ||z||^2>rho^2, and otherwise enumerate e_n=R^(-n)p and halt if z=e_n. This is also a rational BSS procedure, but the guard procedure more directly ties the semidecision to finite failure of the audited complete collision word.

Thus G minus V is BSS-semidecidable, while V is not. This is exactly the asserted proper co-semidecidability. “Invalid” means that the specified repeated complete word fails; it does not assert that the underlying signal machine has no alternative subsequent behavior. If inputs outside G are to be invalid too, first halt whenever some input gap is nonpositive.

The contraction and its Zeno accumulation are irrelevant to this algorithmic classification: there is no instruction to inspect the limit of infinitely many physical collisions. The correctly reclosed uncontracted 114-event variant has the same normalized set, and the same conclusions follow with return 2M.

## 7 Why encoded rational membership remains polynomial time

For this fixed machine, the following is a deterministic decision procedure on binary encodings of rational gaps. First reject nonpositive gaps. Compute d and z by exact rational arithmetic and compare ||z||^2 with rho^2. Accept below the critical radius and reject above it. On the critical circle, put

    w=(u+iv)/(p_x+i p_y),       alpha=3-4i.

Then z is excluded exactly when w=(alpha/5)^n for some n>=0.

Let q be the least common positive denominator of the real and imaginary parts of w in reduced form. The denominator of (alpha/5)^n is exactly 5^n. Indeed, for n>=1, in the ring (Z/5Z)[i] with i^2=-1 we have alpha=3+i and

    (3+i)^2=3+i.

Hence alpha^n has coordinate residues (3,1) modulo 5 for every n>=1. Neither numerator coordinate is divisible by 5, so neither cancels any factor of the denominator 5^n. For n=0 the denominator is 1.

It follows that q determines the only possible n. If q is not a power of 5, accept. If q=5^n, compute alpha^n exactly and reject if and only if w=alpha^n/5^n. The case q=1 forces n=0, and only w=1 is then rejected. Orientation matters: forward powers of (3+4i)/5 are accepted boundary examples, not members of the forbidden inverse orbit.

To check bit complexity, let L be the total binary length of the six signed numerator/positive-denominator integers encoding the three rational gaps. A fixed number of rational arithmetic operations, comparisons, gcd calculations, and an lcm produces all normalized quantities and q with O(L) bits. Repeated exact division by 5 either finds q=5^n or proves otherwise, using at most O(L) divisions and giving n=O(L). The integer coordinates of alpha^n have O(n)=O(L) bits because |alpha^n|=5^n. Repeated multiplication by the fixed Gaussian integer alpha, followed by exact integer comparisons, therefore takes polynomially many bit operations. No factorization, orbit-density search, or numerical approximation is needed.

The elementary and polynomial-time character of this encoded procedure is fully compatible with the real-input lower bound. An exact real input supplied as a register value is not supplied with numerator/denominator data, and the real-input procedure must also cover irrational inputs.

## 8 Finite unions of forbidden orbits

The topological and certificate arguments use only that E is countable and dense in a nondegenerate circle. Therefore they remain true if E is any nonempty finite union

    E=union over j=1,...,r of {R^(-n)p_j:n>=0},

where every p_j lies on the same nonzero circle and R has infinite order. Orbit intersections or duplicated orbit representatives do not affect the argument. The same normalization transfer works whenever that circle is inside the positive-gap domain, as it is for Report 57.

A weaker sufficient transfer hypothesis is that the admissible normalized domain contains a nondegenerate closed arc J of S. Replace S by J in the Baire proof and in the fixed-scale embedding; E intersect J is countable and dense in J, and J is a perfect compact metric space. This handles a circle with a few inadmissible boundary contacts whenever an admissible arc remains.

### Corollary 7 for the audited Report 59 family

Fix any compiled Report 59 member: a rational infinite-order rotation, a positive rational scaling, and its finite rational complete-word chamber. Its exact all-real positive-gap validity set is G_delta but not F_sigma, has no finite existential mixed real/integer polynomial certificate of the form in Theorem 4, and is properly co-semidecidable in the stated BSS model.

**Proof.** Import the audited family geometry, specifically its PROOF.md Sections 6 and 6.1: the normalized closed critical disk lies in the closed initial-order triangle, its finite nonempty tangency list lies on the nonzero critical circle, and validity is the disk with the union of the corresponding backward orbits deleted. The three initial-gap affine forms are strictly positive at the origin and nonnegative on the whole closed disk. Each can vanish on the critical circle at at most its single perpendicular contact point. Thus only finitely many circle points lie outside the positive-gap triangle, and there is a nondegenerate closed arc J wholly inside it.

Apply the preceding closed-arc version of the Baire argument and normalization transfer to J. The certificate and BSS lower bounds follow from exactly the same F_sigma arguments. For complement semidecision, the rotation and finite tangency list have rational entries: normalize, halt outside the disk, and enumerate the backward iterates of all tangencies, halting at an exact match. Alternatively use the family's finite strict guard list and rational return. Hence complement semidecision uses rational constants alone. Positive scaling cancels in the normalization. □

This specialization relies on the passed family audit; it is not a new physical or arithmetic audit of Report 59. In particular, the family's polynomial-time rational-input theorem and its existential-positive integer-input certificates remain compatible with Corollary 7. The Report 57 instance already establishes all preceding theorems independently of this extension.

## 9 Dependency and claim boundaries

- Physical dependency: the audited exact M, strict chamber C, and omitted inverse-orbit formula for K
- General mathematics: elementary Baire category, Tarski–Seidenberg, and finite BSS path decomposition
- Application proved here: proper G_delta topology, exclusion of finite existential mixed real/integer polynomial certificates on all real gaps, and proper BSS co-semidecidability for this actual five-signal set
- Preserved distinction: polynomial-time encoded rational membership and integer-input certificates are compatible with all three real-input conclusions
- Not claimed: Borel completeness, BSS completeness, a general Diophantine impossibility for integer inputs, arbitrary quantifier-alternation lower bounds, Type-2 classifications, physical hypercomputation, or literature priority

Primary-source verification and precise source pins are in SOURCE_NOTES.md. No upstream program, physical simulator, or saved collision schedule was executed for this companion.
