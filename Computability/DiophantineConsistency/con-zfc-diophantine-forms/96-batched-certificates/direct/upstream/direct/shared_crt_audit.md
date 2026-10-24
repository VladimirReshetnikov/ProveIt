# Independent audit of the shared CRT certificate

The source theorem is correct with a common scalar witness bound. A crucial
detail is that soundness decodes modulo one prime divisor of each CRT modulus,
not modulo the entire generally composite modulus.

## Precise theorem

Let E and F be fixed polynomials with nonnegative integer coefficients in
coordinates (i,z_1,...,z_r,w_1,...,w_m). Fix N,z in the nonnegative integers.
The statement

    for every i < N there exist w_1,...,w_m >= 0 with E(i,z,w)=F(i,z,w)

is equivalent to existence of U,A_1,...,A_m,C >= 0 with the following
definitions and conditions:

    H = E(N,z,U,...,U) + F(N,z,U,...,U) + N + U + 1
    T = H!
    d_i = 1 + (i+1) T
    B = product_{i<N} d_i
    B divides (U+1)! binom(A_j,U+1) for every j
    B divides 1 + (C+1)T
    E(C,z,A) congruent F(C,z,A) modulo B.

The empty product for N=0 is 1, so this theorem includes the vacuous case.
Products, factorials and binomial coefficients here are arithmetic macro
relations; they must be replaced by fixed polynomial certificates before
claiming a single ordinary Diophantine equation.

## Soundness

Assume N>0 and fix i<N. Since T>=1, d_i>=2 has a prime divisor p.
Because d_i is 1 modulo every divisor of T, p does not divide T=H!.
Consequently p>H. In particular p>N and p>U.

Since d_i divides B, all asserted divisibilities hold modulo p.
Comparing 1+(C+1)T and 1+(i+1)T modulo p, and cancelling the nonzero
residue T, gives C congruent i modulo p.

The integer polynomial identity

    (U+1)! binom(A_j,U+1) = product_{k=0}^U (A_j-k)

holds also when A_j<U+1: then a zero factor makes both sides zero.
Primality gives a k_j in {0,...,U} with A_j congruent k_j modulo p.
Put w_j=k_j. Polynomial congruence gives

    E(i,z,w) congruent F(i,z,w) modulo p.

Both values are nonnegative and no larger than
E(N,z,U,...,U)+F(N,z,U,...,U)<H<p, by coefficientwise monotonicity.
They are therefore equal as ordinary integers. This supplies the required
local witnesses for every i<N.

It is false in general that A_j modulo d_i lies in [0,U]. For example,
6*binom(16,3)=16*15*14 is divisible by 35, although 16 modulo 35 is not
in [0,2]. Decoding the prime divisors 5 or 7 gives valid bounded roots.
This negative control is illustrative; the numerical pair does not itself
instantiate the factorial choice of T in the main theorem.

## Completeness

Choose one local witness tuple for every i<N. Finite choice suffices.
Choose U at least every selected coordinate (U=0 suffices when N=0).
Then H>=N and T is divisible by every positive integer <=N.
For i<k<N, any common divisor of d_i,d_k is coprime to T and divides
(k-i)T, hence divides k-i; since k-i divides T, the common divisor is 1.
Thus the d_i are pairwise coprime.

The ordinary finite CRT supplies each A_j with A_j congruent w_{ij}
modulo d_i, and C congruent i modulo d_i. Choose nonnegative
representatives. The falling-factorial product vanishes modulo each d_i,
because it contains A_j-w_{ij}. The index and evaluation congruences
also hold modulo each d_i. Pairwise coprimality promotes all three types
of congruence to divisibility by B.

## Formalizability scope

The theorem uses only finite polynomial arithmetic, finite CRT, factorials,
Euclid's lemma and finite induction. ZFC proves these facts about its internal
natural numbers; the reasoning does not need a model of ZFC, arithmetic
soundness, a consistency assumption or a restriction to standard naturals.
An ordinary detailed derivation formalizable in ZFC is distinct from a
supplied object-language derivation checked by Lean. The latter is not
asserted by this audit.

## Power primitive audit checklist

The repository PowerRepresentation finite certificate uses truncated
subtraction a-n. A direct integer subtraction can replace it only after
proving a>=n. In the nontrivial positive-base branch, n<=w, a>1 and

    a^2 - ((w+1)^2-1) (w z)^2 = 1

give z>0 and then a>w>=n, so the replacement is valid. The branches
n=0 or exponent=0 must either be retained or treated separately with an
explicit proof. Pell-index conditions include a>1 and exponent<=Pell_y;
dropping these side conditions invalidates the cited characterization.

The modulus 4*Pell_y can be zero in the Pell base case. If a polynomial
congruence gadget uses signed quotient witnesses, modulus zero correctly
means exact equality. If it uses Euclidean quotient/remainder witnesses,
zero requires an explicit case or may only be invoked in the positive
Pell_y branch. Similar care applies to division denominators in the
factorial/binomial macros.

## Final optimized source audit

The separately authored theorem in `agent_direct/shared_crt_theorem.tex`
has been read in full. Its heterogeneous bounds and factorial cancellation
are correct. Specifically H>=u_j+1 implies (u_j+1)! divides T, whereas
gcd(B,T)=1. Thus the certificate can impose B|binom(A_j,u_j+1) directly.
The three formula labels use bound m; the remaining ten local coordinates
use bound V=m+U. This removes the three local label-bound slack coordinates.
The CRT proof never infers a bounded residue modulo a composite modulus.

The concrete builder uses t=t0+1, m=m0+1 and each encoded coordinate
A_j=alpha_j+1. Positive t and m lose no valid certificate because the
distinct endpoints exclude t=0 and a zero label bound makes every step
constant. Positive A_j lose no CRT solution: add a positive multiple of B
to a zero CRT representative. Divisibility of the binomial is preserved
under this lift by its falling-factorial identity and cancellation of
(u_j+1)! modulo B; binomial coefficients themselves should not be assumed
to be ordinary integral-coefficient polynomials in A_j.

These shifts justify the positive power specialization. The arithmetic
construction has 55 power calls. A separate static induction through their
ordered macro records and arithmetic gates proves both arguments positive
at every call, starting only from nonnegative external variables and the
literal added ones. Once the arguments of a power are positive its output
is at least one; factorial outputs are at least one. No unproved positivity
of an arbitrary local or quotient witness is used.

For a positive power call m=n^k, n,k>=1, the builder's conditions translate
exactly to the repository criterion. Its Pell index witness Y satisfies
Y>=k>=1. Hence the Pell base alternative (X,Y)=(1,0) is impossible, and
the nontrivial Pell branch suffices. V=Y^2(vd+1) is equivalent to V>0 and
Y^2|V on this domain. B=1+4Y*q4 is equivalent to B congruent 1 modulo 4Y
because B>1. The three auxiliary congruences use signed quotients split
into two natural witnesses, so either sign of the integer quotient is
permitted. A>=2 and W>=n>=1, together with the final norm, force Z>=1:
Z=0 would imply A^2=1. Then

    A^2 = 1 + W^3(W+2)Z^2 > W^2,

so A>W>=n. Consequently X+Yn congruent YA+m modulo T is exactly the
required congruence X congruent Y(A-n)+m, including the repository's
truncated natural subtraction. T=m+gap+1 enforces the strict output bound.

In the unrestricted power mode, the zero-exponent and zero-base branches
are selected by natural Boolean variables whose sum is one. Every
nontrivial equation is guarded, while unguarded arithmetic gates merely
compute additions and products on natural inputs. The inactive branch
auxiliaries can therefore be assigned arbitrary natural values, with gate
values then uniquely determined. This validates the retained total-power
comparison construction, including 0^0=1.

The binomial graph correctly combines quotient and digit extraction in one
identity A=D(qh+b)+r, with 0<=r<D and 0<=b<q. Here q=2^n+1 and D=q^k.
The factorial graph correctly enforces

    numerator+c-1 = c*out+remainder, 0<=remainder<c,

which is the ceiling quotient from the cited factorial formula. Its
denominator c=binom(radius+n,n) is positive. The product graph correctly
uses a positive modulus Tq-1 and a bounded remainder. No variable exponent,
binomial, factorial, division or remainder symbol remains in the exported
quadratic rows.

## Independent implementation controls

The separate checker `agent_routes/check_equation.py` reads the actual
quadratic rows and independently expands their sum of squares. It matches
the delivered ordinary sparse polynomial exactly and checks variable
indices, canonical row monomials, full variable use, and exact degree four.
It also constructs complete Pell certificates for six positive power
fixtures, including 3^2, checks five exponent-zero and five base-zero
fixtures in total-power mode, rechecks the six positive fixtures in the
specialized graph, and rejects corresponding changed outputs. The
binomial controls exercise the actual graph builder with separately exact
power outputs for 63 input pairs, including k>n. Factorial and CRT-product
identities receive 20 and 30 arithmetic controls. The shared-CRT fixture
uses three different rows and verifies the factorial-free divisibility.

Normal and optimized Python runs pass. These controls do not determine
whether the complete consistency equation has a zero, and they are not a
formal proof of the universal semantic theorem or its inherited C222/ZFC
calibration. No implementation gap was found in the stated audit scope.

## Nonnegative affine gate elimination

The later export optimization is sound. If a gate coordinate g has the
monic defining equation g=L, where L is an affine polynomial with
nonnegative integer coefficients in earlier coordinates, substitute L
through every remaining residual and remove this defining equation and g.
For every natural assignment to the retained coordinates, L supplies a
unique natural restoration of g. Forward projection and backward
restoration therefore preserve the entire zero set. Substitution of an
affine polynomial in a quadratic residual preserves degree at most two.
Repeating the operation in topological order preserves this conclusion.
The support cap of four terms is an implementation size choice, with no
role in the correctness argument.

The independent checker infers every eliminated coordinate from the
original builder rows and the final list of retained variable names. It
does not call the exporter or use its recorded substitution map. For each
removed coordinate it checks monicity, triangularity and a nonnegative
affine restoration. It then substitutes those expressions into every
original row and compares the complete nonzero row multiset with the
delivered residuals, exactly over the integers. This proves the finite
algebraic row identities, independently of any unknown full solution.

The first optimized export removes 2968 affine variables from the previous
7272-variable representation, leaving 4304 variables and 3644 quadratic
rows. Its expanded quartic has 24602 terms and maximum absolute coefficient
248626296. These figures describe that particular build; the checker
recomputes them and does not hard-code them, so later source improvements
must be replayed before making updated claims.

## Frozen literal-calculus builds

The final builder additionally computes the original numerical constructors
directly, rather than re-evaluating their expanded coefficient lists. The
constructor module is `direct_calculus.py`; its own compositional identity
audit is a separate dependency supplied with the package. The complete
independent arithmetic and affine checks have been replayed on this source.

| Variant | Variables | Quadratic rows | Quartic terms | Maximum absolute coefficient |
|---|---:|---:|---:|---:|
| Default affine elimination | 3614 | 2954 | 15996 | 127778545 |
| Retained affine wires | 6183 | 5523 | 17430 | 1993 |

The first variant removes 2569 nonnegative affine gates from the second.
The independent row-multiset identity proves the restoration exactly;
neither count is inferred from a local witness count. Both have degree
exactly four. Both pass the same macro, power-positivity and CRT controls
in normal and optimized Python. The receipts also record the hashes of
both the builder and the literal-calculus module, so changes in either
source invalidate the recorded audit identity.
