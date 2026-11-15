# Lean formalization blueprint: finite Puiseux packets

**Status:** The source file is an uncompiled interface. This document lists
the missing implementations and proof obligations. It is not a list of
axioms, and it does not claim a completed Lean proof.

The inspected target is ProveIt commit
`d851229c33ef395db8dc04baf28c6a291073f61e`, Lean 4.32.0.
Use `ConciseIPRA.PR` for the object theory and optionally
`ConciseIPRA.NativeBiInterpretation` for the final transport.

## 1. Two layers, with a precise internal endpoint

The executable layer manipulates natural codes for finite exact algebraic
numbers, rational functions, polynomials, arrays, and certificates.

The structural algebra layer may first use an abstract decidable,
effectively presented algebraic coefficient field. It organizes finite
identities and coefficient recurrences. These Lean propositions are not
automatically iPRA derivations.

The final internal endpoint is

```lean
Prf PRAAx [] (PuiseuxSentence concretePrograms)
```

from `PuiseuxTarget.lean`. The fields of `Programs` must be replaced
by concrete `PR` syntax trees. Their semantics must be proved before
the formula can be described as Puiseux's theorem.

## 2. Finite data types

Suggested executable data (eventually coded by natural numbers):

```text
Input:
  exact algebraic base point and coefficients of P(X,Y)
  degree d>=1 and exact leading-coefficient witness

SquarefreePacket:
  coefficient a_d(X)
  monic rational-function factors Q_m
  multiplicity labels m
  common denominator C(X)
  integral monic F_m(X,Z)=C^n_m Q_m(X,Z/C)
  Bezout and product-identity certificates

NewtonPacket:
  F=product F_m, delta=ord Disc(F)
  N=(d!)^d, Delta=N delta, h=Delta+1, M=2h+1
  B=d N(delta+1), J=max(M,B)+d^2 B+2
  finite labelled Newton/Hensel tree
  b_i modulo T^M for every distinct leaf

SimpleLeaf:
  original label m
  a_i=prefix of b_i THROUGH degree h
  s_i<=Delta
  H_i(T,U)=T^(-(h+s_i))F_m(T^N,a_i+T^h U)
  nonzero derivative H_i,U(0,0)
  rational coefficient bounds beta_i
  rational S_i, r_i=1/(4S_i), rho_i=1/(16S_i^2)

OutputPacket:
  common pole bound p=N*ord C
  denominator unit E(T)=T^(-p)C(T^N)
  all SimpleLeaf records
  pairwise first-difference witnesses at indices <=Delta
  positive common radius R
  weighted-norm bounds M_i for W_i=(a_i+T^h U_i)/E

Jet(p,L):
  coefficients W_i,0,...,W_i,L for each distinct branch
  nonnegative rational coefficient majorants
  labels m and references to finite packet data
```

There is no need to store a general function `Nat → Complex` in the
executable packet. The coefficient generator is one fixed PR program.

## 3. Polynomial and jet primitives

Use a fixed convention:

```text
Jet K L = list of L coefficients, indexed 0,...,L-1
ModEq L A B = coefficients below L agree
```

A sparse bivariate polynomial list stores triples (T exponent, Y exponent,
coefficient). All operations use finite bounds on those lists and the
requested jet length. Required primitives:

- finite coefficient access with zero outside the list;
- normalized polynomial addition/multiplication/Horner substitution;
- coefficientwise congruence modulo T^L;
- ramification T↦T^q;
- translation Y↦Y+a(T);
- monomial division, guarded by a finite divisibility check;
- finite Hasse derivative/Taylor identity;
- resultant and discriminant determinants.

Example goal shapes, in Lean-style notation:

```lean
modEq_mul :
  ModEq L A A' → ModEq L B B' →
  ModEq L (mul A B) (mul A' B')

modEq_eval :
  ModEq L A A' → ModEq L z z' →
  ModEq L (evalY A z) (evalY A' z')

hasse_taylor :
  evalY F (a + v) =
    sum_{k≤degreeY F} (evalY (hasseY k F) a) * v^k
```

These are expected lemma types; no declaration of them as an axiom is
intended.

## 4. Original polynomial decomposition

Prove the squarefree algorithm by polynomial Euclidean division over the
encoded rational-function field. Its invariant is a finite product identity
with derivative-gcd and degree certificates. At every step degrees fall.

The central postcondition is

```text
P/a_d = product_m Q_m^m
sum_m m*degreeY(Q_m)=d
Q_m monic
gcd(Q_m,Q_m')=1
gcd(Q_m,Q_n)=1 for m≠n
```

After choosing C, check by exact denominator clearing that every F_m is
monic in K[X,Z]. Prove

```text
P(X,Y)=a_d(X) C(X)^(-d) product_m F_m(X,C(X)Y)^m.
```

The expression is an identity in K(X)[Y], with an equivalent polynomial
identity obtained by multiplying by C^d. The latter is the internal checker
condition.

## 5. Finite Newton–Hensel construction

Implement the tree as a bounded array/stack. Use d rounds and at most 2d-1
nodes. Every active node stores degree, cumulative ramification e, available
precision, its polynomial coefficient arrays, and finite discriminant data.

Required induction invariants:

```text
sum of current leaf degrees = initial degree
current e divides N and e<=d!
node discriminant order <=e*delta
all available arrays are correct modulo their recorded precision
remaining precision >=requested precision + remainingLevelReserve
```

A coefficient scan through B determines the least rational slope. A
transformation uses at most dB extra input digits. Child degrees are all
strictly smaller because the centered characteristic polynomial is not a
pure power.

The Hensel correction at order k uses the fixed polynomial Bezout inverses
of the coprime constant factors:

```text
U_j,k = remainder(E_j * residual_k, C_j).
```

One bounded coefficient loop computes all lifts. Prove the product
identity modulo T^(k+1) and independence from later requested precision.

Expected theorem:

```text
valid SquarefreePacket
  -> finiteNewton(packet,J)
       returns b_i modulo T^M
       with F_m(T^N,Z)=product_(label_i=m)(Z-b_i) mod T^M.
```

No infinite series evaluator is used.

## 6. Finite discriminant and separation

Since discriminant is a finite polynomial expression in the coefficients,
it preserves ModEq M. Apply the product discriminant identity to the
finite b_i list.

Expected contracts:

```text
disc_congruence:
  ModEq M (Disc(F)(T^N)) (product_(i<j)(b_i-b_j)^2)

finite_separation:
  coefficient Delta of Disc(F)(T^N) !=0
  and all earlier coefficients =0
  -> for every i<j a computable w_ij<=Delta and nonzero
     coefficient lead_ij exist, with
     b_i-b_j = T^w_ij*(lead_ij + higher terms) mod T^M
  -> 2*sum_(i<j)w_ij=Delta
```

All witnesses are found by scans through Delta. The coefficient-field
zero test applies only to finite algebraic numbers.

## 7. Desingularization from M digits

For each labelled root define a_i from coefficients through h. The finite
proof uses M=2h+1 and b_i-a_i divisible by T^(h+1).

Expected goal:

```text
simple_leaf:
  finite factorization mod M
  + discriminant/separation certificates
  -> s_i=ord F_m,Z(T^N,a_i)<=Delta
  -> T^(h+s_i+1) divides F_m(T^N,a_i)
  -> H_i=T^(-(h+s_i))F_m(T^N,a_i+T^h U) is polynomial
  -> H_i(0,0)=0 and H_i,U(0,0)!=0
```

The proof is finite Taylor expansion. For U-degree at least 2 the
T-exponent after division is at least h-s_i>=1. The linear U coefficient
at T=0 is the recorded nonzero derivative coefficient.

## 8. Coefficient recurrence

For a simple leaf set Phi=U-H_U(0,0)^(-1)H. The coefficient at (0,0)
and (0,1) vanishes.

Expected definitions and goals:

```text
u_0=0
u_k=coeff k (Phi(T,sum_(ell<k)u_ell T^ell))

coefficient_recursion_correct:
  H(T,sum_(k<L)u_k T^k)=0 mod T^L

coefficient_recursion_unique:
  two zero-constant L-jets solving the same H mod T^L agree

prefix_compatible:
  take L (simpleCoeffs H (L+1)) = simpleCoeffs H L
```

All sums, products and substitutions are bounded by L and the finite
degree of H. This is a single PR recursion.

Set z_i=a_i+T^h U_i. It agrees with a_i through h, so the finite
first-difference certificates remain valid.

## 9. Complete factorization by finite cancellation

Synthetic division over an arbitrary commutative ring factors Y-z_i from
a polynomial vanishing at z_i. For subsequent roots use the recorded
leading coefficient of z_j-z_i to cancel.

Expected finite cancellation lemma:

```text
leading A at w is a nonzero algebraic number
and A*B =0 mod T^(L+w)
    -> B=0 mod T^L.
```

Prove it by induction on the coefficient index, dividing by the fixed
nonzero leading coefficient. Summing the necessary precision losses costs
at most Delta. To obtain coefficients through degree L, use residual
congruences modulo T^(L+Delta+1).

After all n_m roots are extracted, monicity and degree force the remaining
factor to be 1. This is a finite degree argument. It yields full formal
factorization at every requested precision without choosing an index from
an undecidable vanishing-product disjunction.

## 10. Rational majorants and tail estimates

Use rational coefficient majorants instead of taking square roots inside
the arithmetic proof. If v_k is the nonnegative majorant coefficient,
check

```text
normSquare(u_k) <= v_k^2,
sum_(k<L) v_k*rho^k <= r.
```

The first inequality uses exact real-algebraic order and the second is
pure rational arithmetic. The positive Picard polynomial proves the
weighted sum bound by finite induction. Truncate all Picard iterates
modulo T^L; truncation preserves every relevant coefficient and only
decreases their nonnegative weighted sum.

After unit inversion and finite convolution obtain rational majorants
wMajor_i,k for W_i with

```text
normSquare(W_i,k) <= wMajor_i,k^2,
sum_(k<L) wMajor_i,k*R^k <= M_i.
```

Then the purely rational finite tail certificate is

```text
N<M ->
sum_(k=N+1)^M wMajor_i,k*(R/2)^k
    <= M_i*2^(-(N+1)).
```

For an evaluated Laurent series multiply by eta^(-p), where eta>0 is
a supplied lower bound for |T|. The internal result remains a finite
estimate; the Cauchy-name interpretation is a separate semantic layer.

## 11. Exact specification of factorJet

Let p=N*ord C and let W_i be the normalized power-series jets with label_i.
The checker must compare finite coefficients of the explicit identity

```text
sum_(r=0)^d T^((d-r)*p)*a_r(T^N)*Z^r
  =
a_d(T^N) product_i (Z-W_i(T))^(label_i).
```

Compare each Z degree 0,...,d and each T degree up to the requested
cutoff. Every exponent on the left is nonnegative.

The `factorJet` field in the interface refers to exactly this finite
identity, not merely to independent small residuals of the roots.

## 12. Object-theory assembly

Compile all loops from explicit `PR.comp` and `PR.prec` constructors.
Every invariant above must be a Boolean-coded FINITE condition. Keep
arbitrary cutoffs as ordinary numerical parameters and quantify them only
after applying `PRA.qfInd`.

The implemented tuple must prove:

- valid input -> valid packet;
- valid input -> factorJet at each cutoff;
- prefix compatibility;
- the finite coefficient majorant bounds;
- the finite rational tail bound.

Then construct the object derivation of `PuiseuxSentence`. The existing
`pra_iff_native` transports it to the concise calculus. The theorem
`suppliedDerivation_toNative` in the interface illustrates ONLY this
last step and assumes that the derivation has already been constructed.

## 13. Verification boundary

A completed project should:

1. Compile the interface at the pinned repository revision.
2. Test exact finite computations against independently computed examples.
3. Complete decoding theorems for arithmetic/checker codes.
4. Build the object derivation with no postulated Puiseux result.
5. Inspect the final theorem type and `#print axioms`.
6. Rebuild the entire dependency closure from pinned source.
7. Keep the semantic convergent-series corollary separate from the
   logical-strength certificate.

None of these steps is replaced by a successful conventional Lean
complex-analysis proof or an example program passing tests.

