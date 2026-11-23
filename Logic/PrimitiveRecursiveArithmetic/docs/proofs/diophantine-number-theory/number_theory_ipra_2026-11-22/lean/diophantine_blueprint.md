# Diophantine formalization blueprint

## Status

The chapter supplies 20 human-readable theorem, lemma, and corollary statements
with proofs. DiophantineTargets.lean is an **uncompiled outline of definitions
and target propositions**. It has no admitted theorem proofs and asserts no
completed Lean certification. The Python companion exercises finite examples
and norm-quotient sign cases; it is not an iPRA proof checker.

There are two separate formalization tasks: prove the mathematical
specifications in Lean, and construct proof objects establishing their
translations in the chosen object-language iPRA calculus. The latter must
restrict induction to quantifier-free formulas. A Mathlib proof using
unrestricted Lean induction does not itself discharge that obligation.

## Representations

Use the repository's natural and signed-integer encodings. A sign bit and
magnitude, with negative zero normalized to zero, is a suitable alternative.
Addition, multiplication, order, and absolute value are finite cases.

RatCode stores an integer numerator and natural denominator. Validity means
positive denominator; reducedness adds coprimality. Equality and order use
cross multiplication. Normalization divides both coordinates by their gcd.
Invalid inputs receive a default. Reciprocal is specified under nonzero
numerator. Multiply all internal rational estimates by positive denominators.

A polynomial is a finite coefficient list. Horner evaluation is a fold;
rational evaluation clears a known denominator power. Lists inside iPRA are
number codes with explicit lengths and entry bounds. Their folds are fixed-fuel
primitive recursions. Ordinary Lean lists are convenient metalevel interfaces
and must be connected to object-language number coding.

The integer square root scans through 0,...,n and retains the last index whose
square is at most n. Its invariant records that inequality and that every
inspected larger index has square greater than n. The bounded universal
component is a Boolean fold.

CFState stores two preceding numerator and denominator continuants; cfStep is
a four-coordinate polynomial transition. No negative natural indices occur.
Validity requires positive coefficients after the first. The canonical final
coefficient test excludes a last 1 except in a one-entry list.

PellPair stores two signed integers. Its norm and pair product are explicit
polynomials. Positive solutions can equivalently be represented by naturals
satisfying x*x = 1 + D*y*y, avoiding truncated subtraction.

## Proof obligations and induction invariants

| Module | Ordinary Lean proof | Object-language invariant |
|---|---|---|
| Rational normalization | Equivalent reduced representative and uniqueness | Gcd certificate and exact division equations |
| Rational root test | Clear denominators; coprime cancellation | Horner identity for the processed coefficient prefix |
| Power obstruction | Rational monic root is integral; exponent divisibility | Prime-factor list and exponent-product identity |
| Pythagorean recovery | Parity, coprime square factors, parameter equations | Bounded root search checks both square identities |
| Square-area descent | Smaller right triangle with square area | Counterexample and hypotenuse at most original size minus stage |
| Quartic descent | Two parameter decompositions yield smaller solution | Quartic equation, positivity, and decreasing z |
| Continuants | Determinant, denominator positivity, bounds | Stored coordinates and determinant/growth identities |
| Tail error | Matrix identity and determinant cancellation | Finite product identity for the coefficient prefix |
| Rational collision | Box range; equal boxes imply close fractions | Marked-box count and no-collision test on the prefix |
| Simultaneous collision | Base-N vector code and equal-digit consequences | Digit-bound and code-range invariants |
| Pell approximants | Nonzero bounded norm and essential q>Y bound | Rational Dirichlet and integer-square-root certificates |
| Pell class collision | Matching residues make quotients exact | Class code below K; equal-class indices; increasing denominators |
| Pell quotient | Norm one and positivity for either norm sign | Norm identity and the two sign-comparison identities |
| Pell powers | Norm multiplicativity and strict increase | Norm one, positivity, coordinate bounds |
| Pell classification | Fundamental quotient decreases y | Quotient times recorded power equals input; decreasing y |

Each invariant is a conjunction of polynomial equalities, primitive recursive
comparisons, and bounded Boolean-fold equalities. It has a quantifier-free
formula in the language with symbols for the relevant primitive recursive
functions. Prove the initial case and step preservation, apply that induction
instance, and extract the final witness by projections.

## The uniform Pell argument

Define uniformly in D:

    C = 4*D + 2
    B = 4*(D+1)
    K = 2*C^3
    U = (B+1)^(K+1)
    H = 4*(D+1)^2*(U+1)^2

These are primitive recursive numerical functions. The theorem is one uniform
arithmetical assertion in D; no universal primitive recursive interpreter is
needed.

1. For Y put Q=B*(Y+1), A=isqrt(D*Q^4), r=A/Q^2. Prove
   1<=r<=D and 0<=D-r*r<2*D/Q^2+1/Q^4.
2. Extract a rational Dirichlet witness q<=Q and |p-q*r|<1/Q.
3. Factor the difference of squares to prove 0<|p*p-D*q*q|<C.
   Nonvanishing uses the rational-root obstruction for nonsquare D.
4. Assuming q<=Y makes that nonzero integer have absolute value less
   than one, a contradiction. This proves the crucial q>Y condition.
5. Generate K+1 pairs using T_0=0, T_(i+1)=B*(T_i+1).
   The invariant T_i+1<=(B+1)^i gives all coordinate bounds.
6. Encode (m,p mod |m|,q mod |m|) with a norm tag below 2*C and two
   slots below C. The class code is below K, so a collision exists.
7. Matching residues prove exact division in

       x=(p_i*p_j-D*q_i*q_j)/m
       y=(p_i*q_j-p_j*q_i)/m.

8. Expansion proves norm one.
9. Prove positivity for both signs of m using

       (p_i*q_j)^2-(p_j*q_i)^2 = m*(q_j^2-q_i^2)
       (p_i*p_j)^2-(D*q_i*q_j)^2 = m*(D*(q_i^2+q_j^2)+m).

   The second bracket is positive even for negative m, since
   D*q_i^2+m=p_i^2>0.
10. Prove the loose coordinate bound H, then the finite-box search is
    guaranteed to succeed.

The norm collision can return a power of the fundamental solution.
Minimality is a separate bounded search proved in the chapter.

## Continued-fraction names and represented reals

For each **fixed** primitive recursive coefficient function, instantiate its
code and positivity derivations. Finite tails give a rational Cauchy estimate;
taking the (2*k+2)-nd convergent gives error 2^(-2*k-2). This schema does not
quantify over arbitrary functions or posit a universal evaluator.

For simultaneous approximation of supplied real names, the theorem takes
certificates |xi_i-r_i|<=epsilon and gives

    |q*xi_i-p_i| < 1/N + N^d*epsilon.

An explicit dyadic precision yields the stated constant 3/(2N).
That is the result proved. No undecidable floor of a general constructive real
is assumed, and the sharp classical constant is not silently substituted.

## Repository integration

At the ProveIt snapshot pinned by the main report, the directory
Derivations/Lean/IPRADerivations/DiophantineNumberTheory contains modules named
Pythagoras, FermatQuartic, QuarticStep, SquareArea, FLTMultiples,
Dirichlet, DirichletReal, SimultaneousGrid, SimultaneousTransfer,
PellGeneral, PellDirichlet, PellCF, PellCFStep, PellAll, PellIndex, and
PellDescent.

Use the main report's audit to distinguish object-level derivations from
certificate interfaces, assumed input properties, and ordinary Lean theorems.
The norm/residue bound in this chapter needs its own proof chain; similarly
named modules do not certify it automatically.

## Reproduce the computations

From the package root run:

    python3 code/verify_diophantine.py

The checked-in JSON at verification/diophantine_checks.json records 16,545
exact-arithmetic cases, including norm collisions for all 90 nonsquare
integers from 2 through 100. Both common-norm signs occur. These checks detect
sign, indexing, and numerical-bound mistakes; they do not replace the
universal mathematical proofs or the formalization obligations.
