# Recursive decidability of radical solvability for integer quintics and sextics

## Statement

Encode a quintic by six signed integers

$$
(a_0,a_1,a_2,a_3,a_4,a_5), \qquad a_5 \ne 0,
$$

representing

$$
f(X)=a_5X^5+a_4X^4+\cdots+a_0.
$$

Let $\operatorname{Rad}(f)$ mean that every complex root of $f$ has a
finite expression made from rational constants, field operations, roots of
unity, and extraction of nonzero-order radicals. This is the exact predicate
called `all_roots_radical_int` in the accompanying Rocq development.

**Theorem.** The characteristic predicate $\operatorname{Rad}(f)$ on
integer quintics is recursive. In fact, the coefficient procedure below is
primitive recursive.

The theorem concerns individual input equations. It is different from
Abel--Ruffini's statement that there is no single radical formula solving
every quintic.

## A bounded coefficient algorithm

### 1. Make the polynomial monic without changing the question

Put

$$
B=a_4,\quad C=a_3a_5,\quad D=a_2a_5^2,\quad
E=a_1a_5^3,\quad H=a_0a_5^4,
$$

and form

$$
F(Y)=a_5^4f(Y/a_5)
    =Y^5+BY^4+CY^3+DY^2+EY+H\in\mathbb Z[Y].
$$

The roots of $F$ are exactly $a_5$ times the roots of $f$.
Multiplication or division by the nonzero rational number $a_5$ is allowed
inside a radical expression. Hence

$$
\operatorname{Rad}(f)\quad\Longleftrightarrow\quad
\operatorname{Rad}(F).
$$

The corresponding roots also generate the same splitting field over
$\mathbb Q$.

### 2. Decide reducibility by a finite search

Let

$$
R=1+\max(|B|,|C|,|D|,|E|,|H|).
$$

Cauchy's bound says that every complex root of $F$ has absolute value at
most $R$. If the monic quintic $F$ is reducible over $\mathbb Q$,
Gauss's lemma gives a factorization by monic polynomials in
$\mathbb Z[Y]$. Taking the smaller side of a nontrivial factorization
gives a monic factor of degree one or two.

A monic linear factor is $Y+c$, with $|c|\le R$. A monic quadratic
factor is $Y^2+bY+c$. Its two roots are roots of $F$, so Vieta's
relations give

$$
|b|\le 2R,\qquad |c|\le R^2.
$$

It therefore suffices to enumerate

$$
-R\le c\le R
$$

for linear factors, and

$$
-2R\le b\le 2R,\qquad -R^2\le c\le R^2
$$

for quadratic factors, testing exact polynomial divisibility in each case.
This bounded integer computation detects every reducible quintic, including
quintics with repeated factors.

If a factor is found, answer **yes**. Every irreducible factor of a reducible
quintic has degree at most four. Its Galois group embeds in $S_d$ for some
$d\le4$, and $S_d$ is solvable in those degrees. In characteristic zero,
the Galois criterion for solvability by radicals therefore gives a radical
expression for each root of each factor, hence for every root of $F$.

### 3. Depress the irreducible quintic

If the bounded search finds no factor, $F$ is irreducible. Substitute
$Y=Z-B/5$. The result is

$$
g(Z)=Z^5+pZ^3+qZ^2+rZ+s,
$$

where

$$
\begin{aligned}
p&=C-\frac{2B^2}{5},\\
q&=D-\frac{3BC}{5}+\frac{4B^3}{25},\\
r&=E-\frac{2BD}{5}+\frac{3B^2C}{25}-\frac{3B^4}{125},\\
s&=H-\frac{BE}{5}+\frac{B^2D}{25}-\frac{B^3C}{125}
     +\frac{4B^5}{3125}.
\end{aligned}
$$

This rational translation again preserves radical expressibility.

### 4. Apply the Frobenius sextic criterion

Compute the fixed sextic $R_{20}(T;p,q,r,s)$ displayed in equation (2) of
Dummit's paper. It is monic in $T$, and each of its coefficients is one
fixed integer polynomial in $p,q,r,s$. Evaluating that finite coefficient
formula is therefore a rational-arithmetic computation.

For an irreducible rational quintic, Dummit's Theorem 1 states

$$
g\text{ is solvable by radicals}
\quad\Longleftrightarrow\quad
R_{20}(T;p,q,r,s)\text{ has a rational root}.
$$

The group behind the criterion is

$$
F_{20}
=N_{S_5}\!\left(\langle(1\,2\,3\,4\,5)\rangle\right)
\cong C_5\rtimes C_4.
$$

Every solvable transitive subgroup of $S_5$ lies in a conjugate of
$F_{20}$. The six roots of the resolvent correspond to the six conjugates
of this subgroup; a rational resolvent root is equivalent to containment in
one of them. Chapman's correction note supplies the published proof's
repeated-resolvent-root step.

### 5. Decide whether the sextic has a rational root

Clear denominators to obtain a degree-six integer polynomial

$$
A(T)=A_6T^6+\cdots+A_0,\qquad A_6\ne0,
$$

with the same rational roots. If $A_0=0$, return **yes**. Otherwise the
rational-root theorem says that a root $u/v$ in lowest terms satisfies

$$
|u|\le |A_0|,\qquad 1\le v\le |A_6|.
$$

Enumerate this finite rectangle and test

$$
\sum_{i=0}^{6} A_i u^i v^{6-i}=0
$$

using integer arithmetic. Return **yes** exactly when a pair passes.

## Correctness and recursion

The factor branch answers **yes** exactly for reducible quintics, all of whose
irreducible factors have degree at most four. On the other branch, Dummit's
theorem and the rational-root theorem show that the final bounded search
answers **yes** exactly when the irreducible quintic is solvable by radicals.
The preliminary scaling and translation preserve its roots' radical
expressibility. Thus the procedure decides $\operatorname{Rad}(f)$.

Signed-integer arithmetic, absolute value, maximum, fixed powers, exact
polynomial remainder, and the displayed rational transformations are
primitive recursive under any standard coding by natural numbers. Every
search above is bounded by an integer computed from the input. The resolvent
is one fixed finite coefficient expression, so it can be hard-coded.
Consequently the entire Boolean procedure is primitive recursive and is
therefore computed by a Turing machine that halts on every integer quintic.

For comparison, a much stronger general result is known: Landau and Miller
give a polynomial-time radical-solvability algorithm for monic irreducible
integer polynomials of arbitrary degree. Combining it with the
Lenstra--Lenstra--Lovász rational factorization algorithm also proves the
present theorem (and more) in polynomial time.

## Formalized verification status

The Lean development now formalizes the full mathematical reduction and its
computability endpoint. In particular, it verifies:

- integral monicization and completeness of the bounded linear/quadratic
  factor search;
- the degree-at-most-four radical-solvability argument for the reducible
  branch;
- the scalar Frobenius--Dummit invariant and sextic, the six
  $S_5/F_{20}$ cosets, the solvable-transitive-subgroup criterion, and
  Chapman's repeated-root/no-collision step;
- specialization of the universal resolvent at an ordered root tuple and the
  equivalence between a rational resolvent root and solvability of the
  irreducible quintic's Galois group;
- a directly evaluable sparse table for all seven integer coefficients of the
  sextic, together with a symbolic-normalization certificate equating that
  table with the universal resolvent;
- completeness of the bounded rational-root search;
- primitive-recursiveness of the coefficient transformations, both bounded
  searches, the explicit resolvent-coefficient function, and the assembled
  Boolean criterion;
- correctness of that criterion for the semantic all-complex-roots radical
  predicate, hence a `ComputablePred` theorem and existence of a
  `PartrecToTM2` program whose execution realizes the encoded criterion.

This is stronger than merely installing a classical `Decidable` instance:
the Lean proof explicitly passes through a primitive-recursive Boolean
characteristic function and mathlib's Turing-machine execution relation.

The repository contains the seven coefficient polynomials as a 302-term
sparse table. Lean first proves the table correct over every commutative ring,
then proves its directly evaluable coefficient function equal to the abstract
one selected by the fundamental theorem of symmetric polynomials. Thus
`quinticRadicalDecision` is a reducible Lean Boolean function, not merely a
classically selected characteristic function. The development does not claim
that this deliberately simple bounded search is efficient, nor does it ship a
standalone extracted solver or display the numeric code of the existentially
obtained Turing program.

The largest finite table identities are intentionally checked with
`native_decide`: coefficient indices zero through three use Lean's native
compiler, while indices four through six use ordinary kernel reduction. As
with other documented native certificates in this repository, those four
proofs therefore expose four generated native-decision axioms in the
assumption audit and include the native compiler/runtime in their trust
boundary. All symbolic bridge lemmas and the final semantic reductions are
ordinary Lean proofs.

Rocq now checks the bounded coefficient algorithm as well.  In
[`QuinticCanonicalDecision.v`](Coq/QuinticCanonicalDecision.v),
`quintic_radicalb` first runs the complete bounded linear/quadratic factor
search and, on the irreducible branch, runs the bounded rational-root test on
the explicitly computed scalar Frobenius--Dummit resolvent.  The theorem
`quintic_radicalP` reflects the exact `radical_formula_solves` predicate to
that Boolean.  Its Chapman step is discharged from an explicitly constructed
five-cycle automorphism of the canonical splitting field; theta-value
injectivity is no longer an input hypothesis.

[`QuinticRadicalDecidability.v`](Coq/QuinticRadicalDecidability.v) remains as
an independent semantic route through MathComp-Abel's abstract `numfield`:
`integer_radical_decisionP` handles every size-six integer polynomial, and
`quintic_radical_decision_codeP` handles natural-number encodings.  The
coefficient Boolean and the abstract semantic Boolean are separate checked
implementations of the same all-roots radical predicate.

## The sextic extension

For seven signed coefficients

$$
(a_0,a_1,\ldots,a_6), \qquad a_6\ne0,
$$

the sextic development decides the analogous predicate that every complex
root of $a_6X^6+\cdots+a_0$ has a radical expression over the rationals.
Integral monicization preserves that predicate.  A bounded search for monic
factors of degrees one through three is complete by Cauchy's bound and
Gauss's lemma.  A nonlinear proper factor leaves only degree-at-most-four
factors; a linear factor reduces the remaining factor to the verified
quintic decision above.

On the irreducible branch, the construction evaluates the two classical
block-system resolvents of degrees fifteen and ten.  A separating
specialization is found by enumerating nonnegative-integer parameter pairs and
taking the least collision-free one.  Existence follows from the proved
pair/triple descriptor separation theorem, so this is an honest terminating
unbounded search.  Bounded rational-root tests on the two specialized
resolvents then decide the solvable-subgroup criterion.

Lean packages the resulting Boolean as
`allRootsRadical_computablePred : ComputablePred AllRootsRadical` and derives
`has_verified_sextic_radical_turing_machine`.  The proof is compositional:
each arithmetic operation, bounded loop, and least-successful-parameter
search is proved recursive from its definition.

Rocq compiles the same layers to Coq-Library-Undecidability's explicit
`recalg` syntax.  In
[`SexticMuRecVerifiedDecision.v`](Coq/SexticMuRecVerifiedDecision.v), the
theorems `encoded_raw_sextic_radical_relation_murec` and
`encoded_raw_sextic_radical_code_relation_murec` establish recursive graph
computability for a seven-vector and a one-natural encoding.  The definitions
`encoded_raw_sextic_radical_decidable` and
`encoded_raw_sextic_radical_code_decidable` have explicit decision sum types
`{P} + {~ P}`.  Their semantic link uses the already documented classical
splitting-field bridge, while the characteristic function itself is realized
by an explicitly proved $\mu$-recursive program.  Thus the formal endpoint
records both meanings of decidability needed here.

## Primary sources

- D. S. Dummit,
  [*Solving Solvable Quintics*](https://doi.org/10.1090/S0025-5718-1991-1079014-X),
  *Mathematics of Computation* 57 (1991), Theorem 1 and equation (2).
- R. Chapman,
  [*Note on Solving Solvable Quintics by D. Dummit*](https://site.uvm.edu/ddummit/files/2021/04/Solving_Solvable_Quintics_note_by_Robin_Chapman.pdf),
  correction of the repeated-resolvent-root step.
- S. Landau and G. L. Miller,
  [*Solvability by Radicals Is in Polynomial Time*](https://www.cs.cmu.edu/~glmiller/Publications/Papers/LaMi85.pdf),
  *Journal of Computer and System Sciences* 30 (1985), Theorem 3.6.
- A. K. Lenstra, H. W. Lenstra Jr., and L. Lovász,
  [*Factoring Polynomials with Rational Coefficients*](https://eudml.org/doc/182903),
  *Mathematische Annalen* 261 (1982).
