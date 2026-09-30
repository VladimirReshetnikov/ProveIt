# Effective width decision for the unfiltered affine carry queue

The effectivity gap recorded in
[the carry note, Section 5](native_controller_carry_obstruction.md) can be
closed for its stated application. Given the fixed integer matrices,
endpoint carries, and a numerical ordinary input x, there is a uniform
algorithm computing a width cutoff, period, exceptional widths and
admissible residues. Existence of a width `L=3^ell>x` is consequently
decidable. This conclusion uses constructive reductions, not merely the
existence of eventual periodicity.

The conclusion concerns the **entire unfiltered affine carry relation**
with an absorbing zero endpoint and the stated initialization. It does
not apply to extra edge filters, additional nonlinear witnesses, or a
different terminal-state contract. The original carry checker and receipt
are unchanged. Two independent scoped proof/source/default reviews pass,
including review of the constructive steps in the two primary papers.

## The exact input to the logical procedure

Fix a numerical positive x. Write `K=c_final-c_start`, `I=(x,L)` and
form the parameter-L sentence

    Phi_x(L) := L>x AND exists A in Z^d:
                  A>=0 AND U*I+(3L*U+V)*A=K.              (1)

Extra specified stream-positivity inequalities are linear in A with
integer-polynomial coefficients in L, so they can be included. More
generally this works for a fixed affine initialization in x and L, with
its required initial bounds included. The value x is substituted before
running the algorithm. No uniform period independent of x is asserted.

All coordinates other than the parameter L are quantified. That fact
lets us stop the cited reductions before their later polyhedral steps.

## Audit of the constructive dependencies

The audited primary sources are
[Bogart–Goodrick–Woods, arXiv:1608.08520v2](https://arxiv.org/pdf/1608.08520v2)
and [Goodrick, arXiv:1604.06166v2](https://arxiv.org/pdf/1604.06166v2).

Goodrick's Theorem 1.4 is implemented in its proof by finite syntactic
operations: normalization, products of coefficient functions, sign/zero
branches, and recursive lower-bound terms (Lemmas 3.2–3.8, pp. 7–12).
For the computable ring `Z[L]`, each operation is effective. Lemma 3.8
explicitly replaces an unbounded quantifier by polynomially bounded
ones. Its proof's auxiliary cutoff in Lemma 3.4 is not an input to that
replacement; no algorithm must discover that cutoff. Theorem 1.5 then
gives the finite Cooper elimination when quantified-variable coefficients
and divisors are constant. [Goodrick, Section 3](https://arxiv.org/pdf/1604.06166v2)

BGW Step 2 removes polynomial divisibility using quotient/remainder
substitution (Lemma 4.1). Step 3 expands bounded variables into base-L
digits and splits each lowest coefficient into finitely many carry cases
(Lemmas 4.5–4.6). Step 4 eliminates the resulting bounded digit variables
(Proposition 4.7). These constructions use computable polynomial bounds;
their finitely many exceptional parameter values can be retained
separately. In the present sentence there are no free coordinates to
reconstruct. The output is a Boolean combination of polynomial comparisons
in L and divisibility by fixed integers. Thus Steps 5–6, integer-hull
selection and generating functions are unnecessary for this application.
[BGW, Sections 4.1–4.4, pp. 16–22](https://arxiv.org/pdf/1608.08520v2)

For explicit control of every “sufficiently large” choice, a polynomial's
coefficient list gives an integer bound beyond all of its real roots.
Likewise, if a bounded quantifier has upper bound f(L), then for
`L>1+sum(abs(coefficients(f)))` it lies below `L^(degree(f)+1)` whenever
its range is nonempty. Retain its original bound as a guard when enlarging
the digit box. Every branch uses finitely many such computations. All
discarded smaller L are individually decidable by ordinary Presburger
arithmetic. This supplies a computable accumulated exception threshold.

Consequently we obtain, effectively, a threshold N0 and a finite formula
Psi(L) equivalent to (1) for `L>=N0`, with atoms of the forms

    f(L)<=0,    f(L)=0,    c divides g(L),                 (2)

where f,g are explicitly represented integer polynomials and c is a
fixed integer. Zero-divisor predicates are replaced by their fixed
logical value under the cited language's convention. This is an audited
specialization of the proofs, not a claim that eventual-periodicity
theorems are automatically effective.

## Computing the period and the powers-of-three answer

Here is an independent elementary postprocessing proof. For a nonconstant
nonzero polynomial `f(L)=a_d L^d+...+a_0`, set

    N_f=2+floor(sum_(i<d) abs(a_i)/abs(a_d)).

For `L>=N_f`, the leading term strictly dominates all lower terms:

    abs(a_d)*L^d > sum_(i<d) abs(a_i)*L^i.

Thus f has the fixed sign of a_d and is nonzero there. Constant and zero
polynomials are handled directly. Let N be the maximum of N0, 1 and all
these computable N_f. All comparison atoms in (2) are constant beyond N.

Let P be the least common multiple of all positive absolute divisors c
in (2), taking P=1 if there are none. Integer polynomials satisfy
`g(L+P)=g(L) modulo c` for every such c. Therefore Psi is periodic with
period P on `L>=N`. For each `r=0,...,P-1`, evaluate it at

    L_r=N+((r-N) modulo P)

to compute exactly which residues are admitted. Decide (1) separately
at the finitely many positive widths below N. This constructs the
cutoff, period, residues and finite exceptional set uniformly from (1).

To restrict to powers of three, check all `1,3,9,...` below N. Starting
with the first power at least N, iterate its residue by

    r_next=3r modulo P.

If an admitted residue occurs, accept. If a residue repeats first, reject.
This always terminates after at most P distinct residue states. It works
when P is divisible by 3: no assumption of invertibility or purely cyclic
behavior from exponent zero is needed. The input inequality `L>x` is
already included in (1). This proves a uniform decision procedure for the
ordinary-input set of the scoped queue architecture, so that architecture
cannot represent every recursively enumerable set.

## A hand-eliminated matrix example and executable scope

Take one carry coordinate, two queue coordinates,

    U=(1,-1), V=(0,6), K=0.

Then (1)'s equation is

    x-L+3L*A0+(6-3L)*A1=0.                               (3)

For `L>x` and positive x, widths below 3 give no solution. For `L>=3`,
the two append coefficients have opposite signs. Thus nonnegative, or
even strictly positive, solutions exist exactly when

    gcd(3L,6) divides L-x.                                (4)

Bezout gives an integer solution; adding a sufficiently large positive
multiple of the positive kernel vector makes both coordinates positive.
Equivalently, for odd L require `3 | L-x`, and for even L require
`6 | L-x`. This is an explicit period-6 width formula above its finite
input bound. On powers `L=3^ell>x`, it admits exactly inputs divisible
by 3. It illustrates the algorithm, rather than proving the general
effectivity claim by example.

The [checker](input_bridge_presburger_effectivity.py) and
[receipt](input_bridge_presburger_effectivity.json) implement the
postprocessing of (2), including noncoprime modular orbits. They check
34 explicit formulas, 3,366 width evaluations and 1,920 exact positive
append-witness decisions for (3). Run:

    python input_bridge_presburger_effectivity.py

The full Goodrick/BGW formula transformation is **not implemented** in
this source. Its effectivity is established by the proof audit above;
the executable evidence covers the terminal algorithm and the stated
hand-eliminated family only. There is no complexity bound or reduction
of the established 76-operation universal certificate.
