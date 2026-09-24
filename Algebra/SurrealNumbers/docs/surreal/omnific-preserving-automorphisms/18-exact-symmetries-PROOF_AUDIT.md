# Proof audit

This is an author-side logical audit of the accompanying manuscript,
not an independent referee report or a formal verification certificate.
Stable theorem identifiers below are LaTeX labels in `article.tex`.

## Standing hypotheses

- NBG set theory with Global Choice.
- All Hahn supports and summation index sets are sets.
- All groups being realized and all parameter collections are sets.
- Growth supports are reverse well ordered, not valuation-style well ordered.
- The exact common fixed-field theorem assumes a nontrivial group.
- A group action is one class function G x No -> No. No NBG class of all
  proper-class automorphisms is assumed.

## Main dependency chain

1. Classical inputs: the Conway normal-form theorem, real closedness of
   No, and the surreal set-cut property.
2. `prop:lifts`: ordinary external double Hahn lifting.
3. `lem:orbit` and `thm:fixed-support`: exact fixed support at two levels.
4. `lem:cut-insert`: free insertion at all cut orbits in a set-sized
   ordered G-set.
5. `thm:free-order`: set-valued recursion through On, followed by
   class-order back-and-forth.
6. `thm:exact-index`: free actions installed in all components of No\S.
7. `thm:main`: apply the double lift; use the moved omnific witness.
8. `lem:necessity` and `lem:fractions`: the converse for fields and rings.
9. `lem:centralizer`, `lem:nonreal`: complex/Gaussian classification.

## Critical checks

### First lift versus second lift

T_phi relabels the support of an exponent using the merely increasing
bijection phi. It is real-linear and additive, but generally not
multiplicative and need not fix 1. F_phi relabels outer exponents using
T_phi. Its multiplicativity follows from T_phi(a+b)=T_phi(a)+T_phi(b).
All composition conventions are F_{phi psi}=F_phi F_psi.

### No cancellation between distinct permuted exponents

Both exponent relabellings are injective. A fixed series must have an
invariant support. An orbit in that support has a greatest element;
invariance and monotonicity make the greatest element fixed, and hence
make the orbit a singleton. No infinite orbit sum is introduced.

### Cut insertion and left, not right, order

For a cut D, its stabilizer H inherits the chosen left order on G.
A free copy of G is placed over the orbit of D. The fiber over C uses
labels s(C)h. Acting by k changes the internal coordinate to h0 h,
where k s(C)=s(kC)h0. This is left multiplication, so no bi-order or
conjugation-invariant order is being assumed.

Inserting only one point at a stabilized cut would destroy freeness.
The free ordered fiber is essential.

### All set cuts are eventually filled

Any set L union R in the final union has a set of appearance stages,
hence is contained in some X_alpha. The downward closure of L inside
X_alpha is a cut at which a point is inserted at stage alpha+1.
That new point is strictly between L and R, including when either side
is empty. The recursion handles all cut orbits at each successor stage.

### Proper classes and uniform choices

The recursion values are sets; limit stages are set unions. One global
set-like well-order chooses representatives uniformly. Component
isomorphisms are outputs of a uniform back-and-forth rule with a set cut
code as parameter. A set of proper-class functions is never formed.

### Parameter support and exact fixed fields

S controls the second-level supports of the fixed field. For every
nonidentity index action, the fixed indices are exactly S. Applying the
orbit argument twice yields H(H(S)), not H(S). For a parameter set A,
Sigma_2(A) is a set and is sufficient. The minimality assertion is only
within the family K_S, not among all subfields and not for definable closure.

### Faithfulness on the integer part

If phi_g(a) != a, the moved witness is omega^(omega^a). Its outer exponent
omega^a is positive for every surreal a. Therefore the witness is omnific.
The ring restriction cannot kill a nonidentity group element.

### Fraction-field passage

Every normal-form support is a set, so a positive surreal b can be chosen
above its negation. Multiplication by omega^b puts both numerator and
denominator in Oz with strictly positive supports. Thus Frac(Oz)=No.
This bounding step uses the full No and is not transferred to a smaller
Hahn exponent group. Invariants and fractions need not commute:
the constructed S=empty action gives Frac(Z)=Q but Fix(No)=R.

### Converse left ordering

One moved-point witness per nonidentity element gives a set of test
points. Well-ordering that set allows first-difference comparison of
images. Left multiplication preserves both the first differing index
and its order. Real closedness supplies order preservation for arbitrary
surreal field automorphisms. It does not supply pointwise fixation of R.

### Surcomplex signs

Commutation with conjugation preserves its fixed field No. The image of
i is either i or -i. A kernel of the real restriction, if nontrivial,
is the central C2 and is split by the sign map. For a fixed nonreal point,
a negative sign would force sigma(y)=-y for nonzero real-surreal y,
contradicting order preservation. The same argument transfers through
the Gaussian fraction field.

### Character-twist boundary example

The real constant coefficient ct(a) of an exponent is additive, so
exp(2 pi i ct(a)) is a character. It is not asserted that ct is a ring
homomorphism on all of No. The twist fixes complex coefficients, preserves
Gaussian-omnific support, but does not centralize conjugation. Its fixed
exponent group is nondivisible; the leading-exponent argument rules out
specified roots and proves its fixed field is not algebraically closed.

## Verification performed

`verify.py` completed 11,330 exact rational assertions, including finite
lift functoriality, multiplication, signs, constant coefficients, fixed
support, omnific membership, and the Klein bottle action identities.
The code uses a deterministic seed and no floating-point arithmetic.

No infinite support or class construction was executed in that test.
No Lean proof of the new results was generated or checked. Mathematical
correctness remains subject to independent expert checking.

## Excluded claims

No automatic strongness theorem for arbitrary omnific automorphisms;
no universal preservation of ordinary reals by all field automorphisms;
no preservation of the named omega map, Gonshor exponential, derivation,
simplicity, or birthdays; no full classification of fixed subfields;
no automatic birthday-cutoff transfer; no classification of all
surcomplex actions without named conjugation; no certified historical
priority or resolution of an unrelated published conjecture.
