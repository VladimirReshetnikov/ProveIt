# Independent review of the four linear-input quotient polynomials

The [construction](complete_linear_auxiliary_quotient_family.md) passes this
source and mathematical review. It supplies four complete universal
polynomials with 18 positive witnesses, at the same ordinary positive input
and with the full inherited fixed-program numeral recipe:

| First / auxiliary coordinate | M | A | Operations | Uniform exact degree |
| --- | ---: | ---: | ---: | ---: |
| Root / ordinate | 47 | 40 | 87 | 119 |
| Root / positive gap | 47 | 41 | 88 | 113 |
| Positive gap / ordinate | 47 | 41 | 88 | 109 |
| Positive gap / positive gap | 47 | 42 | 89 | 103 |

The 88/113 source is dominated by the 88/109 source at the same operation
count. The other three extend the reviewed 18-witness tradeoffs. None lowers
the minimum of 85 operations. This review covers four complete products;
it neither enumerates new grouped finalizers nor establishes an unrestricted
circuit optimum.

## Independent source and degree reconstruction

The [review helper](review_linear_auxiliary_quotient_family.py) authenticates
the author packet and its actual saved historical parents. It reads JSON
and proof bytes only. It never imports the author checker, executes a
predecessor builder, or reruns an earlier census. Its
[receipt](review_linear_auxiliary_quotient_family.json) is portable and
compared with recursive type-exact equality; its checks also run under
optimized Python.

For each source the checker independently verifies every instruction's
references, the entire supplied interface, all output-live gates and ports,
and the actual multiplication/addition counts. The four circuits contain
352 paid gates: 188 multiplications and 164 additions/subtractions. Each
retains all six fixed numeral ports, ordinary x and exactly 18 witnesses.

A separate implementation expands every coefficient of each of the seven
actual factors, retaining the six fixed numerals symbolically. It compares
these expansions with independently written mathematical formulas for q,
X,Y,c,a, the packed R, the input factor, the two gaps and the new auxiliary
V. There are 20,336 nonzero coefficient terms across the 28 factor instances,
counting repeated shared factors separately. This is a full factor audit,
not a comparison of degree metadata or sampled evaluations.

The reviewer computes the weighted highest homogeneous parts directly from
those full expansions, assigning fixed numerals degree zero. It checks every
coefficient against the construction's explicit leading-form formulas. It
then multiplies the seven leaders completely: the four whole leading forms
have respectively 240, 216, 456 and 408 monomials. Their degrees are exactly
119, 113, 109 and 103. Bm1 is positive on every valid compiler slice, and the
transport leader has the nonzero coefficient −Bm1 at
`transport_quotient*Jrep`; the remaining displayed factors are nonzero
polynomials in independent supplied variables. Thus the degree proof is
uniform over the allowed fixed numeral family, not confined to a numerical
specialization or to accepting zeros.

The output cone is separately expanded at independent factor cuts and
required to equal the product of all seven factors minus one. The same check
on each actual historical parent gives the full eight-factor product.
Consequently no missing finalizer, separate comparison or discarded
operation is hidden by the factor expansions.

## Full correction and positive inverse

The reviewer substitutes the polynomial `o=cT−Rf` into each actual parent
factor, with j still independent. All seven retained factor polynomials
agree coefficient for coefficient with the emitted child. The omitted
factor satisfies the whole polynomial identity

    Nlinear = Nk+V+R−cj.

Together with the two checked complete finalizers this proves, over every
commutative ring including c=0,

    Fparent(o=cT−Rf,j)+1 = (Fchild+1)*(Nk+V+R−cj).

Only over the rationals with c nonzero may one set j=(V+R)/c and obtain the
shorter correction `(Fparent+1)=(Fchild+1)*Nk`. Integrality and positivity of
j are zero-set conclusions. Neither correction asserts that the whole
polynomials are identical after arbitrary positive-coordinate substitution.

The mathematical proof was read separately from the source checker. Its
critical order is sound:

1. The first norm excludes the negative unit by descent. With the first gap,
   `tau=L+g>0` supplies exactly the same root equation. The main/input and
   ordinary strong factors exclude the negative unit modulo four. Only then
   is Kaux a square, excluding the auxiliary negative unit even if y is signed.
2. The retained transport unit proves the pretyping packing bounds, including
   R>0 and E>R+2. The index unit then forces the large first rank. The main
   ratio gives p>n and the large-c premises for the ordinary relaxed-rank
   lemma. Replacing the input modulus by a+1 changes none of these steps.
3. Ordinary rank gives c squared dividing f squared minus one. It does not
   give the stronger normalized divisibility for the Pell coefficient.
4. In the auxiliary-gap case, the gap estimate uses **absolute y**. From
   Kaux V squared minus (Kaux−1)y squared equal to one, a nontrivial absolute
   V is at least 2 Kaux−1. Positive T and the ordinary size margin exclude
   that negative branch; the congruence V=−c modulo f excludes V=±1. Hence
   V>0 before y=V+e>0 is asserted. Restored o and j are now positive integers.
5. The local auxiliary step-down identifies p=R before any parent zero
   theorem is invoked. The strict main ratio rejects the remaining negative
   index sign. All eight restored parent factors are therefore +1, so the
   exact selected historical parent theorem applies.

Conversely, every positive parent zero has `of+R=c(j+1)` and
`f squared=1 modulo c`, forcing `c` to divide `o+Rf`. The positive quotient
T=(o+Rf)/c reconstructs the old V and restores o,j uniquely. The existing
first gap or auxiliary gap is left unchanged within its selected parent.
These are bijections of the **complete** positive integer zero sets for
each pair, not merely of canonical Pell extensions. The proof does not
invoke the normalized polynomial restoration for j in these ordinary forms.

## Scope and replay

The four universal claims retain the full parent compiler recipe. Arbitrary
positive choices of the fixed mask numerals are not covered. No rational,
real, signed-zero or globally positive off-zero extension is asserted.
Neither checker materializes an enormous accepting universal Pell tuple.

    python3 /absolute/path/review_linear_auxiliary_quotient_family.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/review_linear_auxiliary_quotient_family.json
