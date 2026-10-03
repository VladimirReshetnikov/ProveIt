# Independent review of the111-operation main/input norm grouping

PASS on the frozen [source](complete113_main_input_units111.py),
[receipt](complete113_main_input_units111.json), and
[proof](complete113_main_input_units111.md), with source SHA256
`152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16`.
No correction is requested. This is a complete111=53M+58A polynomial of
exact degree30, with the same24 positive witnesses and ordinary-input
program interface as the selected113/28 parent.

## Integer zero equivalence and complete correction

The actual coefficient is `Delta=a*a+4*a+3`. For every integer a it is0 or3
modulo4. When it is0, any norm `r*r-Delta*z*z` is a square modulo4. When it
is3, the norm is a sum of two squares modulo4. Neither possibility is3
modulo4, so neither actual main/input norm can be−1. This argument needs no
other equation, positivity, or Pell typing.

The new complete source is a sum of12 squares. At any integer zero all
residuals vanish, including `Nmain*Ninput-1`. Integer factorization then
forces each norm to be a unit, and the modular exclusion forces each to be+1.
These recover both original norm equations. The other eleven equations are
unchanged. Conversely, both original unit equations imply the grouped one.
Thus the complete integer zero sets are identical on the same supplied
coordinates; in particular their positive zero sets are identical. No
coordinate projection or new positivity assumption is required.

If S denotes the sum of the other eleven squares, the exact full polynomials
are `S+(Nmain-1)^2+(Ninput-1)^2` and `S+(Nmain*Ninput-1)^2`. Independent
coefficient expansion gives the complete off-zero difference

    F111-F113=(Nmain-1)*(Ninput-1)
              *(Nmain*Ninput+Nmain+Ninput-1).

The polynomials are therefore not asserted to be identical off zeros. This
identity holds over every commutative ring; the zero-equivalence proof uses
integer domains. For unconstrained unit factors, taking both−1 would invalidate
the grouping. The actual coefficient excludes that case. No real zero-set
equivalence or rational-witness semantic theorem follows from the modular proof.

## Complete source and paid arithmetic

The two removed parent registers are exactly `R15=Ac2+1` and
`norm_rhs=scaled_kappa2+1`. Neither has another source consumer, and each has
one comparison consumer. Their replacements each cost one subtraction:
`main_unit=L15-Ac2` and `input_unit=mu2-scaled_kappa2`. The added product costs
one multiplication. All other source rows are retained in their original order.

The independently reconstructed comparison list has the grouped unit equation
at position7 and removes only the original position12. Its full76-gate
certificate costs41M+35A. The literal finalizer pays12 subtractions,12 squares,
and11 additions, giving111=53M+58A. Against113=53M+60A, the certificate's extra
multiplication cancels the removed square multiplication, leaving exactly two
additions saved. Both entire old/new finalizers were reconstructed and matched
against the emitted source; no residual or sum contribution is free.

The independent checker verifies closure and liveness of all111 gates and all
31 supplied leaves: input x,24 witnesses, and six fixed numeral ports. It
also proves104 unchanged expression registers/leaves and all eleven unchanged
residuals in one exact expression table. Current comparison maps distinguish
the two recovered unit equations from identical retained residuals; the
parent's deleted-coordinate maps and former ledger remain historical metadata.
The source's existing definitions, ratio conditions, input loader, masks,
first-root gap and program conditions are all preserved.

## Exact uniform degree

All varying supplied coordinates have degree one and compiler numerals degree
zero. Write b=Bm1. Independent sparse expansion of the actual norm cones gives

    degree(Nmain)=8,   leading(Nmain)=b^6*w^2*Jrep^6,
    degree(Ninput)=7,  leading(Ninput)=-4*delta^2*a^5.

For the input norm, put `H=4a+3`, `kappa=u+delta*(a*a+H)` and
`v=W+rho*H`. Expanding the actual source gives exactly

    (a*kappa+v)^2-(a*a+H)*kappa^2
      =v^2+2*a*kappa*v-H*kappa^2.

This is polynomial cancellation before imposing any equation. The last term
alone reaches degree7. The product norm has degree15; its squared residual
is the unique term of degree30 in the complete SOS. Its full leading form is

    16*b^12*w^4*Jrep^12*delta^4*a^10.

All eleven other residuals have degree at most14, independently propagated
through their actual source cones. The leading form is nonzero for every
admissible fixed b>0, independent of the other fixed program numerals. Exact
degree30 follows uniformly. Literal uncancelled propagation gives32, correctly
recorded separately. This review proves the full multivariate leading forms,
rather than inferring them from one fixed-base evaluation.

## Inherited theorem and bounded independent replay

The selected parent's positive graph restoration and first-root-gap inverse
apply after recovering both norm equations. Its fixed admissible program
numerals, ordinary positive input, and unbounded existential duration remain
unchanged. The source only improves this parent's operation/degree tradeoff;
it does not reduce the separate86-operation bound or establish any global
optimality. Arbitrary positive numeral ports do not automatically describe a
valid compiled program.

The [review helper](review_complete113_main_input_units111.py) pins all three
author files and the selected parent before loading the authenticated current
source for public-interface tests. All12 inherited file pins are checked.
It executes no historical Python code and never invokes the author's verifier,
structural proof, or degree expansion. Actual parent JSON supplies the source
being independently transformed and compared. The inherited universal theorem
is not reproved by finite tests; the direct complete grouping argument above
is the new theorem under review.

The [receipt](review_complete113_main_input_units111.json) records the complete
source reconstructions, exact norm cancellation and multivariate leaders,
full symbolic correction, all64 modular classes,40 full numeric/SOS checks
(24 signed and eight rational),31 malformed API rejections, four child copies,
one parent copy,12 changed-parent pin rejections, and optimized-mode rejection.
The public degree API authenticates the complete canonical packet. No enormous
positive Pell tuple is materialized. Writer and fresh exact receipt replay pass.

```sh
python review_complete113_main_input_units111.py \
  --source complete113_main_input_units111.py \
  --receipt complete113_main_input_units111.json \
  --note complete113_main_input_units111.md \
  --root /path/to/native-stream-queue \
  --expect review_complete113_main_input_units111.json
```

Replay uses only Python's standard library and explicit paths. It modifies
neither the frozen parent nor any repository file.
