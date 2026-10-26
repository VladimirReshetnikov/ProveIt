# Mathematical and source review of the release report

Reviewed 25 October 2026, within the AI-assisted research workflow.
This is an independent internal mathematical review, not external human
peer review or a newly compiled proof-assistant derivation.

## Scope

Reviewed `output/ConZFC_Pooled_Projection_2026-10-25/report/report.tex`
before typesetting. The review covers the stated consistency theorem,
source attribution, the strict-range argument, the signed power-pooling
lemma, the noncircular arithmetic bootstrap, the radical projection,
the centered affine companion, and the stated finite-verification boundary.

The underlying combined source had already received the separate review
`COMPOSITION_REVIEW.md` and the independent exact checker
`check_composition_binding.py`. Those checks bind all 17 actual power
requests, the 36-square frame, the signed-index aggregate, the bootstrap
equations, and every emitted pooled residual to the concrete input.
This report review does not expand that finite-check scope.

## Verdict

No mathematical flaw was found in the signed estimate, bootstrap,
strict-range completeness argument, radical lift, centered chart, or
calibration statements. Two presentation corrections are required to make
the literal statements accurate. Additional small clarifications below
would make the report easier to verify.

## Required corrections identified during review

1. **Define the actual ambient Pell coordinate map.** In the private-wire
   and Pell-difference subsection, the displayed change must be

       U_i = X_i - Z_i,       X_i = U_i + Z_i.

   This is an invertible integral affine coordinate change in the ambient
   coordinate space. The retained gate equation `Z_i=A Y_i` then implies
   `U_i=X_i-A Y_i` on the common zero set. Defining `U_i=X_i-A Y_i` first
   and calling that displayed ambient map affine is inaccurate: that
   expression is quadratic before imposing the gate equation.

2. **Specify which sparse lists have bounded length.** The bounded lengths
   two and four apply to each monomial's coordinate-index list, not to the
   residual list or coefficient list. Recommended wording:

   > Each monomial's coordinate-index list has length at most two in a
   > residual and at most four in the collected quartic.

   This correction was already visible in a later read of the report.

## Recommended precision improvements

* Replace “All coordinates in this article range over unrestricted
  integers” with “All independent unknowns of the delivered equations
  range over unrestricted integers.” The syntax recoding is a map on
  natural numbers; begin that subsection with `a,b in N` explicitly.

* In the strict-completeness proof, replace “At a prime power p^(xm) of
  N=B^x” with “For each full prime power p^m || B, hence p^(xm) || N=B^x.”
  This states exactly which valuation is being used and makes `xm>=x`
  explicit. The intended proof is correct.

* The syntax recoding may explicitly identify zero as its base case.
  `I(0,0)=0` is the exceptional nondecreasing constructor instance; the
  other positive constructor values permit recursive descent. The
  report's existing claim that the recoding fixes zero is compatible
  with that treatment, but the exception helps readers reconstruct the
  recursion without silently assuming strict descent at zero.

* The measured uncentered 216-coordinate comparison is correct:
  14,145 terms and height 16,989,092 versus 15,158 terms and height
  334,952 after centering, a difference of 1,013 monomials. If that
  alternative is not retained in the archive, label the comparison as
  an internal measured control or include its coefficient file and
  metrics so that the stated comparison is independently reproducible.

## Points specifically checked

### Signed pooling

With `b=floor(sqrt(W-1))`, each requested signed exponent has absolute
value at most `b`, so multiplication by `n^b` clears negative exponents.
The displayed integer sum of squares is bounded by `4r b^(4b)`; because
`4r<=60<W`, `b^2<W`, and `2b+1<=W`, it is less than `W^W`.
The lower bound `|2An-n^2-1|>=2|A|-W>W^W` is valid.
The congruence is legitimate for negative indices since `n` is a unit
modulo `T=2An-n^2-1`. The converse formulas for `K,L` are integral.
No positivity of `A` or `n` is silently needed, and the cases `n=+/-1`
are correctly separated from nonunit bases.

### Bootstrap and strict ranges

The first three power requests remain individual. Raw parity proves
`B!=0` and `|H|>=2` before representative signs are recovered. The
terminal endpoint excludes `x=0`, licensing the q pool. Its `y+1`
request gives `y>=F`; the endpoints then force
`x>=2+(t+1)y`. Only after this is the q+1 pool used. The signed-digit
argument can therefore recover `B=binom(F+t,t)>0` without circularly
assuming a positive radix.

Strict completeness chooses a larger cofinal horizon before defining
`F`, accumulators, beta witnesses, or Pell-frame witnesses. It bounds
the full local derived label, including inactive branches and padding,
and does not bound the global CRT-derived label by `t`. Precision-2x
CRT leaves enough p-adic divisibility after division by `t!`.
The factorial-free spacing `y=F(2v+1)` remains intact; the incompatible
factorial-dependent spacing modification from source 158 is not used.

### Algebraic maps

The radical projection has integral polynomial inverse because its
chosen direction coordinate is one and its chosen directional slope
is plus or minus one. The displayed projection and lift are inverse
on the corresponding common zero sets.

The centered chart is correct:

    t_* = u+3a+4b+1,     c_* = v-2t_*,
    u   = t_*-3a-4b-1,   v  = c_*+2t_*.

It changes the affine consequence `4+12a+16b+4u-v+w=0` to
`2t_*-c_*+w=0`. Solving for `w` uses a unit coefficient and divides
no integer coordinate by two. The retained square row becomes
`c_*-4t_*^2+1=0`. Recovery of an omitted row from a nonzero integer
row-combination coefficient is valid over the torsion-free ring Z;
that coefficient need not be a unit.

### Source and verification boundary

The cited pinned files contain the unconditional named interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The former precedes the machine-specific simulation section and does
not require its hypotheses. The report correctly distinguishes these
inherited interfaces from the new ordinary semantic proof and exact
finite coefficient checks. It makes no claim to have recompiled the
transitive Lean closure, produced a new object-ZFC derivation, proved
consistency, found a global minimum, or established literature-wide
priority. These qualifications accurately describe this release.

The archive should retain the complete ordinary proof dependencies
and exact pinned identities advertised in the report. Its build and
receipt claims should be checked once more against the actual final
packaged files; this mathematical review was conducted while archive
assembly was still in progress.
