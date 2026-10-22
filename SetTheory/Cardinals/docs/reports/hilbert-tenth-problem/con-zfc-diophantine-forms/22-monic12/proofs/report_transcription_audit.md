# Independent transcription audit of the synthesis article

Release note: All corrections listed below have been incorporated into the delivered report and generated circuit counts.

Reviewed `output/con_zfc_synthesis/con_zfc_synthesis.tex`, specifically the
twelve-variable and thirteen-variable constructions, their logical endpoint,
and the related arithmetic part of the unrestricted-integer extension.

## Result

The mathematical transcription passes. No mathematical gap was found in the
reviewed sections. In particular:

- The definitions of `H8`, its division-free quadratic norm evaluator, and
  the resultant scaling agree with the independent circuit generator.
- The monic-root lemma correctly uses the nonintegral norm
  `-4B/(H^2 c^2)` and the exact identity
  `H^2-4Delta=12a^2+8a-3`.
- The rational auxiliary-coordinate saturation lemma includes the required
  squarefree denominator argument and the odd-multiple Chebyshev divisibility
  argument. It does not infer integrality from an arbitrary rational square.
- The strengthened low-degree weight supplies positive denominators and
  excludes the zero weighted root before restoring eliminated coordinates.
- The conversion `i_ordinary=Delta*i` is explicitly stated before use of the
  signed ordinary interface. Signed gamma is not silently assumed positive.
- Product guards are justified modulo four, and the two remaining outer
  signs are passed to the inherited signed step-down with only the weak
  transport boundary available.
- The quartic monic identity and thirteen-variable norm evaluator agree
  with the emitter. Its zero weighted-root branch is excluded by the strict
  bound `0<A-1<c^4<=K`, rather than by dividing by a potentially zero root.
- The exact degrees 1520/1529 and 288/319 follow from the displayed nonzero
  highest forms and agree with independent degree propagation.
- The article distinguishes ordinary proofs formalizable in ZFC from new
  kernel-checked formalization, and does not infer two-sided independence
  from mere consistency.

## Small editorial/count corrections sent to the integrating author

The author already plans the system-count corrections 113 to 112 and 84 to
83, because the emitted systems compare the two norm terms directly and
omit the subtraction needed only for a polynomial residual. Consequently
the 26-integer system count must also change from 165 to 164:

    112 + 7*7 + 2 + 1 = 164.

The thirteen-variable introductory sentence should say that the **twelve**
variables in the earlier display, together with `f`, give thirteen variables;
the earlier display itself contains twelve coordinates.

These are presentation/count fixes and do not change any polynomial or proof.
The strict compiler and coefficient-layout proof are outside this audit's
scope and have separate reviewers.
