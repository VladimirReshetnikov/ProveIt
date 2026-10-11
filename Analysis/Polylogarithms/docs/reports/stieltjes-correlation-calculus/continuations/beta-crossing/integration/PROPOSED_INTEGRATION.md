# Proposed manuscript integration

This package does not change the repository. The following steps are a
reviewable integration proposal.

## Source and status

The immediate reference is `07-mixed-twist-identities.tex` at commit
`446dca9bd65c20e409d1d2561d4ffad408103e2a`.
The existing theorem is correct with its common-interval assumption.
The supplied continuation treats arbitrary nonintegral real twists at a
positive integer **total order**. Do not drop that last qualification.

The core uses all of the standalone article's mathematical Sections 2–9.
All analytic hypotheses and proofs are retained. It does not include the
standalone title, status discussion, research questions, or verification
appendices. Preserve those sections with the research report even when
the mathematical core is integrated.

## Suggested placement

Copy `07-beta-crossing-identities.tex` to the manuscript's `chapters/`
directory. Review `beta-crossing-preamble.tex` and load its helper commands
from the common preamble. The parent manuscript must already provide
`theorem`, `lemma`, `proposition`, `corollary`, `example`, `remark`, and
`proof` environments. The commands require standard AMS math support and
`bm`; no custom fonts or nonstandard data files are needed.

After the existing unequal-twist section, insert:

```tex
\input{chapters/07-beta-crossing-identities}
```

Merge the entries in `beta-crossing-references.tex` into the existing
bibliography or map the cited `dlmf-hurwitz` key to an existing equivalent
entry. The core currently cites only that bibliography key; the additional
entries document the full standalone report's provenance. Do not create
nested `thebibliography` environments.

All labels use the `bc:` prefix. All helper commands use a `bc` prefix and
are defined with `\providecommand`. Check for a pre-existing contribution
with this namespace before merging. Equation and theorem numbers will
adapt to the parent manuscript; use labels rather than copied numbers.

## Review gates

Check the Fourier sign convention, particularly the factor `(2*pi*i)^(-m)`
and the phase `exp(i*pi*sigma_n)`. At symmetric half-twists and total order
one, the missing zero-mode correction is exactly `1/pi`.

Keep three regularization notions separate: affine finite part in the
intermediate twist; the right-half-plane analytic boundary value; and
Mellin Hadamard finite part in the variable `v` with the declared scale.
The delta derivatives used in the proof live in the twist parameter, not
in the circle variable `x`.

Retain the distinction between a correction vanishing on integer tuples
and a correction vanishing identically in an analytic neighborhood. The
first derivative at orders `(1,1)` and twists `(-1/2,1/2)` is `i/pi`, even
though the original correction vanishes there.

Retain the Gamma-residue term in every Mellin finite-part formula. The
reference cutoff integral at `m=2,a=1,j=2` has finite part `1`, not Euler's
constant. This is independently checked by an elementary antiderivative.

The 508 exact checks and 94 diagnostics should be rerun in an isolated
output location and separately recorded. Passing them is not a substitute
for analytic audit. No S6/S8, independence, or global-priority claim should
be promoted during integration.

## Regenerating the fragment

```sh
python integration/extract_core.py
```

This extracts the marked mathematical region and bibliography from the
current `article.tex`. It also regenerates the helper-macro fragment.
Do not edit both the source article and the extracted fragment separately.
