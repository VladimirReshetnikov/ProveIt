# Exploratory all-model rotation case coverage

`RotationCoverage.coverage` partitions any model cut and output window into non-wrapping, wholly wrapped, or straddling cases under the sole geometric assumption `b+w≤L`, giving the exact witnesses needed by the three earlier rotation lemmas. `digit_index` is the internal quotient/remainder decomposition by 67. `RotationCoverage67.coverage` specializes to `b=67*k`, `w=67`, `L=67*n` for arbitrary model n, e, k with `k<n`, and supplies the source-index quotient and remainder for every case.

`RotationAllCases.digit` combines the three conditional rotation identities for any model X, n, e, k satisfying `k<n` and `X<2^(67*n)`. It returns a source quotient q and remainder r<67 and states either the two-adjacent-digit formula or the explicit boundary-splice formula. This theorem does not establish `q<n`; the q+1 source position and cyclic reduction still require care. It does not rely on finite standard-model checks.

The author-only compiler sessions 48957, 71225 and 78751 actually exited 0 without warnings or `sorryAx`, and all named axiom reports use `propext`, `Classical.choice`, and `Quot.sound`. Initial session 8628 actually exited 1 on subtraction/associativity rewrites; its exact source and log are retained, and its `sorryAx` report proves nothing. The same fresh author overlay and locally built dependencies from commits 5152fadc5e, ce88d22a4f, 40b71334eb, and 5105b2126b were used. This is exploratory evidence, not a paired replay or independent artifact audit.

No strict half-radix bound, clean predecessor, graph-column decoding, retained-K binding, or internal iPRA conclusion is claimed.
