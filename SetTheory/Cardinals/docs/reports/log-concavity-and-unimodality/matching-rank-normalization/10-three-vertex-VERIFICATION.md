# Verification

The universal finite certificate is the complete degree-six expansion of the
3 by 3 matrix M displayed in the article. Its entries depend on all seven
right-neighborhood classes and on exact first/second activity moments. No upper
bound or numerical approximation is used in the moment substitution.

Two separately written standard-library reconstructions agree coefficient by
coefficient with data/determinant.json:

- 5,339 nonzero coefficients, all positive integers
- Minimum 36 and maximum 10,656
- Every monomial has total degree six in the eleven stated variables
- Canonical coefficient-list SHA-256:
  0f6b0733bd999e34e058223139f524830bcdcd6a1436a8fae89983cba49c3522

The primary reconstruction uses the six determinant permutation terms. The
independent reconstruction uses explicit neighborhood forms and the symmetric
five-term determinant formula. Each script fails on any exact discrepancy.
The combined replay uses optimized Python, so its checks cannot depend on bare
assert statements.

Independent endpoint-state enumeration also verifies 240 weighted three-left
graphs and 160 weighted star-core graphs, of which 38 have matching rank equal
to the displayed cover size. It checks the overlap formula, the three Rayleigh
inequalities, the exact gluing identity and every fixed-cover Newton inequality.
These graph tests are finite regressions and are not substitutes for the proof.

The mathematical argument, the selected-left versus complemented-matroid
distinction, all activity normalizations, degeneracies and vertex-sum scope
received independent review. The report uses ordinary mathematical reasoning
and an exact integer-polynomial certificate; it is not a formal-kernel proof.
