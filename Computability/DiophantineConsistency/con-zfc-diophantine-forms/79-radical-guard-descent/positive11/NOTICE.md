# Attribution

Prepared against Vladimir Reshetnikov's ProveIt repository at commit
2605669a532342f153b13eb6b4a0af4b54f5fa37.

The construction builder, exact sparse-ring checker, and register/degree
audit are adapted from package 70 (`70-residue-orientation/eleven`). Its
LICENSE is retained as `LICENSE.upstream`, along with all licenses and
notices from the fixed coefficient package.

The rational-integrality lemma is package 69's Pell descent. The new
contribution is its composition with package 70's root transfer, removing
the denominator guard and lowering the literal degree from 325 to 277.
The normalized source, signed-index interface, fixed tuple, native
compiler, and K215/refutation equivalence are inherited.

AI assistance was used in the new research, proof, and code. Source hashes
are recorded in SOURCE_PINS.json. Finite checks are not unbounded semantic
proofs, independent human peer review, or a new internal-ZFC derivation.
