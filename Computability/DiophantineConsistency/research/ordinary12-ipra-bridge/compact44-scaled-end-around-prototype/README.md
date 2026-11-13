# End-around carry with an arbitrary digit bound

This is a model-level generalization of `ArithmeticWindowCarry.lean`. For an
externally finite family of model words `X`, the explicit premises require a
positive word length and modulus, each word below the word radix, every digit
below the word length at most `D`, a remainder `F` below the modulus, the stated
congruence, and `(∑ aᵢ) * D + 1 ≤ (b+1) * (2^w−1)`. Under these hypotheses the
constructed cyclic carries are at most `b` and obey the digit and carry column
identities at each model position. The scaled digit-bound results are imported
from the separately paired parent `compact44-scaled-carry-prototype`.

The theorem is conditional: it does not derive the digit bounds or mass bound
for the actual compact44 construction, bind `MC` or `K`, establish a clean
predecessor, prove machine simulation, or construct a PRA proof. In particular,
the dummy digit at position 1063 is allowed to be 0 through 3, and there is no
global Boolean premise. The external finite index is not a model-internal
arbitrary finite family.

The initial exploratory Lean session 2295 exited 0 with a single unused-variable
linter warning and `[propext, Classical.choice, Quot.sound]` for the final
theorem. Its source and complete log are retained in `observations`. This
source follows the structure of the pre-existing window carry proof, replacing
the Boolean prefix bound and unscaled mass estimate by the new `D`-scaled
bounds. The subsequent matched author/peer wrapper session 58865 exited 0; both
compiled without warnings and produced matching object hashes and four matching
axiom reports. Its replay pins and checks the independently reviewed scaled
digit-bound parent (audit 4fa9b4ecab), direct imports, and 24-module provider
audit before and after. This paired result awaits its own independent review.
The provider audit lacks a complete axiom inventory, and neither package-
transitive nor dynamic ancestry is completely audited; the sampled resource
monitor is not a hard whole-process-tree quota.
