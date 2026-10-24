# Attribution and retained dependencies

New constructions and proofs in this component were developed with AI assistance
for Vladimir Reshetnikov's ProveIt repository. They are offered under the attached
repository license. No external human peer review or new proof-assistant endpoint
is claimed.

The finite native tuple and coefficient recipe, normalized source, determinant
guard, root norm implementation and logical calibration are inherited from the
two incoming packages named and hashed in `SOURCE_PINS.json`. Their license and
notice texts are retained under `upstream/root_fusion/licenses/` and
`upstream/fixed_prime/licenses/`.

`dag_support.py` is a verbatim copy of the root-fusion builder, used here for its
arithmetic-DAG classes and export function only. `five_square_norm.py` derives
from that package; the first biquadratic squaring is specialized algebraically
to its equal linear coefficients. `build.py` and `verify.py` are new.

The general valuation-separation lemma and generalized-pentagonal guard are
credited to the fixed-prime package; the latter representation theorem is
classical and its historical attributions remain in the retained source.
The new contribution combines that separation with the root-fusion CRT carrier,
removes the redundant scale guard, and develops the retained-root family.

Historical relative links inside verbatim retained documents refer to their
original source trees. The source ledger identifies exact members and hashes;
the supported new replay commands are `python3 build.py` and `python3 verify.py`.
