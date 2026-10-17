`ZeroSite253.lean` proves the complete zero branch of literal site000 in
the actual public253 machine, using its compact table. Logical register8
is physical block5 under the published permutation. The input permits any
five preceding register values, any following primary/spare blocks, a
ten-zero left margin, and arbitrary finite farther-left data. The whole
zero-exterior tape is retained by `ZipRep`.

The PC changes000→01, its zero gap grows by one, and the header, absolute
head, all primary registers and every spare stay fixed. The return state
is compact33, the attributed old96 dispatcher. For gap≥37 the exact time is
`8*gap + 4*prefixWidth + 110`, where `prefixWidth` is the unary width of
physical blocks0–4. The lower bound follows from the existing frame's
path-length-plus-gap invariant. `paired_zero000` also proves agreement with
the actual literal `Prog254` register step. Logical tail-zero and physical
spare values remain separate conditions.

The proof composes127 literal transitions, eight arbitrary-length scan
applications, and the already proved marking and zero-decrement boxes.
Every literal row equality is checked by kernel `decide`; `WritingRuns`
supplies the scans that overwrite bits. View normalizations and arithmetic
do not add machine steps. The independently assembled control proof does
not trust a Python executor or import a Coq theorem. Its contracts are
attributed to Mira-Cult's machine, Wade's framework, Jeff's verification,
and mira-emmy PR20 head0d544f2a2e3c18f12278441a74b7879f31cbe856.

At the already proved bootstrap frame, gap37 and prefix width12 give454
further steps. Composing the existing Core312975 certificate proves the
exact whole frame at binary step313429, with state33 and head−17. The
marker remains−18 and the header23; all158 spares, including their two
nonzero entries, are retained. The literal register computation extends
from RM330 to RM331, with path01 and unchanged whole logical vector.
`bootstrap_matches_rm331` pairs these endpoints. No bootstrap computation
is repeated. Intermediate dispatcher visits are permitted, and the result
does not assert first arrival or first return.

The combined source compiled with the explicit absolute Lean4.32 executable
in15.542s. Twelve ZeroSite and four WritingRuns axiom reports plus six
caller checks passed in0.568s. Binary/site facts use standard `propext`
and `Quot.sound`; the RM331 prefix and paired endpoint also inherit standard
`Classical.choice` through their logical proof dependencies. There are no
custom axioms, `sorry`, or `native_decide`. Commands, source identities,
scoped dependency-cache provenance and logs are recorded in
`results/zero-site253-verification.json`. The two modules also received
independent read-only scope reviews.

This adds one instruction branch and a concrete continuation of the public
bootstrap. General site checking, reachable-PC preservation, the
structured-DAG/path bridge, full register/binary refinement, and the
machine's enumeration/consistency calibration remain separate obligations.
The machine table and state count are unchanged.
