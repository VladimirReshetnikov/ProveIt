PA194D: a 194-state machine with a separate Gamma(D) head
=======================================================

Reproduce with Python 3.10 or newer, standard library only:

    python3 rebuild.py
    python3 independent_verify.py

Run without Python -O. No network, repository checkout, or proof assistant
is required. The independent check may take several minutes.

Literal machine
---------------

machine/pa194d.tm has 194 working states, 388 transitions, initial state 0,
and terminal 194. The halt label has no rows and is excluded from the count.
The tape is a two-way infinite binary tape, initially all zero, with the
head at position 0. Every transition writes one bit and moves one cell L/R.

Dense SHA-256:
4226b7702de554df4b52d10239b2bd7ad79ca90bd8faf2bd256552fe0c7fe81b
Native SHA-256:
bc8ab6c58badd137535938c9810e39d19152c49dd2eb26ef4ea07dbcf3157231

The native presentation starts in control 74 and halts in 254.
machine/pa194d.labels.json gives the exact dense-to-native map.

Construction and logical change
-------------------------------

The machine retains the supplied cached Combined controller, including
the zero-register jump at source site 26. The emitter's separate diagonal
head changes from Gamma(A) to Gamma(D). In its 190-token macro word this
is exactly three copyA -> copyD replacements, at zero-based token indices
121, 122, and 123. The separate logical proof must establish the calibration
of this modified head enumeration; the scripts do not assume source-step
identity with the original Gamma(A) emitter.

A new shared association of that word compiles to 69 raw readers. Nine
simultaneously valid history folds produce the total:

    134 fixed controls + 69 raw readers - 9 folds = 194.

The final AX break is implemented by dec D. D is provably zero whenever
that site is reached. The existing source-site-26 jump uses the analogous
X-zero fact. Both facts follow from an independently recomputed finite
positivity closure containing 263,244 pairs. The old and new closures and
all successors agree exactly. Source reassociation is checked by comparing
the entire resolved instruction graph with the original accepted tree
shape populated with the same modified word, including all jump targets.

Verification
------------

rebuild.py reconstructs the full table from the pinned fixed controller,
frozen grammar and nine explicit folds. It checks all 36 local fold cases
on the final simultaneous table, each requiring at most five physical
steps, and regenerates the complete 3,649-site source program.

independent_verify.py imports no compiler or arithmetic-box oracle. It
rederives four generic list-sweep lemmas from the literal table and checks
all 4,751 source cases, including both outcomes of every decrement, over
arbitrary natural register values, arbitrary extra header gap, and an
arbitrary nonempty finite spare list. Two independent source resolvers
must agree. A separate bytearray interpreter checks the entire blank-start
tape after 58,168 transitions: native state 84, head -2, source site 25,
logical registers (2,0,...,0), and 26 spare blocks of value 1.

The completed independent run performed 1,091,154 symbolic steps, with at
most 385 per case and minimum positive-duration constant 3. The complete
receipts, contracts, fold traces, invariant masks, and exact blank seed are
in evidence/. No new Lean or Rocq kernel theorem is claimed, and this
construction does not claim fewer than 194 working states.

Provenance
----------

The primary Program.lean, fixed rows, and original AX association come from
VladimirReshetnikov/ProveIt at revision
17f92105e2bc4317feae6c219cb2143437b482ff:

- PA/jamesyc-upstream/pa196/PA196/Program.lean.
- PA/docs/pa194_conpa_2026-11-13/construction/.

The Combined controller and site-26 zero jump are the supplied PA194C/CZ
constructions from the incoming packets. Their exact edits are retained in
rebuild.py. The independent runtime and dual source resolvers are preserved
from incoming pa194c_conpa.zip, verification/independent/reference/, with
original attribution and licenses in reference/.

inputs/winner.grammar.json and inputs/nine_folds.json freeze the new result.
inputs/separateD.word.json records the independently audited symbolic emitter.
