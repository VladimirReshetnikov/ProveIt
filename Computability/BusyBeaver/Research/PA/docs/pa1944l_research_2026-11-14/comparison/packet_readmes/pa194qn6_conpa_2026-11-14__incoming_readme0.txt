PA194QN6: a new verified 194-state composition for Con(PA)
======================================================

RESULT

The literal binary, single-tape, blank-start machine has 194 working states.
There are 388 rows; start is 0 and the separate halt label is 194. The tape
is two-way infinite and initially zero everywhere; initial head coordinate 0.
All transitions move exactly one cell left or right.

The ordinary mathematical theorem, using the explicitly retained inherited
syntactic PA-calibration arguments, is:

  PA proves: Halt(PA194QN6, blank) iff PA has a proof of 0=1.
  Therefore PA proves: Nonhalting(PA194QN6, blank) iff Con(PA).

No machine below 194 states is claimed by this package. No newly compiled
end-to-end Lean/Rocq theorem or completed machine-specific iPRA endpoint is
claimed. The new contribution is the concrete verified composition, source
binding, and physical realization; the constituent ideas are inherited.

CONSTRUCTION

The machine combines Q's exchanged universal-distribution premises with
N6's coefficient-six constructors and no-push MP controller. It retains the
original sum-one Shift test, distinguishing it from QH6. Successful MP
returns (b,w,b,0), b=d+x. Shift halts iff t+h=1, otherwise it maps the store
to (h,tail(w),d,head(w)). The Q source replaces 83 of 3,776 resolved N6
instructions, preserving every other instruction exactly.

The count is 135 fixed controls + 67 axiom readers - 8 simultaneous folds.
Thirty-two local fold contexts, 4,877 arbitrary-register source outcomes,
and the entire blank startup tape were checked. A separate literal-tape
engine rederived four register-list lemmas from actual rows and independently
replayed all source outcomes without importing arithmetic-box contracts.

START HERE

report/pa194qn6_conpa.pdf      Integrated comparison, full proof, transition
                             table, and ledgers for all 66 supplied packets.
report/pa194qn6_conpa.tex      Editable source for the integrated report.
machine/machine.tm           Authoritative dense transition table.
machine/machine.native.tm    Native table (start 74, halt 254).
machine/labels.json          Exact dense-to-native map, including halt.
proof/qn6_preservation.tex    Self-contained report fragment: calculus,
                             proof translations, all-store compiler,
                             scheduling, soundness, physical transfer.
references/                  Inherited logical calibration and Lean templates.
construction/build_qn6.py     Deterministic portable builder.
verify.py                    Portable acceptance-check runner.
PROVENANCE.json               Pinned source revision and input hashes.
comparison/                  Current corpus census, all 66 packet entries,
                             frontier graph representatives and exact novelty
                             checker, including rejected tables.
research/                    Completed bounded negative searches and their
                             inputs, source code, logs and limitations.
licenses/                    Retained supplied notices.

The PDF includes the complete 388-row machine table, the exact calculus,
the all-store proof-word compiler, the comparison and research results.
SHA256SUMS covers the complete release. Imported dependencies and their
licenses are retained; the new work is the explicit verified composition
and comparison, not a claim to the invention of its existing ingredients.

For the closest Q6 comparator, the native table changes only row (164,1),
whose destination changes from 98 to 114. This removes a 19-instruction
dummy-zero stack push. On the sound store (0,3,0,0), successful MP_0 leaves
w=3 in QN6; Q6 instead pushes zero and obtains w=9. The one-row proximity
and the material command-semantics difference are both documented.

REPLAY

Python 3.10 or later and its standard library suffice. No network, solver,
external checkout, or proof assistant is needed. Keep assertions enabled.

  python3 -B verify.py

The full command rebuilds in a fresh temporary directory, checks exact byte
reproduction, all construction contracts, complete blank initialization,
source and coefficient binding, the symbolic proof-word compiler, the
61-line K/S exchange proof, corpus novelty, and the independent literal-tape
engine. It removes only its own temporary directory and leaves the release
files unchanged. The literal engine takes roughly a minute or two, depending
on the host.

  python3 -B verify.py --quick

Quick mode omits only the independent literal engine. The receipt explicitly
records this omission; it does not present old independent results as fresh.

The construction and independent literal engine were both run successfully
for this delivery. The portable wrapper was also run in both quick and full
modes, including a fresh independent replay in the rebuilt temporary directory.
Their detailed original receipts are included under machine/ and verification/.

OBSERVED VERIFICATION

  Construction contracts:             4,877
  Construction symbolic operations:   1,565,180
  Construction maximum per contract:  490
  Independent symbolic operations:    1,145,033
  Independent maximum per contract:   397
  Minimum positive-duration constant: 3
  Whole blank startup:                58,320 literal steps
  Source instructions:                3,776
  Independent list lemmas:            4
  Distinct prior 194-state graphs:     76
  Exact matches to prior graphs:       0

The symbolic domain covers arbitrary natural registers, both decrement
branches, arbitrary nonempty finite spare-register lists, and arbitrary
natural affine header gaps. Symbolic counts are checker operations, not
bounds on the machine's full execution. Finite startup is not evidence of
infinite nonhalting.

IDENTITY

Dense SHA-256:
72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9
Native SHA-256:
372d68753d206e5396312951a6be777179757598ad1384784db45764efd61fbc

Novelty is relative to the recognized literal/JSON corpus at ProveIt commit
2337ce611a26e308697ccbddb2a1636f989f01c3. The comparison allows arbitrary
control renaming, any graph-spanning start, reflection, global bit exchange,
and ignores write/move actions on halt edges. This is graph novelty, not a
claim of semantic inequivalence, global priority, or a state lower bound.
