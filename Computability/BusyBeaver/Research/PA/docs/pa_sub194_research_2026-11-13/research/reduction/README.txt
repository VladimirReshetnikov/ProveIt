STATE-REDUCTION RESEARCH ARTIFACTS

RESULT
No machine with fewer than 194 states was established as a blank-tape PA
consistency machine. The runtime193 table in the enclosing package is a
runtime reduction whose blank initialization fails. This directory records
further reduction screens, a repaired context collector, and two 194-state
research compositions. No bounded negative search is a minimality theorem.

PLACEMENT AND OFFLINE REPLAY
This directory belongs at research/reduction/ in the delivered package.
It shares the package's runtime193/ source arrays and reference/haz/ runtime
and licenses. Python 3.10+ and a C++17 compiler suffice; no network is used.

From this directory:
    python3 reproduce.py
    python3 reproduce.py --full --output /tmp/pa-reduction-replay

For a staging directory outside the delivered package, add:
    --reference-root /absolute/path/to/the/enclosing/package

The default run compiles both C++ programs, regenerates corrected radius 4
source contexts, reproduces the 346-candidate pool, and replays the historical
65041-simulation bootstrap screen. The full run also checks radius 6, the 19
speculative box candidates, HAZ register interference, and both194-state
companions. Run with assertions enabled; do not use Python-O.

THE193-STATE CORE AND PROOF BOUNDARY
The core, its source, and its precise arithmetic-box lemma are documented
under ../../runtime193/. Its4780 symbolic source outcomes pass. The changed
row51/0 has a separate two-step argument on valid unary register cells; it is
not justified by silently retaining the old arithmetic oracle. Successful
Python execution is not a proof-assistant theorem.

CORRECTED LOCAL CONTEXTS
collect_source_contexts.py deliberately excludes blank startup. It observes
every source outcome and now explicitly adds interior positions of accelerated
constant-symbol self-loops. The inherited boundary-only procedure omitted
those positions. At radius 4, the repair changes8331 contexts to 8357; at
radius 6 it changes29299 to 29421. Both radii now yield the same 346 candidate
row rewrites, including 19 speculative arithmetic-box rows and 327 outside
the boxes. The 9 apparent q35/0 rewrites disappear.

The symbolic engine still abstracts arithmetic-box interiors, and the
collector intentionally does not narrow those controls. A box-row candidate
therefore has no source-equivalence claim from this collector. Even for a
non-box candidate, final accepted machine status would require universal
refinement, exact whole initialization, and logical calibration.

HISTORICAL BOOTSTRAP SCREEN
inputs/runtime193_neutral_source.tsv retains the original 336 outside-box
candidate edits, including the 9 subsequently rejected q35 variants, plus
the unchanged core. It is deliberately NOT relabeled as a certified neutral
pool. The historical any-frame search tested all 193 existing initial states
for each of these 337 tables.

Acceptance in that strongest screen means only a complete physical source
frame at a source site25..44, with arbitrary values of ALL 9 registers,
any tape translation, padding 48+n for n>=0, and any finite nonempty spare
tail. It does not infer consistency-machine status from the register values.
The detector checks the entire finite tape support. No such frame occurred.

Recorded totals:
    tables337; starts per table193; simulations65041
    literal transitions101840170
    halts674; certified outward blank rays62799; bounded runs1568
    complete physical frames0

Each simulation is limited by 200000 transitions, head displacement 20000,
and support size 20000. A bounded run is not proved permanently unsuccessful.
The corrected327-candidate outside-box pool is a subset of this screened
historical pool. Radius6 introduces no additional candidates.

The19 speculative box variants were screened separately: 3667 simulations,
30044 transitions, 39 halts, 3628 rays, 0 bounded runs, 0 accepted seeds.
No equivalence lemma is asserted for those mutations.

REGISTERS
zero_interference.py computes the sound 0/positive relational abstraction of
HAZ from source 25 and initial [2,0,...,0]. It reaches 263604 abstract states
and all 3650 sites. No two of the 9 counters can be directly coalesced under
this abstraction. This says nothing about stronger abstractions or different
register representations. The only ruled-out decrement outcome is the
positive branch of the explicitly added final-X test.

194-STATE COMPANIONS
companions/PA194R_AD and PA194F_AD contain exact native tables, pinned source
arrays, and receipts. Both compose the symmetric cached controller/final
zero test with the A/D physical swap. Each passes 4746 source outcomes and
reaches its complete blank source seed after 57736 transitions. All arithmetic
box rows equal the shared original194-state table. verify_companions.py
reruns these checks. These companions do not meet the requested sub194 target.

OTHER NEGATIVE SCREENS
The recorded HAZ and companion neutral-plus-quotient receipts cover 328,
275, and 290 candidate edits respectively, each followed by the supplied
joint two-row quotient synthesis at radius 4 and 100 steps. All 893 runs found
zero quotients. Some reused the historical boundary-only contexts; these
are screening records, not proofs of neutral equivalence after the first edit.
joint_return_merge.cpp is the pinned attributed upstream synthesizer.
These longer historical suites are not automatically rerun by reproduce.py.

PROVENANCE AND LICENSING
provenance/sources.json identifies the pinned repository revision and imported
files. The symbolic runtime and original quotient synthesizer derive from
the supplied PA research, including James Chang and other attributed work.
Retain ../../reference/haz/licenses/ and its PROVENANCE.json when copying this
directory. Fresh code here consists of the register abstraction, neutral-row
synthesizer, whole-frame bootstrap detector, portable replay, and the scan-
interior correction to the inherited context-generation method.

STATUS OF THE TWO-EDIT IDEA
The proposed two-edit repair through q35 was rejected before second-stage
synthesis: its9 first-stage rewrites failed generic symbolic command checking
and are removed by the corrected finite-window envelope. The recorded
two_stage_startup.log is a rejection record, not an exhaustive two-edit search.
