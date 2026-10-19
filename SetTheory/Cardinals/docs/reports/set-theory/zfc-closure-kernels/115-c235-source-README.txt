SOURCE/DECODER CONTRIBUTION TO THE 235-STATE CONSTRUCTION

Final status: the seven-rotation basis and the folded 235-state table both
pass the fresh unbounded instruction-runtime proof on all 8,386 guarded
source cases. They also pass complete source-graph comparison, independent
all-tape local fold proofs, and exact blank startup comparison.

Portable deterministic construction
-----------------------------------
Python 3.10 or newer, standard library only, assertions enabled:

    python3 -B build_zfc235.py --baseline-dir EXTRACTED_236_PACKAGE \
        --output-dir NEW_DIRECTORY

The builder reads:
    EXTRACTED_236_PACKAGE/machines/zfc236_old.tm
    EXTRACTED_236_PACKAGE/source/sites_logical.json

The exact baseline package is the original zfc236-research-20261019 bundle
from the pinned ProveIt 236-state commit. It is retained unchanged in
vendor/zfc236.zip; no network lookup is used during reproduction.

Outputs are flat. The main reproduce.py script compares them byte for byte
with the supplied machines/, source/ and evidence/ files:

    zfc_rotated236_old.tm          exact source-rotated basis
    zfc235_old.tm                  final table, inherited labels
    zfc235.tm                      final table, canonical labels
    sites_logical.json            final expanded source leaf list
    source_rotation_certificate.json
    startup235.json
    construction235.json
    renumbering235.json

The builder checks input/output hashes, every intermediate guarded source
graph, all pure-decoder rotation conditions, and the complete startup.
Independent local fold and unbounded runtime checks remain separate proof
artifacts. Do not mistake construction/startup replay for runtime replay.

Exact output identifiers
------------------------
Rotated 236-state basis:
014133f39c409277c239fa327db17800b4e886a5c7a5a73034ed87e4978820aa

Final 235-state table, inherited labels:
d017abe46023a4154085a2fe2c04c8d66bbbec53b81d193d520ad697d171cbd4

Final 235-state table, canonical labels:
4a2c6b05e347522236dc6faf0bde5f71480aa6c6795faa6f20a11f1a1601895f

Final source:
c17ab40e032e79dca03eaa955a78dbcd65bd030795ecc232dc504aff1551cb20

Canonical start 0, dispatcher 84, separate halt outcome 235; working states
0 through 234. Inherited labels: start 95, dispatcher 96, halt 254. The
alphabet is binary, tape is two-sided, and all moves are L or R.

Seven rotations, in order
------------------------
Direction L means (A,(B,C)) -> ((A,B),C); R is the inverse.

    R 138/211: chunk sizes 539, 56, 242
    L 116/134: chunk sizes 56, 121, 125
    L 162/116: chunk sizes 108, 177, 125
    L 199/227: chunk sizes 2965, 177, 940
    R 227/197: chunk sizes 1919, 1046, 177
    R 197/115: chunk sizes 480, 566, 177
    R 115/229: chunk sizes 406, 160, 177

Every chunk is closed, with boundary (0, 0, false). Each stage retains 224
source DAG nodes and 6,455 leaves. The final source has depth 48 and maximum
zero run 6; intermediate stages 2, 4, 5 and 6 have zero run 7. Only the final
binary source/table pair is calibrated. Exactly 2,524 final leaf paths
change. The basis has 17 net edited literal rows in 10 states.

The final fold deletes state 193 and redirects its incoming transitions to
74. It sets 74/0 = 0 L138 and 74/1 = 1 L116. The immediate left bit encodes
the old state: 0 for 74, 1 for 193. Four exact three-step routes reproduce
the four old rows; the other 468 rows commute in one step. Relative to the
original 236 table there are 20 changed surviving rows and two deleted rows.

Discovery provenance and scope
-------------------------------
The successful construction does not require the search to be replayed.
The fixed seven-stage trace is its complete constructive witness. A broad
deterministic source walk examined 10,000 iterations (seed 20261019), with
9,676 distinct literal tables and 324 revisits. It found nine local fold
hits: seven in the 74/193 family and two in a 136/225 family. These were
local fold hits, not nine calibrated reductions. Long rotation histories
could break compact runtime helpers despite preserving the source graph.

The 74/193 mechanism was reduced to four relevant rotations. That core
failed because it introduced a seven-zero source path. A repair beam
(seed 23574, beam width 200) then generated 2,535 candidates and rejected 65
for failing the required immediate-left-bit tags. It permitted temporary
zero runs up to eight, protected known helper states, and ranked candidates
by the number of bad prefixes, maximum depth, and minimum chunk size. The
first candidate passed to the full finite profile filter was the successful
three-rotation repair displayed above. Full unbounded proof followed.

Rejected history is not distributed as if it were valid machinery. In
particular, older scratch files called two_rotations, four_rotations or
six_rotations are not the final construction. One repair rotating 105/123
passed source comparison but changed the predecessor context used by an
arithmetic helper; another fold involving 86/187 disturbed the inherited
182/223 helper route. These failures motivate the independent runtime
obligation and should not be interpreted as evidence against the final
seven-rotation bytes.

The reported search counts establish no state lower bound and no exhaustive
claim about other source trees. Sequential associativity and predecessor-bit
folding have prior implementations in the baseline 236 package; the new
contribution is the specific 235-state composition and its proofs.

Exposition
----------
sections/source_rotations235.tex is included in the main
report. It requires amsmath and booktabs, defines no global macros, and uses
only inherited state labels. Its statements agree with the final exact
machine/source pins above. The main report supplies the inherited logical
calibration, broader formalism research, bibliography and proof-assistant
boundary.
