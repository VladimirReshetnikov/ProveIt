# Dependency and portability map

## Executable checks

The new builders and producer checkers require only Python 3.10+ standard
library modules. The independent low-degree, positive, and power-graph
review scripts use SymPy 1.14.0; this exact version is declared in
`requirements.txt` and checked by `reproduce.py`. No Git clone, network
connection, TeX installation, or Lean/Rocq toolchain is needed to rebuild
and audit the equations.

A TeX installation is needed only to recompile the manuscript. The PDF is
already included; consult `report/report.tex` for the packages it uses.
Historical `.lean` files are retained as exact source references, not as a
claim that this release reran their proof-assistant dependencies.

## Mathematical and coefficient dependencies

1. **Integer coprime fusion.** Read `integer/PROOF.md` first. The six actual
   fixed coefficients are in `integer/coefficients/`, with full finite
   reconstruction under `coefficients/recipe/`. The normalized 17-integer,
   signed, centered, and interpolation predecessor proofs are retained under
   `integer/source/`. The source ledger and component manifest authenticate
   these copied materials. In particular, the ordinary compiler/refutation
   boundary is in
   `integer/source/provenance/rootfusion/CALIBRATION_STATUS.md`, and the exact
   machine/native-source texts and pins are in its `upstream_ordinary/`
   subdirectory. The newer repository pin and inherited source pins are
   distinct and recorded without conflating them.

2. **Positive coprime Pell fusion.** Read `positive/PROOF.md`. The frozen
   predecessor is `positive/source/parent_equation.json`. Its complete
   coherent original compact44 coefficient tuple is under
   `positive/coefficients/`; it must not be replaced by source34 or the
   separately repaired BFS tuple. `positive/source/SOURCE61.tex` states the
   inherited normalized positive-kernel interface and calibration;
   `FREE_J_PROOF.md`, `DIRECT_PROOF.md`, and other copied source proofs retain
   the exact transformations. The BFS files are provenance for a distinct
   alternative tuple, not an instruction to mix coefficient components.

3. **Low-degree integer carriers.** Each variant's ordinary proof maps to
   the fixed normalized17 predecessor. The local `source/` excerpts and six
   payloads support that map. The full inherited native/compiler/refutation
   chain is shared with the retained integer source tree, not duplicated as
   an entire historical archive. `lowdegree/DEPENDENCIES.md` gives the
   precise component paths and source pins.

4. **Positive-power graph and tiling fixture.** `alternative/PROOF.md` proves
   the graph theorem with its stated nonnegative/positive domain contract.
   Its original Pell-index and strict-boundary tiling sources, licenses, and
   pinned reference Lean files are in `alternative/prior/`. The emitted
   four-corner tile fixture is an ordinary arithmetic composition, but no
   calibrated proof-checker tile set is supplied by this component. In
   particular, the raw 943-tile list has an all-zero tile and is not silently
   substituted as a Con(ZFC) endpoint.

## Historical records versus active runtime requirements

Copied source/provenance files are immutable excerpts from earlier archives.
Their old READMEs, bibliography paths, or historical builder defaults may
refer to layouts and auxiliary files of those original archives. They are
retained for attribution and mathematical review; this release does not
claim every historical program is a standalone runnable package. The
current top-level `reproduce.py` enumerates the new active builders/checkers
and verifies that their actual runtime dependencies are included.

Likewise, `baseline/FETCH_LEDGER.json` and the baseline citation documents
record the original research acquisition paths and hashes. They do not
imply that `baseline/ProveIt`, `baseline/budget`, the original incoming ZIPs,
or the old acquisition script are distributed. Source SHA-256 records are
provenance, not a replacement for an unbounded mathematical proof.

## Bounded late comparator review

`baseline/LATE_BASELINE_NOTE.md` and its JSON ledger distinguish later
comparison findings from the original construction source. The small
`baseline/late_head_evidence/` collection preserves the exact cited texts
and relevant comparator DAGs, not a new repository checkout or runtime
dependency. Neither the late positive comparator nor the measured quartic
frontier is silently substituted for a component's fixed source tuple.

`baseline/check_late_evidence.py` authenticates all ten saved late-review
source files and independently traverses the two supplied comparator DAGs
to recover 98 and 103 live binary operations. It runs in both Python modes
from the release runner, includes six malformed-DAG controls, executes no
upstream programs, and does not claim to reprove the reported degrees.
