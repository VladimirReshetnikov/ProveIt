PA194QH5: coefficient-five Q / no-push / cached-only-Shift composition

RESULT
194 working states, binary alphabet, one two-way infinite blank tape.
No machine below 194 is asserted by this component of the research.
The ordinary mathematical argument gives
  PA proves Nonhalting(PA194QH5, blank) iff Con(PA),
using the explicitly identified inherited calibration and the new complete
source/physical bindings. No new end-to-end Lean/Rocq or iPRA endpoint is claimed.

TABLE
machine/machine.tm: dense states 0..193, start 0, halt 194; 388 rows.
Each row: current_state read_bit write_bit L_or_R next_state.
machine/machine.native.tm: native labels, start 74, halt 254.
Dense SHA-256:
94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5
Native SHA-256:
45c649af2600c2cfa8bbb07ce2a674e07945d985af6c9fc8aaa8563df1225c05

RUN
Python 3.10+ and standard library, with assertions enabled:
  python3 -B verify.py --receipt fresh-verification.json
--quick skips only the independent physical replay; its omission is recorded.
For table reconstruction alone:
  python3 -B construction/build.py --output rebuilt-machine
No network or repository checkout is required.

PROOF AND VERIFICATION
proof/qh5_preservation.tex: complete new proof fragment for incorporation in
  the main report, with all inherited mathematical dependencies identified.
references/logical/: unchanged calibration, generic constructor, and older
  controller reports. Their historical runtime counts and controller sections
  are not descriptions of QH5; the new proof explicitly supersedes them.
references/lean/: unchanged modules and local import dependency closure;
  Std is an external Lean standard-library dependency. No new endpoint.
machine/source_binding.json: all 61 source body replacements and exact relocation.
machine/independent/: independent literal-table symbolic certificates.

Observed: 3,714 source sites; 4,815 outcome contracts; 32 simultaneous fold cases;
construction 1,576,144 symbolic operations (max 499); independent 1,150,677 (max 403);
4 literal-row register-list lemmas; min positive-duration constant 3;
whole blank initialization 58,088 literal transitions.
These symbolic counts are not bounds on the entire machine run.

ORIGIN
ProveIt commit 2337ce611a26e308697ccbddb2a1636f989f01c3, PA/docs/pa194qh6_conpa_2026-11-13.
PROVENANCE.json and licenses/ preserve exact sources and credits.
The new composition changes one native transition in the recurring constructor,
from 190 1 1 R 330 to 190 1 1 R 99, and binds it to coefficient-five arithmetic.
Materiality and novelty are separate: the full main-research census checks
against the pinned PA and incoming corpus, including additional encodings.
