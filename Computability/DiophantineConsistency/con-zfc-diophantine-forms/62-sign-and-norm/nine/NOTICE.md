# Attribution and scope

This is AI-assisted mathematical research prepared for Vladimir Reshetnikov
and ProveIt. Internal review is AI-assisted and is not an external human
endorsement. The new prose and authored code follow the ProveIt MIT No
Attribution terms in `LICENSE`. Inherited materials retain their original
notices and licenses; this notice does not relicense them.

The finalizer and its correctness proof come from ProveIt package59
(`59-degree-separated/nine_free_adjunct`). `build_nine.py` is an adaptation
of that builder. The general arithmetic-DAG utility `circuit.py` comes from
package53 (`53-selective-quad/nine`). The exact compact coefficient tuple,
its builder and adapter proof come from package44, with matching proof from
package39 and whole-tuple binding from package52. The shifted parent is
package31's 60-operation source. The old sparse parent is retained solely
to check the precise row change. `SOURCE_PINS.json` records the pinned
repository paths and hashes. Original notices are retained under `upstream/`
and `licenses/`.

Newly authored here are the changed source specialization and its explicit
row comparison, target-order certificate, precise coefficient majorant and
popcount calibration for those parameters, shared addition-chain rewrite,
fixed-leaf materialization and local audits. The second audit was drafted
separately, then its grouping implementation was corrected by the component
author; it imports no project builder or verifier. It is a second finite
check, not a claim of an independently reproved universal compiler.

James P. Jones's ratio and Pell constructions, the native Wang943 compiler,
the K215/refutation calibration, and the antecedent work credited by
ProveIt are inherited. These include the respective contributions credited
to Mira, Elliot Glazer, JeFF, Andrew James Wade, BusyCoq and the Coq Library
of Undecidability. No consistency proof, global minimum, new universal
variable-count theorem, or end-to-end formal proof is claimed.
