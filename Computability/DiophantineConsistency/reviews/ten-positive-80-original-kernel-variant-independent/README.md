# Independent external review of the original-kernel 80-row variant

The checked candidate has the same ten witnesses, fixed-port names, output,
positive domain and all 80 ordered source rows as the pinned q-cube V²
parent, but a different fixed kernel payload. Independently walking every row
confirms that operands are defined before use, all 80 operations are reachable
from the output, and the operation counts are 48 multiplications, 18
additions and 14 subtractions. The counts apply to the given unshifted graph;
they exclude any representation or evaluation cost for fixed numerals.

The four compressed payloads are byte-for-byte identical to the retained
original tuple in `free-j-polarized-positive/source/positive/coefficients/payloads`,
and their complete decompressed minimal unsigned little-endian bytes agree as
well. The raw SHA-256 values are:

| Port | Raw SHA-256 |
| --- | --- |
| β | `0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d` |
| K0 | `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e` |
| MC | `6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4` |
| MF | `48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737` |

The review independently reruns the existing symbolic-K recipe audit: its
external reconstruction from pinned Lean source text equals the full raw K0
above. That reconstruction is a manually transcribed finite calculation, not
the execution of Lean definitions or a kernel-checked equality relating a
filesystem byte string to `paramKernel rho`. The original manuscript's own
copies are unavailable; the source is the retained reconstructed tuple.

The candidate JSON labels the degree as inherited. This review establishes
degree **exactly 750** independently for these actual numeric constants. The
checker substitutes the same indeterminate `t` for all ten witnesses,
reduces each actual constant modulo `1,000,000,007`, and tracks degree and
leading coefficient through every row. No leading coefficient vanishes in
any row; the output has degree 750 and leading coefficient 12,396,338 modulo
the prime. Recursive operation degrees give a matching multivariate upper
bound, while the nonzero specialized coefficient gives the lower bound.
The separately written author `verify_degree.py` was read and rerun: it
reports the same bound and coefficient for the hash-pinned candidate and
payloads and rejects optimized Python. It tracks the coefficient at the
structural degree bound even if intermediate coefficients were to vanish;
the nonzero output coefficient is sufficient for the certificate. The review
checker additionally rejects any intermediate leading cancellation, none of
which occurs for these inputs.

The checked `build.py` reads the hash-pinned parent and four source payloads,
validates their reported gzip/raw hashes, emits the copied payloads and its
deterministically serialized JSON, and resamples parent/payload hashes. Two
separate executions in the same isolated temporary tree both reproduced the
candidate JSON and all four outputs byte-for-byte. The checker separately
tested rejection of optimized Python, a changed parent, and a changed valid
gzip for each input port. This is a finite reproducibility test; the builder
does not establish the semantic relationship to the Lean graph or prove any
machine or arithmetic theorem.

The successful captured check is `observations/attempt03/`, which adds the
author degree-script check. The retained first capture incorrectly called
this a receipt audit; the second corrects that scope while using the earlier
checker. The work provides external evidence that this *distinct*
specialization uses the original symbolic recipe's reconstructed kernel. It
does not establish Lean/file binding, a full graph-to-machine equivalence,
either direction of its iPRA consistency theorem, or minimum equation size.
