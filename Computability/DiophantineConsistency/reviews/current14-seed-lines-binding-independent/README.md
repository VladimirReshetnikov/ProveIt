# Independent review of the 14-variable decimal seed binding

The reviewed Lean theorem states that all entries in `digits = lines.flatten`
are below ten, that the flattened list has 715 entries, and that folding it
left with `10 * acc + d`, starting at zero, equals the **imported**
`DecimalMachine215.seed`. Its proof uses `decide +kernel`, and both recorded
successful runs report no axioms. This is a theorem about the explicit Lean
lists and the imported seed; it does not itself interpret TeX, PDF, the full
coefficient recipe, or the iPRA endpoint.

A separate Python parser independently reads the twelve Lean lists as literal
lists, checks the digit bounds, independently performs the decimal fold, and
compares the result with the current `DecimalMachine215.lean` source numeral.
It also compares every line with the TeX source and `pdftotext -raw` output.
The line lengths are eleven times 62 followed by 33, and line seven is the
only line with a leading zero. The author's display checker was rerun and
reproduced its recorded JSON, including its three mutation controls; it and
the runner both reject optimized Python.

The two successful receipts use the same inherited direct object, now resolved
from the compact provider to its retained author object, with matching SHA-256
before, after, and at review. The resulting two objects have identical bytes,
and the second's stdout and stderr match its retained logs. The failed initial
string-parsing attempt has a nonzero recorded exit and its source matches the
preserved failed source. The runner refused a reused attempt name and an
optimized invocation; the two successful object files and three receipts were
unchanged by these refusal checks. Resource observations are sampled, not
continuous.

Run `python3 -I -S -B check.py` from this directory, or provide the script's
path from any working directory. The script is read-only, checks fixed hashes
of the reviewed files and compares guarded file hashes before and after, and
requires the retained absolute `/tmp` provider and outputs. Its captured
successful stdout is in `observations/stdout`; the review run exited zero with
empty stderr. No new Lean process was started.

This review does not authenticate the imported object's source-to-object
origin or complete project, package, and dynamic-import ancestry. The current
source numeral matching the digits externally is not proof that the inherited
object was compiled from that source. PDF text extraction checks the retained
file's extracted digit lines, not general TeX or PDF semantics. The two Lean
observations share the same inherited provider and are not an independent
coherent replay.
