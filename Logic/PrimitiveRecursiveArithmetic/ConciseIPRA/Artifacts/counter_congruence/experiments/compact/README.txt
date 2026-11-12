COMPACT COUNTER-CONGRUENCE EXPERIMENTS: NO FRONTIER IMPROVEMENT
================================================================

Result
------
These are complete standalone source experiments preserving the compact raw
syntax, sorted opener, reusable context, shared continuation, and JSON/verdict
driver of the supplied generated-assumptions checker. They do not import the
readable checker or an uncounted proof kernel. They were measured with the
unchanged source_measure.py supplied in the comparison corpus.

Whole-program normalized measures (CPython 3.12.14):

  Program                          Tokens   AST   Bytes
  generated_checker.py baseline       281   318     685
  R_general_transport_control.py      296   333     704
  counter_compact.py                  343   395     881
  fused_facts.py                      341   388     892

The current corpus coordinate envelope is 281 / 315 / 685, with different
programs attaining its coordinates. The separate import-only variant found
by the primary agent improves the byte coordinate to 680 (281 / 320 / 680);
that mechanical change does not alter the negative result here.

No program in this directory establishes a reduction of the frontier. The
main delivered readable checker is the audited implementation of the new
calculus. These nonwinning source experiments received 52 successful finite
smoke/boundary runs, but not a complete independent audit of every permissive
raw serialization alias. They must not be presented as universally certified
replacement kernels. No source-size saving is inferred from a code fragment.
They also retain the inherited raw unary-formula vocabulary; they do not
enforce the main tagged checker's narrower exported-object and Q-only-Hyp
boundary. That boundary would need additional code or an explicit conservative
extension argument before claiming exact implementation of the main protocol.

What was actually changed
-------------------------
The unchanged baseline has initialized scalar iteration and a shared
Eq/Q transport test. Its general formula-opening function is already required
by DI, DE, and QE. Restricting equality therefore does not delete that helper.

The R control changes scalar iteration to the successor-seeded counter-aware
R of the report. It checks the supplied numerical source at root, adds the
counter substitution, uses successor seed [t] at zero, and checks the entire
generated equation before the common fresh-variable continuation. This
strictness excludes the baseline's extra safe fresh-zero aliases; canonical
computation certificates remain available. The R change costs 15 tokens,
15 AST nodes, and 19 bytes in this particular implementation.

counter_compact.py then replaces unrestricted formula transport by separate
RL, CC, and QE behavior. CC is recognized by constructing both displayed
R endpoints with a two-field [seed,update] tail. RL replaces only the left
root of an equation, using its requested right endpoint as the minor's right
endpoint. QE specializes the actual unary major's matrix. DE and the DI
case/progress choice keep the inherited shared continuation. This logical
split adds 47 tokens / 62 AST nodes / 177 bytes over the R control.

fused_facts.py makes a further real fusion: a CC result is added as a checked
local equality and goes through the same continuation as arithmetic facts
and logical hypotheses. It removes CC's separate successful return, saving
two tokens and seven AST nodes relative to counter_compact.py, but increasing
the byte count by eleven. Its logical split still costs 45 tokens / 55 AST
nodes / 188 bytes over the R control.

Canonical mathematical argument
-------------------------------
Every added arithmetic equation is checked at formula root before freshness.
The source R term is separately checked before its update is opened. The
first opening at depth 3 substitutes the predecessor counter; the second
opening at depth 1 substitutes the recursive state. Expanding *n at the first
opening also requires a genuine singleton successor counter even when the
update ignores both arguments. This avoids the old binary-counter/constant-
update unsoundness. The two displayed equations are therefore R0/RS on the
canonical syntax. The strict whole-equation opening prevents a new fresh
parameter from being silently inserted into their source or target.

For a proved binary major [s,u], counter_compact.py's terminal CC test accepts
only a goal [[s,a,h],[u,a,h]], with a two-entry tail. Counter-only congruence
justifies it. Its RL branch changes [u,r] to [s,r], which is exactly root-left
replacement. An endpoint mismatch merely preserves the requested goal and
adds the inherited harmless truth, so it supplies no unsupported conclusion.

In fused_facts.py, a nonempty tail generates [[s,*t],[u,*t]] as a local fact,
then immediately runs the whole-formula opener. A two-entry tail is CC. A
one-entry tail consists of two numerical binary annotations, each of which
the inherited decoder denotes as zero; the fact is 0=0. A longer tail is
rejected by the arity bound. An empty tail selects RL rather than this fact
rule, so no primitive successor-congruence rule was smuggled into the union.
The generated fact is validated before allocation of the next eigenparameter;
using it by a context lookup is the ordinary derived cut with that theorem.

The old sorted-decoder invariants still require a full successful-trace audit
for all noncanonical aliases. The arguments above and the executable checks
justify retaining these as concrete experiments, not claiming a universal
implementation theorem from the 52 tests.

Packet changes
--------------
The R control retains the baseline's four-field packets.
The two new equality experiments use three-field packets [m,s,t].
The proof array is consumed from its end, with the goal last.

* m false, t false: s is the numerical R source for a generated equation.
* m false, t true: t is the DI numerical witness; m=0 selects progress only
  at a literal equation, while m=[] selects case, as in the inherited code.
* m a paired formula: prove m, then add its opened internal Q clause.
* m a unary clause: prove it by the inherited context mechanism and use t
  as its QE target.
* m an equation: counter_compact.py uses t as a possible CC tail, otherwise
  tries RL. fused_facts.py uses nonempty t to generate a CC fact, empty t
  for RL. The s field is unused at these major edges.

Scope of the finite checks
--------------------------
Run python3 check_attempts.py. It exercises both complete programs under
ordinary Python and -O, for 52 runs. Positive cases cover R0, RS's counter
and state coordinates, derived reflexivity through RL, CC, DI, and DE/QE.
Negative cases cover wrong R0, CC seed/update alteration, the known malformed
binary-counter attack with a constant update, an escaped update coordinate,
and an unallocated numerical parameter. All passed in the recorded run.

Files
-----
counter_compact.py                 Separate terminal CC, RL, and QE.
fused_facts.py                     CC as a generated local fact.
R_general_transport_control.py    Matched arithmetic-only control.
metrics.json                      Unchanged-normalizer full-module results.
check_attempts.py                  Untrusted test harness.
smoke_tests.json                   Exact finite test receipt.

Provenance
----------
The three executable sources adapt the generated-assumptions draft checker
from ProveIt commit 2fdcf5bf988bead821c416649f713f98b7ed8776, path
docs/drafts/ipra_generated_assumptions_2026-11-10.zip. The upstream license
remains in the enclosing report's reference directory. The parser, opener,
context policy, shared continuation, and public driver are inherited. The
new source changes are the R arithmetic boundary and the RL/CC branch forms.
