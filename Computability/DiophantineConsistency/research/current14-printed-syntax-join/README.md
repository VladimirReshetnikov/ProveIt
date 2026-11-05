# Draft: join the four printed port recipes to the equation syntax

This is an **unchecked draft**, not an endpoint or a Lean proof. It proposes
using the existing `Current14LiteralPorts` assembly to write all four ports
in structured printed-recipe form, taking the integer floor of the displayed
rational K (whose integrality the assembly establishes). It then proposes to
replace the port tuple in `expressionAt` and `naturalExpression`. A successful
proof could be used as a bridge in a later coherent endpoint build, but it
would not parse TeX or PDF and would not itself prove an iPRA endpoint.

The first bounded Lean run exhausted its 2 GiB Lean memory setting in the
interpreter after 66 seconds; it did not produce an object. After sealing
large definitions and raising the bound to 4 GiB, attempts 02, 03 and 04 all
reported kernel memory exhaustion while checking `ports_eq`; subsequent
printed axiom diagnostics contain the failed declaration and do not establish
any theorem. The retained observation files record the actual exits and
inputs for each attempt. The current source is the failed attempt 04 version;
earlier source versions were not separately retained, but their hashes and
complete tool output are in their respective observations. The most recent
runner source is recorded in the attempts; these checks used the assembly's
captured mixed provider and did not authenticate its full ancestry.

No additional retry is justified merely by raising limits. A follow-up should
avoid kernel reduction of the huge concrete port expressions; attempt 04
introduced an abstract finite-vector transport lemma, but this alone did not
resolve the memory failure. A successful join also needs a source-authenticated
endpoint provider. If retried with these
captured inputs still available, choose a fresh name:

```sh
python3 Computability/DiophantineConsistency/research/current14-printed-syntax-join/run.py --attempt fresh-name
```
