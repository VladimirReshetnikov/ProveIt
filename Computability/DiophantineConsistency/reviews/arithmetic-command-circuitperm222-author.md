# Actual C222 finite circuit graphs: author record

26 October 2026. Root authored and fully read134 main/36 check lines and
both complete private drivers before execution. Final main/check pass in
7.129s/1.951s with empty main and nine standard-only axiom reports.
Independent review/replay is separate.

Circuit is external finite syntax. Its four inputs range over any internal
IΣ1 model; each fixed circuit has a literal parameter-free five-slot Σ1
graph, in order(out,a,b,c,u). Structural induction proves exact graph
interpretation for the four inputs, zero/one, addition, truncated subtraction,
Cantor pairing, actual implication coding, represented append and the
zero-safe J loader. This is finite syntax recursion, not an assumed
interpreter or internal induction on an unrepresented circuit code.

Actual NIP/DROP have no operand fields; MP has its permuted tag2; AX packs
y then x with no fourth payload. The exact model-uniform cons/NIP/discard/
terminator/leaf identities bind these expressions to accepted runtime words.
The focused leaf8 client retains u≤a. The graph check holds for every fixed
circuit and every internal input tuple. Zero-J, truncated subtraction and
actual implication coding remain explicit. No unrestricted rho8 contract,
GEN/MP circuit, proof-word history or global compiler correctness is claimed.

Main24427d6d6a643245630a7ea18bc94141ac923a0fffe6a7e3ae86f5309002f75d;
checks3e1f006d0291413d3157ef1e8f48b50bc5a589ca5cec6181b5fbdb893a572214.
Objects d83c48d8a1f602df710c7901ae95a4f213dcbc35ebecfdfce51fa7d8e2e03649
and aabd3d154b7361fd98d62e3af4a54ef937b32ee3bfa92feb236c7350f03129d4.
[Replay](arithmetic-command-circuitperm222-replay.json) SHA
a3ae9fa755656301a64322137e3be00c52780412a065ac34dd6e0f343a7aaa06;
[22-file manifest](arithmetic-command-circuitperm222-replay/FILES.json)
cd1391d70ad7dd6c516fb7ab0cf9f9a0005a9b3474bfbddf0fa59da922a088e3.

Three failed compiler invocations are retained: the initial main needed the
qualified terminatorWord namespace; the first check lacked the rho8 namespace;
opening the whole historical template namespace then made Circuit ambiguous.
The final check qualifies only rho8, preserving all other names. Main passed
after the single namespace repair and was not rebuilt for later check-only
repairs. A separate complete check-resume driver pins the successful main.
No definition, theorem statement, guard or mathematical assumption changed.
All four attempt states, five compiler commands, source snapshots, diagnostics,
timings and both drivers remain frozen. Failed reports are not accepted audits.

The private scope is124 cached custom modules,95 Foundation,409 artifacts,
38 explicit external boundaries and1130 inherited/explicit observations,
verified before/after. The accepted independent root Leaf primary is selected.
Only the new pair is fresh; no Foundation/dependency build or shared-object
change. Lean4.32 -M6000 -j1 -DElab.async=false uses regular nonsymlink outputs
and512MiB reserve at `/tmp/command-circuitperm222-root-author-0m1vhypf/lib`.
The next uniform compiler step must keep the finite circuit witness outside
all model/input quantifiers. Pointwise existence of internal words alone
will not supply the represented row function required by that step.
