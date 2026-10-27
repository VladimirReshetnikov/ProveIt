# Actual C222 uniform rho8 circuit: authenticated cache plan

26 October 2026. Read-only prerequisite authentication for root's proposed
`ArithmeticCommandRho8CircuitPerm222` and checks. No Lean invocation,
proof-source edit, dependency build, cache overlay, or Git mutation occurred.

[Plan JSON](c222-rho8-circuit-cache-plan-20261026.json) SHA
`7d62c795f6de028f4271b30bf8e0f87ddb1dc001c540b4218d88bc09da62898e`
contains exactly 126 custom modules, including 95 Foundation modules,
411 selected artifacts, and 38 explicit external import boundaries.
Every current import header and source hash was checked. All 126 modules
are reachable from the two requested imports, Circuit and Rule; the plan
records their acyclic topological order. The two parents' 124-module bases
agree on sources, imports, artifact paths and hashes. The union adds only
the two accepted primary objects, with no new Foundation dependencies.

Selected providers are the independently replayed Circuit primary
`/tmp/command-circuitperm222-controller-peer-hxn867qf/lib/DiophantineConsistency/ArithmeticCommandCircuitPerm222.olean`
(`d83c48d8a1f602df710c7901ae95a4f213dcbc35ebecfdfce51fa7d8e2e03649`)
and root's accepted Rule primary
`/tmp/arithmetic-command-ruleperm222-root-peer-q3z0_44c/lib/DiophantineConsistency/ArithmeticCommandRulePerm222.olean`
(`c03416125efb63930175222e45710fd61090ce260fa54cf11def06abbc469687`).
Original author providers and accepted replay records remain pinned;
provider replacement does not rewrite their provenance. All 2,881 repeated
observations (668 distinct path/hash pairs) passed. Existing companions
are retained; the 38 external boundaries remain explicit pinned package
or toolchain primaries, without claiming a fresh package rebuild.

The intended proof uses external finite implication expressions with four
input leaves. Syntactic `Below` has reflexivity and insertion into either
implication operand; actual `tagged_components 0` discharges its internal
numeric guard. `Uniform φ` must place one finite circuit existential before
all model/input quantifiers. Restricted row8 is witnessed by fixed leaf8;
MP is witnessed by the exact actual MP block, passing minor and major in
the order required by `mp_contract`. The generic 56-lemma
`DominatedImplication` theorem is already in this cache. Applying it then
supplies one unrestricted rho8 circuit; its literal five-slot Σ1 graph
comes from the accepted Circuit theorem. This proposed inference is not
an already proved result of cache authentication.

Future execution must use a new private overlay and regular fresh outputs,
pinned Lean4.32 with `-M6000 -j1 -DElab.async=false`, and the 512MiB reserve
before each invocation. Only the new pair is to be compiled. No internal
circuit-code recursion, represented proof history, full compiler, seed
calibration, or HA endpoint is claimed at this checkpoint.
