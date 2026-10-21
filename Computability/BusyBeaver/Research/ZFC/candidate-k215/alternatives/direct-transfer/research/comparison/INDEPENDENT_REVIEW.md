# Independent review: final ST215 physical artifacts

**Result:** the exact final native table with SHA-256
`d5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1`
passes the finite source/table, graph novelty, and saved runtime metadata audits
in this folder. The portable rerun requires only Python's standard library.

The table contains 215 working states, both transitions for every state, start
state 0 and halt target 254. Every working state is reachable in the abstract
transition graph. Its 4,732-leaf source has 201 distinct subtree nodes, depth 44,
and maximum zero run 6. Independent reconstruction preserves the entire ordered
primitive sequence and all 6,150 primitive control-flow edges of the proposed
context-root short-transfer source. Every one of the 4,731 internal source
prefixes traverses the actual dispatcher table without modification.

The final rooted labeled transition graph differs, even under global tape
reflection, from all 78 distinct complete 215-state tables found under 332
original names in the specified incoming archives and pinned repository.
Restoring only the append-one write also leaves zero graph matches. Inert byte
copies and full provenance are included, so the comparison does not depend on
network access or executing archive code.

The independently checked saved runtime inventory contains all 6,151 guarded
cases, covers all 430 transition rows, and accounts consistently for 1,617,630
symbolic rules. Every duration summary has nonnegative coefficients and a
positive constant; every nonhalting displacement matches its control-flow
overflow. The four block-certificate traces use actual transitions and have
the required duration and motion sums.

These checks substantiate a materially different physical realization of the
previously proposed 35-leaf direct transfer, whose command guard differs from
the old 78-leaf composite. They do not independently establish its logical
calibration. In particular, case execution traces were not retained in the
runtime inventory; metadata checks are not a replay of the universal runtime
derivations. The main packet's symbolic runtime proof and consistency
calibration remain separate review obligations. No 214-state machine is claimed,
and no bounded simulation is used as evidence for nonhalting.
