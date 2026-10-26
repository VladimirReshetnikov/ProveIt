# Circuit-proof simplification review

Pinned repository commit: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
All line references below are to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/` at that commit. This review and its candidates do **not** modify the snapshot. No Lean executable was available and no software was installed. Every supplied Lean candidate is explicitly **uncompiled**.

## Main conclusion

The useful architectural change is **move generated instances onto infrastructure already present**, not “write the first generic DAG soundness theorem.” The repository already has:

* `ArithmeticDAGSemantics.run_node_equation`, lines 58–94;
* `run_eq_of_node_equations`, lines 97–109, and `value_eq_of_node_equations`, lines 111–116;
* `ArithmeticDAGPowers.run_power`, lines 24–42, and `value_eq_of_powerRewrite`, lines 86–131;
* `ArithmeticDAGDegree.DegreeCertificate`, lines 21–23, and `value_degree_le` / `polynomial_degree_le`, lines 65–90.

The first soundness theorem already supplies each generated gate lemma. Thus its large wrapper family is API/source overhead, not hundreds of independently invented mathematical arguments. The power checker, however, is a real reuse opportunity: `SplitCircuitSteps59` and `GapCircuitSteps66` still generate an individual `ring` proof per pure-power register.

## Measured source census

Counts include blank lines in each declaration's span, ending before the next declaration or namespace `end`. They are source measurements, not proof-term sizes or elaboration timings.

| Module | Total lines | UTF-8 bytes | Gate wrappers | Gate span | Power lemmas | Power span |
|---|---:|---:|---:|---|---:|---|
| `SplitCircuitSteps59` | 3,445 | 169,808 | 515 | L16–2590; 2,575 lines | 107 | L2591–3444; 854 lines |
| `GapCircuitSteps66` | 3,122 | 153,802 | 484 | L16–2435; 2,420 lines | 86 | L2436–3121; 686 lines |

There are 999 gate wrappers and 193 power lemmas, totalling 1,192 public theorem declarations. The gate and power spans together cover 6,535 of these files' 6,567 lines. Removing them is **not** automatically an attainable source reduction: consumers currently refer to their names.

The generator `analyze_circuits.py` extracts the natural circuit lists and the exponent claims from the actual Lean text. It checks list length, input/fixed-leaf bounds, strictly earlier references, and every nonzero exponent transition. It records SHA-256 source hashes. It also mutates an exponent and inserts a forward/non-earlier edge; both negative cases are rejected for both circuits. These are independent Python consistency tests, **not Lean proofs**.

## Proposal C1: consolidate power proofs, preserve the public API

For each circuit, create one finite natural-exponent certificate and call existing `run_power`. The base register is 36 for Split and 20 for Gap. Label zero means “not certified as a power”; it does **not** mean exponent zero. The base has label one. Non-base positive labels must be multiplication nodes whose operand labels are positive and add to the result label. The existing theorem uses topology to justify induction over register number and proves the result over every `CommRing`, not just integers.

The complete candidate files are under `api_preserving_candidates/DiophantineConsistency/`. They keep every original public gate/power theorem header text unchanged and retain the original literal DAG import. Only the power bodies change, with private label data and shared lemmas added. The Python check compares all 1,192 public theorem headers byte-for-byte.

| Candidate | Source lines before → after | UTF-8 bytes before → after | Per-power `ring` calls |
|---|---:|---:|---:|
| Split | 3,445 → 3,074 | 169,808 → 171,042 | 107 → 0 |
| Gap | 3,122 → 2,833 | 153,802 → 154,928 | 86 → 0 |

This deliberately conservative experiment saves **660 source lines but adds 2,360 bytes**, including its warning and axiom-audit commands. Therefore it demonstrates less tactic repetition, not byte compression or speedup. Much line saving is removal of proof-body layout. Retaining all names places a floor on source size. A finite `decide +kernel` check may cost more than the old local proofs; benchmark before adopting.

The Split label table extracted here is **exactly equal as a list of integers** to existing `SplitJointPower59.natural_oldLabelsData` at line 64. Its existing private `natural_old_steps` is lines 76–78. For production, extract this data and its certificate into a shared small module used by both Steps and JointPower. Do not copy the same certificate twice, and do not import the joint child circuit merely to access a parent label table. This is stronger evidence of feasibility than inventing a new data format, but it is still not a compilation result for these candidates.

## Proposal C2: indexed facade and deliberate compatibility boundary

`SplitCircuitCandidate59.lean` (94 lines, 4,098 bytes) and `GapCircuitCandidate66.lean` (92 lines, 3,958 bytes) expose:

1. The same list evaluator as a register function.
2. One `natural_step (i : Fin nodeCount)` theorem using existing `run_node_equation`.
3. One checked label table and one `natural_power` theorem using existing `run_power`.
4. Concrete examples for input register zero and the final original power claim, plus axiom-print commands.

These **are not drop-in replacements**. Their namespaces differ deliberately, and existing named gate/power lemmas are absent. Their small source size is not a measured project-wide reduction. Call-site rewriting, readable named boundary facts, conversion costs, and the certificate runtime are all outstanding.

First migrate one client theorem, such as `GapCircuitRegisters66.natural_baseRegister` (L18–22), before replacing a whole generator. Prove that concrete indexed instances rewrite as expected without unfolding the whole run. Preserve named boundaries such as `natural_kernel0Register`, `natural_sourceHighRegister`, and `natural_sourceRankRegister` rather than exposing numeric gate indices everywhere. These semantic names are useful API, unlike hundreds of mechanical wrappers.

Direct importers of Split Steps are Registers59 and Translation59; direct importers of Gap Steps are Degree66, Tail66, Translation66, and Registers66. The recipes import Registers transitively, so rebuilding direct importers alone is insufficient. In particular, `GapCircuitRegisters66` L30–40 contains long, carefully bounded simplifier lists. Replacing them with `simp [all definitions]` risks exponential expansion of shared DAG expressions. Keep cuts at powers and previously proved named registers, as the current files already do.

## Proposal C3: compositional certificates, not global normalization

The project already does compositional reasoning well: Gap Registers L18–94 proves 13 named register facts, and Gap Recipe L15–211 combines them with local algebra. The Split counterparts do the same. Generalize these boundaries only where the repeated structure is real.

A useful next layer would describe a polynomial kernel block by its input/base register, sparse coefficient/exponent data, and output register, then certify that block with a local symbolic-value table and `value_eq_of_node_equations`. This can shorten the very long literal `simp only` lists in kernel register proofs. It must additionally prove correspondence between the certified block's output and the existing full-DAG register; certifying a newly generated equivalent-looking block alone is not enough. A bounded register interval or a subgraph plus explicit embedding is suitable. Keep the independently transcribed high-level recipe as the specification—do not define the specification to be the same generated DAG and call reflexivity a verification.

`SplitJointPower59` is an existing example of this certificate philosophy, not a new proposal: checked node relations and a power-label correspondence prove equality of distinct literal circuits. The exact 515-node natural Split parent and 498-node joint child are intentionally different objects; do not conflate their counts or replace one merely to shorten a proof.

## Proposal C4: reuse the degree checker for ShortSystem

`ShortSystem.lean` is 1,117 lines / 49,527 bytes. The generated P77 degree section is L565–842 (96 `let` bindings and 96 local `have`s); P75 is L844–1115 (94 each). The two generated proof bodies share an exact 224-line prefix beginning at their first local binding. Their public results remain degree **at most 68**, not degree exactly 68.

Use the existing `ArithmeticDAGDegree` checker for a common literal prefix and two residual/output tails, or first package the shared intermediate degree facts in a record. The graph design must prove equality to `literalValue` / `compactLiteralValue`, and then use the existing bridges to `value` / `compactValue` (L348–360 and L487–499). Adding a fresh DAG without that bridge does not shorten a proof of the original theorem.

An incremental alternative is a common “core degree bounds” lemma with just the boundary fields consumed by the two tails. It has less representation risk than translating the whole literal program. Do not weaken the ≤68 result merely because a syntactic checker produces a larger bound. `GapCircuitDegree66` explicitly warns at L63 that its naive degree bound is weaker than the cancellation-aware finalizer bound; the same limitation matters here.

## Proposal C5: typed view only after the low-risk reuse

`ArithmeticDAG.Node` uses `Fin` for input/fixed indices but `Nat` for operand registers (L11–18). Invalid register lookup currently returns zero (L79–81), while a separate topology certificate excludes invalid edges in well-formed circuits (L105–112).

One optional representation is `SafeNode inputs fixed earlier` with binary operands in `Fin earlier`, and a dependent vector `node : (i : Fin size) → SafeNode inputs fixed i.val`. An easier first step is a checked circuit wrapper bundling the existing literal list, its `Topological` proof, and an output `Fin nodes.length`. Both remove repeated bound plumbing from client APIs.

Retain the raw literal list and prove that erasing the typed view returns **exactly** that list in its original order. Then reuse existing semantics, operation counts, liveness, and pinned-data audits through that equality. A typed graph does not verify the Python importer or establish specification equivalence by itself. It may enlarge elaborated terms and add dependent equality overhead; no performance benefit is established here. This is lower priority than reusing `run_power`.

## Preservation and validation checklist

* Preserve universal `CommRing` statements, input dimensions (9), fixed-leaf dimensions (12 Split / 11 Gap), the base indices (36 / 20), output indices (514 / 483), and exact old theorem headers for the compatibility experiment.
* Preserve the literal DAG, leaf interpretation, topology, liveness, edge direction, operation-count definition, and zero-default total semantics. Original natural operation counts are 480 for Split (`SplitCircuit59` L1246) and 450 for Gap (`GapCircuit66` L1186); these proposals do not improve those counts.
* Keep generator/data hashes and independently specified recipe links. Modify generators as the source of truth rather than hand-editing generated modules only.
* Use kernel-checkable finite certificates, following the pinned source's `decide +kernel` convention. Do not substitute `native_decide` merely to make a timing number look better.
* Compile in the pinned project toolchain, build affected import closure and umbrella targets, compare exported theorem types, and compare `#print axioms` results against baseline. The Python header check is not an elaborated theorem-type comparison.
* Record wall-clock elaboration, peak memory, generated `.olean` sizes, source bytes, and proof checking separately. Run at least cold and warm builds. No such measurements were performed here.
* If a 484/515-node finite check exhausts resources, split the certificate into checked chunks and prove a generic coverage/composition lemma. Do not respond by raising limits indefinitely or weakening trust.
* Test the compact indexed facade on real `simp only` consumers: definitional reduction of `List.getD` at a numeral and elaboration of `Fin` proofs may be significant costs.

## Reproduction

From the report bundle root containing `sources/` and `circuits/`, run:

```sh
python circuits/analyze_circuits.py
```

The script writes JSON/CSV metrics, exponent-label tables, the compact candidate facades, and full API-preserving candidate modules. It never writes the input snapshot. Do not run Python with `-O`: checks deliberately use assertions. Lean candidates require a separate compilation in the already configured pinned repository; they are not endorsed replacements until that succeeds.

Source URL base: <https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/>.
