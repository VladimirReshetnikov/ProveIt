# Decoder reassociation: a proved source transformation and its binary obstruction

This contribution does **not** supply a correct machine with fewer than 246 states. It supplies a useful source-program reassociation theorem, exact finite source certificates, a valid state-neutral change to the inherited 246-state interpreter, and a concrete obstruction to an apparently promising 245-state rewrite.

The binary interpreter shares states between ordinary prefix-tree decoding and backward-peek contexts. A source identity and a reduction in a pure decoder DAG therefore do not, by themselves, certify the corresponding binary transition changes.

## Layout and reproduction

This directory is intended to be installed as `decoder/` beside the unchanged historical baseline at `reference/context246/`. It uses these baseline files:

- `sources/Prog254.v`, the 6,459-node physical program tree;
- `machine/zfc_prefix246_old.tm`, the exact 246-state table in upstream labels;
- `sources/prior/prefix_affine.py`, the guarded affine interpreter;
- `code/check_literal_instructions.py`, the independent literal tape painter and expected-instruction calculation.

An alternate baseline directory can be supplied through `BB246_REFERENCE`. All scripts use the Python standard library. They write only their own `rotation_candidates/` results. From the enclosing package directory:

```sh
python decoder/rotation_candidate.py
python decoder/generalized_rotations.py
python decoder/affine_macros.py
python decoder/concrete_rotation_failure.py
```

The first command reconstructs all four documented rotations, writes exact source tables and finite bisimulation certificates, and rechecks the inherited guarded affine contracts. The other commands reproduce the narrower one-step search domain, the limited affine-summary inventory, and the literal trace. Optional repair-search reproduction takes longer:

```sh
python decoder/repair_rotation.py
python decoder/repair_two_rows.py
```

The wider depth-two and neutral-walk searches are supplied separately by the enclosing research package. They have larger domains than `generalized_rotations.py` and should not be conflated with its four existing-pair rewrites.

## Source theorem

For Wade cons cells, write `A ; B` for a node with car A and cdr B. The reassociation

\[
 A;(B;C)\ \simeq\ (A;B);C
\]

preserves every finite exit relation, including register values, halt, break levels, and continue levels, provided A has no escaping break and C has no escaping continue. B is unrestricted. A may continue and C may break. Divergence is also preserved for the deterministic register language. The ordinary mathematical proof, independently audited against `RM.v`, is in `generalized_associativity.md`; it has not been compiled in a proof assistant in this session.

The static test is `break_bound(A) == 0` and `continue_bound(C) == 0`. Requiring all three components to have both bounds zero is unnecessarily restrictive. The accompanying source checker supplies an independent exact finite operation-graph bisimulation for every concrete source rewrite reported here, matching both outcomes of each decrement and every increment and halt label.

## Four concrete rewrites

All state labels below are upstream labels. Every rewrite has a 4,533-pair source bisimulation: 1,931 decrement sites, 2,601 increments, and one halt. Both decrement branches are checked. There are 6,460 unfolded leaves before and after each rewrite; maximum path length is 34 and maximum contracted control path length is four.

| Changed root | Source shape and reused pair | Working states | Guarded affine result |
| --- | --- | ---: | --- |
| 178 | `23 ; (24 ; 206)` becomes `(23 ; 24) ; 206`, reusing 16 and deleting 208 | 245 | Rejected after 1,166 passing cases |
| 190 | `105 ; (105 ; 114)` becomes `(105 ; 105) ; 114`, reusing 179 | 246 | Rejected after 2,651 passing cases |
| 219 | `206 ; (23 ; 208)` becomes `(206 ; 23) ; 208`, reusing 205 | 246 | Rejected after 5,655 passing cases |
| 226 | `(190 ; 213) ; 231` becomes `190 ; (213 ; 231)`, reusing 207 | 246 | All 8,391 cases pass; 2,912,625 symbolic rules |

The unchanged baseline passes all 8,391 cases with 2,911,962 symbolic rules. An affine PASS denotes the family covered by the supplied symbolic rules and inherited macro contracts, rather than a finite sample of register values. The overall proof-assistant and native-theory status remains that of the enclosing report and baseline; these results do not independently establish the requested ZFC equivalence.

`rotation226.tm` is a state-neutral candidate supported by the source bisimulation and the full inherited binary bridge check. The enclosing package also supplies its unchanged blank initializer replay. The other three `.tm` files are explicitly rejected experiments, not proposed small ZFC machines.

The reconstruction uses all source occurrences having the relevant exact recursive fingerprint. For root178 this is nine occurrences, at nodes 363, 1400, 1995, 2710, 2977, 4313, 4364, 4416, and 4879. A map following only preserving right-moving binary edges initially misses node4364. Adding that ninth occurrence is necessary for consistent source reconstruction, but does not repair the binary obstruction.

## Why deletion208 fails

The proposed saving changes only root178's two rows and deletes the now-unreferenced state208:

```text
178 0 0 R 16
178 1 1 R 206
```

On a pure source-tree path these rows implement the stated reassociation exactly. However, state178 is also borrowed by another decoder context. One affected path is:

```text
237/read0 -> 218/read0 -> left to154/read0 -> right to178/read0
```

The original last step goes right to23; the rotated last step instead goes right to16. State218 is interpreting a different source subtree there, whose car is routine23. It does not represent the whole routine178 tree. This hidden use explains why replacing every complete source occurrence of routine178 cannot fix the binary table.

The first guarded affine rejection is source-site index894, path `11101001001010100111000000`, `EDecnz 1`, with logical register1 zero. Logical register1 is physical register2. The rejected macro attempt reaches state95 marking physical register0, so the required guard does not justify it. This is a precise contract failure, not a proof about the machine's halting language.

The companion literal fixture strengthens the evidence without relying on the affine oracle. Its input is state96, head0, header distance40, this same PC, physical registers `[1,0,0,0,0,0,0,0,0]`, and spare list `[1]`. The source zero branch requires next PC `1110100100101010011100001`, with unchanged registers and head. The baseline reaches that exact tape after 380 transitions. The rotated table reaches a different ordinary encoded dispatcher tape after 378 transitions: its PC is `11101001001010100111000001`, with the same registers, header, and head. The changed successor one is at tape coordinate 25 instead of 24.

Both traces pass through two earlier transient visits to state96. The fixture explicitly records them; it does not incorrectly treat the first state96 visit as an instruction boundary. Exact initial and returned one-position sets are in `rotation178_literal_counterexample.json`. This is a finite local-bridge discrepancy, not a blank-run counterexample and not a counterexample to a halting-language equivalence.

## Repair searches and limits

Each enumerated replacement action consists of either write bit, either head direction, and any of the 245 surviving working targets or halt: `2 * 2 * 246 = 984` actions.

The single-row repair search changes one additional transition in the failed245 table:

| Additional entry | Actions tried | Survive the first failed guard | Survive all 8,391 contracts |
| --- | ---: | ---: | ---: |
| 218/0 | 984 | 16 | 0 |
| 237/0 | 984 | 28 | 0 |
| 154/0 | 984 | 27 | 0 |
| 154/1 | 984 | 0 | 0 |
| 231/0 | 984 | 34 | 0 |
| 23/0 | 984 | 7 | 0 |

The total is 5,904 recipes. The surviving first-gate actions receive the full checker, which stops at their first remaining failed contract.

A second targeted family fixes `218/0 = 0 L 245` and varies one of `245/1`, `243/1`, `244/0`, `187/1`, or `220/1`, for 4,920 recipes. Two fixed guards are used before the full check. Their respective gate-survivor counts are 12, 15, 15, 0, 15; none passes all contracts. The best variants pass 3,856 contracts before a later contextual collision. For example, directly replacing `244/0` by `0 R 105` repairs the immediate backward-peek path but breaks another genuine use of244's original car.

These are exhaustive results only for the explicitly stated finite recipe families. A rejection caused by symbolic fuel or unavailable box justification is recorded as a checker rejection, not asserted to be an independent mathematical impossibility theorem.

## Affine commutation probe

`affine_macros.py` recognizes a deliberately limited class of source subtrees: fixed increments and exits, sequential affine composition, and terminating transfer loops with a fixed additive body. It obtains 24 normally returning affine summaries. Among existing pure decoder nodes whose two children both have recognized normal summaries, the only commuting pair is state200's two identical children114. It therefore produces no nontrivial sibling swap in this domain. The recognizer is not complete, and this result excludes neither richer arithmetic identities nor re-encoding of mixed decoder states.

The source reassociation theorem and the mixed-context obstruction point toward a more suitable optimization problem: a decoder state should carry all its tape and entry contexts as obligations. Pure-tree hash sharing discards information that the existing binary machine uses. Any future synthesis step must preserve these contextual obligations while changing the source paths and decoder table together.

## Attribution

The baseline and physical source are from ProveIt, the upstream `jeff87654/busy-beaver` repository, and their attributed contributors; full upstream notices and licenses are retained in `reference/context246/`. The exact mathematical and machine provenance is described by that baseline and the enclosing report.

`rebracket_axioms.py` is an unchanged copy of ProveIt's existing source helper, used here for `bounder`, `PathMachine`, and `bisimulation`. Its original path is `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-rebracket_axioms.py`. Its unrelated generic-backend command-line experiment is not part of the decoder experiment in this directory.

The new scripts in this directory adapt the baseline's strict affine and literal-instruction interfaces. Their results depend on those explicitly retained artifacts. `PROVENANCE.json` records source and artifact hashes; `SHA256SUMS` covers this contribution's files.
