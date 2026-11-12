# Current iPRA draft audit

Pinned repository: VladimirReshetnikov/ProveIt, commit `76a2651601d17b34d46753f189ea026a21ce8d29`, `docs/drafts`, inspected 2026-11-10.

## Actual benchmark

All 17 direct archives were inspected through the parent's hash-verified downloads. A fresh static recursive census found 32 distinct ZIP payloads, 2,239 Python occurrences after deduplicating ZIP payloads, and 443 distinct Python byte strings. The recursive census found no additional Python content absent from the parent's extracted text corpus. No archived program was executed for this audit. Parsing, normalization, tokenization and gzip measurement were performed by an independent short script. Full exact paths and hashes are in `analysis/full_corpus_metrics.json`; direct extraction occurrences are in `analysis/python_metrics.json`.

The benchmark is an observed achievable upper bound on unknown optimal complexity, never a mathematical lower bound. The current empirical coordinate envelope, attained by different programs, is **558 normalized bytes / 262 significant tokens / 296 AST nodes**.

| Program, relative to its archive root | Bytes | Tokens | AST | gzip-9 raw |
|---|---:|---:|---:|---:|
| certified_zero/code/checker_bytes.py | 558 | 264 | 310 | 345 |
| certified_zero/code/checker.py (explicit list test) | 566 | 264 | 308 | 351 |
| certified_zero/code/checker_joint.py | 598 | 262 | 296 | 350 |
| affine_supply/code/checker.py | 597 | 275 | 316 | 356 |
| affine_supply/code/checker_tokens.py | 691 | 263 | 301 | 371 |
| affine_supply/code/checker_ast.py | 689 | 266 | 296 | 369 |
| checker_and_barriers/implementation/checker_short.py | 593 | 267 | 315 | 355 |
| compact_kernel/ancillary/checker_bytes.py | 597 | 267 | 315 | 356 |

The first three files are at
`reference/extracted/ipra_certified_zero_2026-11-10/ipra_certified_zero_2026-11-10/code/`.

The selected byte leader's SHA-256 is `5520fce8cf011fb3b91f6d9936d12f53aa73908f8aa139dec06a7d1a609fd8ea` (use JSON metrics as authoritative if copying; exact full hash is recorded there). The full filename conventions include the `_2026-11-10` suffix in each archive/root.

All programs charge their complete module, including JSON input, opening/validation, inferences, freshness and success verdict. The shared platform excluded is Python plus standard JSON. Producers, normalizers, proof translations, test harnesses and mathematical appendix scripts are not imported by the small kernels. Thus a helper that just calls another checker is not a competing small kernel. The boundary scan found no overlooked complete checker below these figures; smaller files are builders, manifest scripts, tests, corpus scripts or wrappers.

## Qualification of the benchmark

`checker_joint.py` and the 296-node affine-supply loop profile use exception-based generic iteration. A nonempty string can recurse without bound in an ideal unlimited-stack semantics. Actual CPython's finite recursion limit causes eventual rejection. The reports explicitly disclose this; these profiles are fixed-runtime competitors, not structurally terminating validators of all finite JSON under an ideal unlimited stack. The byte and explicit-list profiles avoid that qualification. Ordinary physical resource limits on large valid inputs apply separately to every profile.

The 558-byte source uses the exact-built-in-JSON predicate `a * 0 == []` to distinguish lists. This is not a general predicate on arbitrary Python objects, but certificates are parsed JSON and cannot provide hooks or subclasses. Its replacement by `isinstance(a,list)` yields the 566-byte recommended source. Boolean and floating JSON aliases, raw large arity constants, and generated fresh assumptions are explicitly addressed in the checker report. The crucial claim is soundness of every successful finite trace under the stated decoder; canonical proof completeness is a separate assertion.

Written bridges claim full first-order intuitionistic PRA, whole numerical domain, actual equality, and identity numerical return maps. Their numerical grammar has zero, successor and a scalar initialized iterator binding one state variable. Equality-only induction is expanded via internally available Boolean functions; a pairing compiler reconstructs every fixed primitive-recursive description. Logical Eq/Q/D rules are reconstructed with formula round trips. None of the newest reports claims Lean/Rocq verification of the universal soundness or bi-interpretation theorem. This audit found no immediate contradiction in the inspected kernel proof, but did not independently reprove all inherited arithmetic appendices.

## Prior ideas that must not be presented as novel

| Direct draft | Prior contribution / limitation |
|---|---|
| adaptive_seed | Adaptive finite update queries and finite-dimensional quotient unit obstruction for almost-unary bounds; no new positive checker. |
| affine_arity | One affine depth traversal, extra zero slot under equality, existing contradiction decoding for large arities; 648-byte checker. |
| affine_supply | Composition of affine scopes, predecessor packets and immutable-context loops; 597-byte checker; no new arithmetic basis. |
| arity_calculus | Unary D, triplicated Q, depth increment `5-len(node)`, conservative surplus-arity decoder; distinct source profiles. |
| bounded_initializer | Tied-seed B plus actual-equality Boolean epsilon, bounded initialization with cap coherence and quantified-free graph compiler; no small checker for this NEW arithmetic theory. Its small programs use the OLD initialized-I arithmetic. |
| certified_zero | Truthiness of initializer chooses computation; no null opcode. Closed nonempty `C=I(2,1;v.0)=0` repairs excluded literal-zero initializers and zero successor predecessors simultaneously by three native inference nodes. Shared continuation hypothesis construction. Eager initialization has a two-element model even with coverage and full induction. |
| checker_and_barriers | Composition of arity codec and predecessor protocol, progressive-binder Boolean-case product obstruction, exact zero profiles for positive iteration. |
| compact_kernel | Smaller combination of existing protocols; eventually constant powers with conjunctive quantifier induction and automorphism obstruction to finite-dimensional ordinary bi-interpretation. |
| constructed_computation | Construct successor sources from a supplied predecessor; validate recursive image when state is used. Finite-range obstruction to restricting witnesses and Q targets. |
| counter_congruence | Root replacement plus congruence only in recursor counter derives numerical congruence; zero-seeded monotonicity; initializer-free almost-unary bounds; naive swapped-E logical composite fails. Direct new theory checker is much larger. |
| flat_computation | Flatten constructed computation packets, with explicit boxing translation and uniform supply. |
| local_scopes | Lexical eigenparameter renaming; finite-profile and existential-free witness-extraction obstruction to ordinary finite-dimensional relational bi-interpretation of tied-seed systems; selector completion. |
| research | Immutable-context loop and byte profiles; progressive H alternative still needs Boolean cases; eventual-sequence obstruction for finitary expansions. |
| scalar_successor | Successor-seeded scalar recursor bootstraps predecessor and ordinary initialization; new arithmetic proof, modest separate checker profiles. |
| successor_seed_completion | Completes existing successor-seeded candidate by shifted affine alignment, capped predecessor, three-value correction; full predecessor has no native certificate. |
| transient_seed | One-state successor-seeded recursor: transient initialization, reset-cycle predecessor, finite Boolean bootstrap, direct native SR certificates; ordinary I is recovered. |
| uniform_predecessor | Direct scalar predecessor packets and shorter certificates; rejection-driver matching removes most apparent code reduction. Stronger one-body initializer-fusion almost-unary obstruction. |

## Essential correctness constraints already exposed by the drafts

1. Major premise verification cannot be dropped or made into a fallback no-op on failure.
2. Induction/progress must retain its literal-equation restriction; permitting arbitrary compounds is stronger than iPRA.
3. Freshness/negative parameter allocation and context immutability are essential. The old mutation suites explicitly turn a shared mutable context into a false `0=1` certificate.
4. Introductions must check the unary paired shape; otherwise arbitrary equalities may be treated as formulas suitable for introduction.
5. A generated computation assumption need not be uniformly true at its newly allocated parameter. Soundness uses its derivable zero instance plus fresh-name discharge. For example a packet can supply `I(0,0;v.0)=b`, whose instance at b=1 is false, yet whose independent conclusion is harmless because b was fresh. Therefore treating generated hypotheses as universally true is an invalid proof argument even when the implementation itself is sound.
6. Any reduction to zero-only initializers or a common syntax representation needs a separate completeness proof; simultaneous boxing of all numerical substitutions is already a rejected incomplete experiment.
7. Term definability obstructions alone do not rule out relational or quotient interpretations. Later reports explicitly strengthen several obstructions and state the residual scope carefully.

## Recommendation

Use the 558-byte certified-zero source as the empirical byte target and the 566-byte explicit version as the transparent target. State separately whether a new implementation beats 262 tokens and 296 AST nodes; never combine minima attained by different programs into a fictitious single implementation. A further syntactic improvement is not, by itself, the requested significant new axiomatization. A credible foundational advance must isolate a new arithmetic or logical construction and prove both return interpretations, including formula composites; representation and driver savings should be itemized separately.
