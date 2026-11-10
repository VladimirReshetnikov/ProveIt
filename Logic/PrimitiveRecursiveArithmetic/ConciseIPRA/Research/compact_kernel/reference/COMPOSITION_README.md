# Composed arity and predecessor checker for iPRA

This is a reproducible constructive checkpoint combining mechanisms already present in the current drafts. It does not claim a new arithmetic foundation, an absolute minimum, or the requested significant breakthrough.

The recommended complete checker has **612 normalized bytes, 266 significant Python tokens, 310 AST nodes**, and **360 bytes under ordinary gzip level 9**. It uses an ordinary explicit list test and includes the JSON input and verdict driver. Against the current complete-program coordinate minima **616 / 268 / 300**, it improves the byte and token coordinates and does not improve AST count. The minima are attained upper bounds on an unknown optimum.

| Delivered complete program | Tokens | AST | Normalized bytes | Raw bytes | Gzip-9 raw |
|---|---:|---:|---:|---:|---:|
| `code/checker.py` | 266 | 310 | 612 | 612 | 360 |
| `ancillary/checker_bytes.py` | 267 | 315 | 597 | 597 | 356 |
| `ancillary/checker_ast.py` | 267 | 298 | 639 | 639 | 360 |
| `ancillary/checker_ast_loop.py` | 266 | 296 | 689 | 689 | 369 |

The AST profiles inherit exception-based iteration and malformed-string rejection through CPython's finite recursion limit. They are auxiliary comparisons. The main checker has explicit list dispatch.

## What was combined

- The arity draft's exact sorted codec: equality `[s,t]`, paired binder `[B]`, and conditional closure `[B,B,B]`; numerical base depth three; recursive depth increment `5-len(node)`.
- The uniform-predecessor draft's arithmetic instruction `[null,p,a,h]`, with depth-three recursive-image opening.
- The existing ordinary exit-status rejection convention.

The main program is the original strict arity checker with those two interface adaptations. The arithmetic packet correspondence is exact: a new truthy-predecessor packet maps to old `[[],[p,a,h],1,0]`, and a falsy one maps to `[[],[0,a,h],p,0]`. The empty-array old marker is essential: it preserves zero opening in the common continuation. The generated raw equation and its scope checks coincide.

Literal-zero DI witnesses now work directly. Successor computation at a literal-zero predecessor uses the inherited box `B(p)=I(0,p;v.0)=p`, followed by equality transport. Every canonical native derivation is still representable. Thus the inherited full iPRA bi-interpretation applies to exactly the same native calculus; the theory is not being strengthened with an unproved supply principle.

## Files

- `code/checker.py`: recommended complete checker.
- `code/readable_checker.py`: explanatory, separately executable equivalent.
- `theory/composition.tex`: full codec/composition soundness and completeness writeup, including exact packet translation, zero-instance supply, fresh labels, zero witnesses, and boxing.
- `ancillary/`: smaller-byte and smaller-AST profiles, with exact compressed source files.
- `tests/producer.py`: untrusted named proof producer; never imported by a checker.
- `tests/cases.json`, `tests/fixtures/`: regenerated canonical positive and adversarial proof packets.
- `tests/verify.py`: standalone complete-program, malformed-input, and guard-control validation.
- `measure.py`: unchanged corpus measurement convention, including gzip-9 FYI values.
- `tools/rebuild_producer.py`: independently recreates the documented producer adaptation from frozen source files.
- `reference/`: unchanged comparison checkers, original producers, and upstream license.
- `evidence/`: exact measurements, source provenance, validation receipt, and written scope.

## Run

```sh
python3 code/checker.py < tests/fixtures/I0_arbitrary_seed.json
python3 code/checker.py < tests/fixtures/contextual_induction_seed_congruence.json
python3 code/checker.py < tests/fixtures/canonical_false.json
```

The first two accept. The third rejects with nonzero exit status. A traceback is diagnostic. Acceptance means both exit status zero and the exact line `ACCEPT`.

Reproduce the delivered finite evidence with:

```sh
python3 tests/verify.py
```

The full suite uses only Python's standard library. Exact normalized-source measurements use CPython 3.12.14 and zlib 1.3.2. `python3 measure.py` remeasures sources; runtime differences can change normalization or gzip bytes.

## Trust and provenance

The repository comparison is pinned to ProveIt commit `fb2dbd2a33c6b132671a54b029d0bf3cd98c633d`. `evidence/provenance.json` records exact source paths and hashes. The arity and uniform-predecessor mechanisms are inherited and explicitly attributed. The producer is formed from the uniform-predecessor producer by replacing the numerical and formula codec methods with those from the arity producer and changing the exposed endpoint-template coordinate from one to three.

These are written proofs and finite executable checks, not proof-assistant formalizations. Large finite proofs can exceed a physical interpreter's resource limits. The primary raw-array traversal is structurally terminating subject to ordinary finite-resource execution; the ancillary exception opener has the additional malformed-string qualification stated above.
