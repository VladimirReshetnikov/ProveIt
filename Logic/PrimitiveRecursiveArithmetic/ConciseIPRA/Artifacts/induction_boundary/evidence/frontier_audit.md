# Frontier audit at 798856e4ef2d02b7f9c0f1660828c5ce58f277f2

## Findings

The README package table is not the current coordinate frontier. The current article and five current incoming archives include newer checkers. The complete-module metric is CPython 3.12.14, `ast.unparse(ast.parse(source)) + '\n'`, significant Python tokens, all AST nodes, and normalized UTF-8 bytes.

The incoming scan measured 94 `.py` or `.py.gz` members. The complete record is `incoming_metrics.json`. This is a source census, not an independent proof of every checker. Build scripts and deliberately rejected experiments must not be mistaken for complete proof checkers.

| Contract | Tokens | AST | Bytes | Comment |
| --- | ---: | ---: | ---: | --- |
| Unshifted promised guarded syntax, JSONL | 239 | 256 | 549 | Different programs; byte coordinate is stream token profile |
| Unshifted promised guarded syntax, whole JSON | 244 | 261 | 465 | Different programs |
| Shifted promised guarded syntax, whole JSON | 267 | 298 | 461 | One actual program |
| Strict zero-alias native Eq/D, whole JSON | 317 | 356 | 597 | Different programs from latest validated-arity package |

The cross-contract compact coordinate envelope is **239 / 256 / 461**. This is not one program and not one unchanged input contract. The article explicitly distinguishes unshifted R/U, shifted R+2/U, whole JSON and streaming contracts. No universal lower bound is established: these attained sizes are upper bounds on the unknown optimum.

## Exact compact controls

All three are present in the current `docs/incoming/ipra_coverage_constancy_2026-11-13.zip`, under its top-level directory's `controls/`.

* `stream_tokens239.py`: 239 / 261 / 549, SHA256 `a6e71832fd2a7aed50714117defe7fbd6af3b958fa72ac9d38847a4d62ca434b`.
* `stream_ast256.py`: 245 / 256 / 580, SHA256 `261ee0f075092ae2bef33016282d7af0cfef743a3dd905472d6b0d4049fdd8cb`.
* `shifted_bytes461.py`: 267 / 298 / 461, SHA256 `e587d311a76e7b1ac9a292883ff57a139ad7ddf8dceff8d39d489a033f29525e`.

Their older origins are recorded in that package's `evidence/source_snapshot.json`: the first two came from `ipra_fused_blocks_and_checkers.zip`; the last from `ipra_prefix_conditional_2026-11-12.zip`. In the current article, they are respectively L_f, L'_f,m and T^rho_+,p in the certificates chapter.

## Exact strict controls

The current `docs/incoming/ipra_validated_arity_refinement_2026-11-13.zip` has `code/checker_strict_tokens317.py`, `code/checker_strict_ast356.py`, and `code/checker_strict597.py`. Its prior frontier 319 / 358 / 599 is superseded by **317 / 356 / 597**. This package proves acceptance preservation for a changed arity predicate, and explicitly does not claim a new axiom basis or a compact-frontier improvement.

## Contract and soundness cautions

1. Compact checkers assume exact integer/list data and a canonical closed guarded public Eq/D goal; they do not independently validate the public grammar. The strict programs check the entire alphabet and public native goal grammar. Calling a 461-byte module a fully input-validated native checker would be false.
2. Token/AST minima use return-reservation of fresh parameters with a global floor, whereas the byte minimum uses a local floor and a shifted sorted-arity codec. Certificates are not interchangeable without a translator.
3. Merely deleting the initial neutral context from `c([0], *q())` to obtain `c(*q())` makes the root context certificate-supplied. It is defensible only as a different checker of explicit sequents, not as an acceptance-preserving closed-theorem improvement; do not claim it as an honest like-for-like record.
4. Computing the freshness floor from packets consumed is known to be unsafe. The coverage-obstruction package includes an explicitly rejected unsound experiment. A locally derived floor must still validate an introduction witness before making its eigenparameter available.
5. Exact syntactic scope is needed when the substitution procedure recursively checks its supplied image. A strict local bound k < atom < depth excludes the freshly inserted k as well unless allocation or image checking is changed.

## Search outcome

Safe local AST rewrites inspected here have not produced a new global compact minimum. Changing `any((m, 3 % len(a)))` to `bool(m or 3 % len(a))` in the byte program lowers tokens to 265 but raises bytes to 462 and retains 298 AST nodes. Moving the major-selector disjunction to a conditional lowers AST locally to 295 but raises bytes to 462. These are not below the existing envelope.

The exact lower-envelope claim should therefore remain conditional on a genuinely new construction, and must not be inferred from a smaller matched control alone.
