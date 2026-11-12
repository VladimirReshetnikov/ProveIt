# iPRA with computation in term syntax

Prepared for Vladimir Reshetnikov, November 11, 2026.

Read **report.pdf** for the full mathematical construction. **report.tex**
is a standalone LaTeX source, including the attributed arithmetic foundations
and the entire selected checker.

## Result

Use full normal forms for both scalar iterator computations:

    I(0,a;u.h)  -> a
    I(Sn,a;u.h) -> h[I(n,a;u.h)/u]

The complete calculus has six patterns: Hyp, Refl, Tr, QE, DE, and one
witness-selected introduction. It has no separate computation-equation axiom.
All normalization code is included in the measured kernel.

The new compound-envelope lemma repairs case introduction when normalization
turns a witness into literal zero. The paper proves strong normalization,
confluence, capture-safe substitution coherence, exact consequence equivalence,
both formula composites, and whole-domain bi-interpretability and
equiconsistency with full first-order iPRA. Equality remains actual equality,
and both numerical composite isomorphisms have graph x=y.

## Exact complexity result

Complete modules under CPython 3.12.14, normalized with ast.unparse plus one LF:

| Checker | Bytes | Significant tokens | AST nodes | Gzip-9 |
|---|---:|---:|---:|---:|
| Matched raw control | 2569 | 895 | 930 | 941 |
| Matched zero-only control | 2532 | 890 | 930 | 945 |
| Full normalization, block form | 2546 | 904 | 962 | 960 |
| Full normalization, expression form | **2529** | 908 | 965 | 963 |

The selected expression-form program is 3 bytes smaller than the closest
matched control, but has more tokens, AST nodes, and gzip bytes.
The separate 516-byte compact arity codec in the repository remains smaller.
No global minimum or coordinatewise improvement is claimed.

The 3100-byte forward implementation is also supplied: it is 5 bytes larger
than its incoming 3095-byte zero-normal control. The reduction from the older
forward interface to the goal-directed family includes a shared validated
traversal and a changed certificate protocol; it must not all be attributed
to the mathematical normalization change.

## Start here

- report.pdf / report.tex: complete report and standalone source.
- main.tex / sections/: editable source components.
- goal_checker/code/full_expression_checker.py: selected complete checker.
- goal_checker/code/full_checker.py: readable block-form counterpart.
- goal_checker/code/raw_checker.py and zero_checker.py: matched controls.
- goal_checker/FORMAT.md: exact input contract.
- goal_checker/AUDIT.md: independent same-run implementation review.
- goal_checker/tests/ and evidence/: certificates, measurements, receipts.
- forward/: independent forward kernel, untrusted normalizing proof compiler,
  source certificates, and normalization tests.
- reference/: attributed upstream foundations, overview, and license.
- PROVENANCE.json / CLAIMS.json / SHA256SUMS: source identities, claim boundaries,
  and integrity information.

## Run

From the extracted directory:

    python3 goal_checker/code/full_expression_checker.py < goal_checker/tests/examples/full/exceptional_case_zero.json

Acceptance is normal exit and exactly ACCEPT
followed by a newline. Exceptions reject.

To reproduce all portable evidence:

    python3 reproduce.py

To rebuild the standalone article and PDF:

    python3 build.py

The checker and test code needs Python's standard library only. Building
the paper requires pdflatex and the standard packages named in main.tex.
Rebuilding files can change their checksums; verify the delivered manifest
first, then use --skip-manifest for subsequent intentional reruns.

## Verification and limitations

The goal-directed family passed 680 process checks (440 acceptances and
240 rejections), including normal and optimized Python, plus 1750 traversal
comparisons/validation checks. The forward package translated all 64 packaged
source proofs, passed 132 process checks, and passed 5000 finite normalization
checks. The deliberately invalid naive introduction translation is rejected;
the compound-envelope repair is accepted.

The universal metatheorems are written mathematical proofs. There is no new
Lean/Rocq formalization and no new machine-checked Python correspondence proof.
The inherited Lean endpoints were inspected, not rebuilt.

Uniform normalization of all primitive-recursive program descriptions is
total recursive but not primitive recursive, and can expand terms enormously.
No internal iPRA proof of uniform normalization or universal evaluator is
postulated. Both interpretations act on fixed finite expressions.

The selected checker validates all syntax used by a proof. After a validated
hypothesis or reflexive leaf closes, its proof payload is intentionally ignored;
the same policy is used in the matched controls.

## Source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot: 11be5aabc6b07262046e2553419bc6b05271d178

Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Upstream files retain their MIT No Attribution license. The new contribution
is distinguished from the inherited scalar arithmetic, logical macros,
single-introduction rule, and original iPRA interpretation bridge.
