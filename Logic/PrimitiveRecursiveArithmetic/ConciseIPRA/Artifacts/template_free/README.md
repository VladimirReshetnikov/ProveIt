# Template-free equality in a seven-rule presentation of iPRA

This package gives a complete native presentation of full first-order
intuitionistic primitive recursive arithmetic with no supplied equality
template in its primitive replacement rule:

From s=t and u=v, infer v=R_s^t(u).

R is one-pass, root-first, capture-safe replacement of every exact free
occurrence. Inserted targets are not revisited.

## Main result

An oversized computation marker recovers arbitrary selected-context
congruence using only computation at zero and the replacement rule.
Together with the inherited witness-sensitive introduction, the seven
primitive rules prove exactly the original native sequents, in arbitrary
contexts. The existing whole-domain bi-interpretation with iPRA therefore
transfers, including both formula round trips and the identity numerical
composite graph.

The PDF gives the full axioms, universal mathematical proof, explicit
interpretations and composites, implementation comparisons, and attributed
arithmetic/logical foundations. No absolute minimality or new compact byte
record is claimed.

## Start here

- ipra_template_free.pdf: complete research report.
- ipra_template_free.tex: self-contained flattened LaTeX source.
- main.tex: editable modular source, with section sources under evidence/.
- code/global_rewrite.py: standalone strict tagged checker.
- tests/: primitive proof certificates, generators, and validation.
- reference/: inherited sources and explicit comparison controls.
- compact/: separate compact forward implementation and tests.
- evidence/: source provenance, measured sizes, and verification receipts.

The copied Lean files are source references, not a standalone Lake project.
The new replacement equivalence has a written proof; it has not been
machine-checked in Lean or Rocq. Finite certificate tests provide
implementation evidence and do not replace that proof.

## Reproduce

Python 3.10 or newer is required (the original run used Python 3.12).
No network access or third-party Python modules are needed for the
checkers and their tests.

    python3 reproduce.py

The checkers are also exercised with Python optimization enabled, so
their correctness does not rely on assertion statements.

Build the report with an ordinary TeX Live installation:

    python3 build.py

To regenerate just the standalone TeX file:

    python3 build.py --tex-only

From the extracted directory, verify the original archive contents before
regenerating outputs:

    sha256sum -c MANIFEST.sha256

Measurements are normalized source bytes, significant Python tokens, and
AST nodes; gzip-9 is informational. Read the report for the precise
normalization and input-contract distinctions.

## Provenance and licensing

The inherited mathematical files are pinned at ProveIt commit
a4e5e96c456303cf231eab2aeeb3291d8889833f. The final comparison boundary
is 2a724ea8ec6665f91aa74c892414584b36ca698d.
Exact URLs and hashes are in evidence/sources.json and
evidence/comparison_sources.json.

The inherited files are distributed under the included ProveIt MIT No
Attribution license (reference/LICENSE). Existing one-template
replacement, witness-sensitive introduction, and the arithmetic and
logical interpretation bridge are explicitly attributed. The new claim
is template elimination by deterministic replacement and its oversized
marker completeness proof.
