# Delivery validation

The packet was checked on 22 October 2026.

## Mathematical review

The article's fixed-input specialization, signed repunit argument, auxiliary positivity, index recovery, restoration of the native compiler conditions, and completeness map were reviewed independently of the circuit author's derivation. The review notes identify the inherited Pell, helical-compiler, and K215 calibration dependencies. The article also proves a uniform nonzero leading homogeneous form, establishing exact degree 169; the unrestricted-integer substitution has exact degree 338.

The compact main projection slack is positive. At a solution the large-Pell bound and main norm additionally force it to be at least two, permitting a split into two positive summands if that projection notation is retained. This uses no new equation or arithmetic row.

## Executed verification

`python3 verify.py` completed with all five stages passing:

1. The five fixed-input circuit packets: full source, counts, liveness, algebraic identities, and degree diagnostics.
2. The two explicit domain conversions: all 86 or 198 arithmetic rows, dependency and liveness checks, and substitution fixtures.
3. The literal K215 normalizer: source hash, 3,440 valid fold rows, and 64 loader lengths.
4. The local predicate and coefficient layout: two exhaustive 18-tile fixtures, each with 1,889,568 central crosses; the exact compressed census; and the powers-of-five layout bounds.
5. The independent verifier: 64 independently transcribed factor/output fixtures, 5,160 virtual-coordinate fold cases, and the fixed-input loader after ten steps.

The exact commands, exit statuses, output hashes, and full outputs are in `artifacts/verification/receipt.json` and the adjacent text files. The existing compiler manifest was also checked and every listed hash matched after regeneration.

The circuit generator was separately replayed in a fresh directory containing only its source and the parent84 receipt; the regenerated JSON was byte-identical. The domain-conversion generator likewise reproduced its JSON from only its own source and the main circuit JSON.

## Document and archive

The 24-page PDF was built from the delivered TeX sources by two pdfLaTeX runs. Its final log has no undefined references or overfull/underfull boxes. Every rendered page was inspected for layout, and the main equation, alternative system, literal evaluator, and coefficient formulas were additionally inspected at full-page resolution. The front matter was finalized with a separate contents page.

The archive contains the main TeX file, both required TeX includes, the compiled PDF, all seven complete circuit packets and their generators, the actual normalized transition table, the coefficient recipe, check receipts, provenance, and upstream notices. Temporary render images, Python bytecode caches, and TeX build byproducts are excluded. `SHA256SUMS` records the delivered file hashes; ZIP integrity and manifest contents were checked when the archive was assembled.

## Evidence boundaries

These checks do not constitute a new Lean or Rocq kernel build or an internal ZFC proof string. The mathematical equivalence is proved using the explicitly cited inherited results. The full finite window list, giant binary/decimal coefficient expansions, and the numerical value of the fixed correction bit were not materialized. No target solution, K215 halting decision, or proof of Con(ZFC) is supplied or inferred from the finite checks.
