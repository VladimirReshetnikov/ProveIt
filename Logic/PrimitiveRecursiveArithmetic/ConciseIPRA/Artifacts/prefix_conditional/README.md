# Smaller complete presentations of iPRA

**Result:** the whole-JSON raw coordinate envelope improves from
**245 tokens / 263 AST nodes / 462 normalized bytes** to
**244 / 261 / 461**. Allowing JSONL, it improves from **240 / 259 / 462**
to **239 / 257 / 461**. Different complete programs attain the different
coordinates. A fully validated native companion decreases from 600 to 599
normalized bytes.

The comparison includes all 16 incoming ZIP archives at ProveIt commit
`1156099ffe30f7497d2c11ab20271f46cffcd115`, not just the integrated article.
These are empirical minima among admissible programs in that snapshot,
not proven absolute lower bounds.

This is an implementation reduction of the existing iPRA axiomatization.
**No arithmetic axiom or inference rule has been deleted.** The report
states the complete mathematical theory and its inherited bi-interpretation
with full first-order intuitionistic primitive recursive arithmetic. The
new operational correspondence proofs transfer that bridge unchanged.

## Deliverables

- `report.tex`, `report.pdf`: the complete report, axioms, rules, logical
  macros, bridge, exact implementation proofs, measurements, and limitations.
- `code/`: six independent measured checkers and deterministic gzip files.
- `controls/`: exact pinned sources used for comparison.
- `tools/`: a readable checker, certificate translators, measurement script,
  and portable validation scripts.
- `examples/` and `fixtures/`: positive, negative, malformed-input, and
  scope-boundary certificates.
- `evidence/`: measurements, provenance, independent review, and test results.

## Exact measurements

CPython 3.12.14; the entire source is normalized with `ast.unparse`, followed
by one final LF. Gzip uses level 9 and `mtime=0`, with no filename.

| Complete checker | Input | Tokens | AST nodes | Bytes | Gzip-9 |
|---|---|---:|---:|---:|---:|
| `checker_tokens244.py` | Whole JSON | 244 | 269 | 547 | 338 |
| `checker_ast261.py` | Whole JSON | 252 | 261 | 593 | 356 |
| `checker_bytes461.py` | Whole JSON | 267 | 298 | 461 | 313 |
| `checker_tokens239.py` | JSONL | 239 | 261 | 553 | 332 |
| `checker_ast257.py` | JSONL | 246 | 257 | 593 | 348 |
| `checker_strict599.py` | Whole JSON, fully validated | 330 | 372 | 599 | 391 |

The byte profile's gzip size is larger than its 310-byte compressed control.
The strict profile's gzip size is larger than its 387-byte compressed control.
Those raw-byte reductions are not compressed-size improvements.

## Run the examples

From this directory, using Python 3.12.14:

```sh
python3 code/checker_tokens244.py < examples/minimal/zero_computation_three_field.json
python3 code/checker_ast261.py < examples/minimal/zero_computation_three_field.json
python3 code/checker_bytes461.py < examples/minimal/zero_computation_four_field.json
python3 code/checker_tokens239.py < examples/minimal/zero_computation.jsonl
python3 code/checker_ast257.py < examples/minimal/zero_computation.jsonl
python3 code/checker_strict599.py < examples/strict_zero.json
```

Each successful invocation prints `ACCEPT`. The corresponding `false_equation`
fixtures must terminate unsuccessfully. Exceptions are rejection, not proof
acceptance. The checkers do not use Python assertions, so `python3 -O` preserves
their checks.

## Certificate contracts

The first five checkers retain the compared raw integer/list certificate
contract and guarded public goal grammar. They are not arbitrary-JSON public
syntax validators. The complete grammar and decoding convention are specified
in the report. Use `checker_strict599.py` when the entire input alphabet and
the unrestricted native Eq/D public goal must be validated by the program.

The token and AST profiles use the same three-field return-reservation
protocol. Their whole-JSON input is the JSONL records reversed into one
array: the goal becomes the last element, and packets are popped from the
end. The JSONL input starts with the goal and continues with packets in
consumption order.

The 461-byte profile uses the inherited offset-two syntax and four fields.
Its final element is `[goal, 0]` for a closed theorem. A packet is now
`[source, target, template, major]`; the former order was
`[major, source, target, template]`. Only top-level packet rows are rotated.
Nested terms, formulas, and the final goal/header are never rotated.

The strict companion uses the same packet rotation, but its different
native syntax codes numerical zero by the scalar `1`. This is an encoding
convention, not an object-theoretic equation between zero and one.

```sh
python3 tools/translate_certificates.py rotate < old_four_field.json > new_four_field.json
python3 tools/translate_certificates.py unrotate < new_four_field.json > old_four_field.json
python3 tools/translate_certificates.py stream-to-whole < proof.jsonl > proof.json
python3 tools/translate_certificates.py whole-to-stream < proof.json > proof.jsonl
```

The translators are conveniences; measured checkers do not import them.
They do not translate between different scope-allocation protocols or syntax
offsets.

## Reproduce measurements and checks

```sh
python3 tools/measure.py
python3 tools/verify_profiles.py
python3 tools/verify_strict.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The compact profile audit ran 560 isolated checker executions (normal and
optimized Python) and 56 stream-state/packet comparisons without a mismatch.
The strict companion passed 172 further executions on 43 cases. The report
contains universal operational arguments; finite tests are additional
implementation evidence, not a substitute for the bi-interpretation proof.

## What changed

1. **Prefix packet layout:** reorder four fields, bind the packet as `r`,
   and reuse `r[:3]` and `r[:2]` instead of reconstructing those exact arrays.
2. **Conditional freshness:** select the post-major floor or zero directly,
   preserving the order of witness opening, major checking, and scope update.
3. **AST representation:** compose the conditional with existing sequence
   pattern matching and move the initial floor assignment into a default
   expression evaluated once at function definition time.

No hidden proof-checker dependency, dynamic executable payload, compressed
kernel, proof-search oracle, or uncounted acceptance driver is used.

## Mathematical and formalization status

The object theory has one numerical sort and scalar iterator terms. Its
small guarded presentation has six primitive families: hypothesis, two
computation schemas, source-selected elimination, witness elimination, and
root-selected introduction. The public language and equation-only progress
restriction matter. The inherited bridge supplies both interpretations,
both term and formula round trips, whole numerical domains, actual equality,
and identity domain composites.

The repository formalizes the underlying native/iPRA bridge in Lean. The
new Python rewrites here have written operational proofs and executable
checks; they are not newly formalized Python semantics in Lean. No fresh
Lean build is claimed by this package.

This proposal does not establish an absolute simplest axiomatization,
a single checker below all three old minima, or a new mathematical axiom
deletion. It establishes a strictly smaller empirical family envelope under
the existing complete-checker metric.
