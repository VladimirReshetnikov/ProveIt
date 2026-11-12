# A one-sided computation guard for iPRA

This package gives a new presentation of intuitionistic primitive recursive
arithmetic, compared with ProveIt ConciseIPRA at commit
`1517d9d79ce33f631e0f82960c849427cbba23bf`.

The numerical language remains `x, 0, S(t), I(n,a;u.h)`. The change is the
canonical atomic matrix beneath the paired binder:

```text
a(x,y) = I(y, a(x,y); u.h(x,y,u)).
```

The initializer is on the **left** of the equation and inside its single
iterator. This permits a single introduction schema, determined by the
matrix root, together with transport sources restricted to terms other than
literal `0`. The report proves recovery of all omitted transport instances,
effective translations to and from the native core, and both formula
composites. The inherited bridge then gives bi-interpretability and
equiconsistency with full first-order iPRA on whole numerical domains with
actual equality.

The compact size improvements are modest. No absolute minimality theorem
or new Lean/Rocq verification is claimed. The report explicitly reports the
larger cost of strict public syntax validation.

## Contents

- `report.tex`, `report.pdf`: complete article, including the new proofs and
  reproduced inherited arithmetic and logic appendices.
- `proofs/`: new mathematical sections and implementation explanation.
- `code/`: three compact complete checker profiles, a readable independent
  expansion, and a strict public-goal profile. Each checker is standalone.
- `tests/`: untrusted named proof construction, certificates, and negative
  controls. The worked constructions include equation induction and the
  zero-source bootstrap using only mirrored atomic introductions.
- `evidence/`: measurements, runtime and compression versions, validation
  results, proof audits, source provenance, and generated report tables.
- `reference/`: frozen comparison checkers, inherited producer helpers,
  arithmetic proof sources, and selected Lean theorem declarations from the
  pinned repository. These Lean excerpts are reference material, not a
  self-contained Lake project or a new formal verification.
- `reproduce.py`, `tools/render_evidence.py`, `Makefile`: reproduction commands.

## Reproduce

Python 3.12.14 is the comparison runtime. The checkers use only the standard
JSON library; the evidence runner uses only Python's standard library.

```bash
python3 reproduce.py
python3 tools/audit_named_formulas.py --kernel-dir . --output evidence/named_formula_audit.json
python3 tools/render_evidence.py
```

To rebuild the PDF with a normal TeX Live installation:

```bash
make pdf
```

To check one certificate with the byte profile:

```bash
python3 code/checker_bytes.py < tests/certificates/derived_literal_zero_transport_local.json
```

Use a `*_global.json` certificate for `checker_tokens.py`. The other four
profiles use the `*_local.json` encoding. Acceptance requires exit status
zero and exactly `ACCEPT` followed by a newline. An exception or resource
failure is rejection, never a proof. The mathematical completeness statement
uses the same ideal unbounded execution convention as the baseline.

## Measurement and input contracts

The measured source is the **entire module**, after removing genuine
docstrings and applying `ast.unparse`, plus one newline. Significant tokens,
AST nodes, normalized UTF-8 bytes, raw source bytes, SHA-256 hashes, and gzip
level-9 sizes are recorded. Gzip is supplementary information, not an
optimization objective. Different profiles attain different coordinates.

The compact profiles check proofs under the repository's canonical encoding
contract and may accept broader sound administrative goals. They do not
validate the complete canonical public grammar. `strict_checker.py` adds a
closed-term and formula validator, checks real versus dummy binding slots,
and verifies mirrored initializers after the necessary index shift. Its
complete cost is reported separately. The derived strict source-dispatch
comparator is supplied for a fair comparison and is not an upstream record.

The named proof generator is a collection of explicit worked constructions;
it is not presented as a complete translator of every possible proof in
either calculus. Inherited normalizer helpers retain their original scope.
The universal completeness and interpretation claims are the written
metatheorems, while executable evidence tests the concrete instances listed
in `evidence/validation.json`.

## Attribution and verification status

The scalar iterator, original logical macros, arithmetic compiler, arity
encoding, certified-zero computation expansion, and core of the
zero-source symmetry construction are inherited from ProveIt. The new
contribution is the mirror guard, its compatibility proof, the
substitution-free induction bootstrap, and the corresponding canonical
certificates and combined checker profiles. The report identifies the
dependency boundary explicitly.

The existing native/iPRA bridge was inspected in the pinned Lean sources.
It was not rebuilt here, and the new mirrored calculus has not been
formalized in Lean in this package. No empirical test is described as a
replacement for the universal mathematical proof.
