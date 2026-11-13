# Canonical R: standalone strict checker and matched controls

This folder contains a transparent strict implementation of the new canonical successor-seeded R presentation and two parallel controls. Each checker module is standalone. The six-rule canonical presentation has no independent successor constructor and no zero-computation proof instruction; normalized substitution enforces its zero-counter body-erasure law.

The matched comparison includes that normalization cost, complete public syntax checking, scopes, all proof rules, JSON decoding, and exact conclusion checking. It does not claim to beat the repository's approximately 522-byte compact checker, which uses a different representation and validation contract.

## Reproduce

```
python3 build_family.py
python3 test_family.py
```

The generator emits the three standalone modules from one common template. The tests emit named JSON certificates, `results.json`, normalized standalone copies, and deterministic level-9 gzip files. Gzip is informational; it was not the optimization objective.

## Measured comparison

CPython 3.12.14; docstrings removed, then `ast.unparse` with one final newline. Token counts omit comments, whitespace/newline/indent tokens, encoding and end markers. AST counts count every node from `ast.walk` of the normalized module. Gzip uses compression level 9 and `mtime=0`.

| Complete standalone checker | Rules | Significant tokens | AST nodes | Normalized bytes | Gzip-9 bytes |
|---|---:|---:|---:|---:|---:|
| Canonical successor-seeded R | 6 | 1,338 | 1,485 | 4,611 | 1,205 |
| Raw successor-seeded R | 7 | 1,378 | 1,532 | 4,753 | 1,209 |
| Scalar I and independent S | 7 | 1,433 | 1,595 | 4,923 | 1,224 |

In this matched implementation family, canonical R saves 312 normalized bytes (6.34%), 95 tokens and 110 AST nodes relative to scalar I. Relative to raw R, its saving is 142 normalized bytes, 40 tokens and 47 AST nodes. These are implementation measurements in a controlled family, not global minima.

## Tests

The canonical checker accepts 12 named valid certificates and rejects 18 named invalid certificates. Each control accepts 13 and rejects 15. Every result is replayed through both the original and normalized standalone executable.

The positive certificates cover successor computation, derived reflexivity, both crossed rule directions, progress and compound-case introduction, paired elimination, a fresh existential witness reused in a nested introduction, a genuinely used equation-induction hypothesis, and an equation transport whose substitution exposes a zero counter.

The negative certificates cover a false goal, future witness dependencies, negative/Boolean/float indices, an out-of-scope recursor body, eigenparameter escape, a literal-zero transport source, a compound transport template, an incorrect closure base, an attempt to use progress at a nonzero witness, unknown instructions, extra fields, and canonical zero-body violations.

Each mode additionally passes direct recursor-body and nested-D/Q capture controls and 160 comparisons between numerical substitution and an independent natural-number evaluator. These finite controls supplement the report's proofs; they do not replace them.

See `FORMAT.md` for every proof instruction and its precise de Bruijn convention. `results.json` records individual outcomes and hashes. No proof-assistant verification of these new checkers is claimed.
