# A smaller complete iPRA checker and a symmetry obstruction

This package contains a complete mathematical presentation of intuitionistic
primitive recursive arithmetic, a smaller executable proof checker, and a new
extension of the eventually constant power obstruction. **It does not establish
the requested significant new simplest axiomatization.** The positive axiom
basis is inherited; the implementation reduction and new negative theorem are
separate results.

## Main results

The recommended complete checker has **612 normalized Python bytes, 266
significant tokens, and 310 AST nodes**. Its exact source gzip at maximum
ordinary level 9 is **360 bytes**, reported as FYI. The inspected current corpus
has separate minima **616 bytes / 268 tokens / 300 AST nodes**. Thus the selected
program improves bytes and tokens but not AST count. It uses ordinary explicit
list dispatch. Smaller-byte and smaller-AST ancillary profiles show tradeoffs;
the AST profiles retain the stated malformed-string recursion-limit qualification.

The new theorem proves exact coordinatewise truth transfer in eventually
constant powers for every formula generated from atoms and truth by conjunction,
existential quantification, and universal quantification, with arbitrary finite
alternation. These powers satisfy induction for all such matrices and every
standard-true implication between them, yet retain nontrivial finite-parameter
involutions. They cannot be ordinarily first-order bi-interpretable with iPRA,
even using multiple sorts, arbitrary definable domains/graphs, finite tuples,
or quotient equality. This extends an argument already in the drafts; no
literature-wide priority or checker-size lower bound is claimed.

## Read first

- `report.pdf`: the complete paper, including explicit rules and attributed
  arithmetic/logical bridge appendices.
- `report_standalone.tex`: one self-contained LaTeX source, with all included
  sections and the selected checker inlined.
- `report.tex`, `theory/`, `reference/*.tex`: modular sources with provenance.
- `CLAIMS.json`: exact established results, qualifications, and unresolved goals.

## Executable artifacts

| Program | Bytes, normalized | Tokens | AST | Gzip 9, raw |
|---|---:|---:|---:|---:|
| `code/checker.py` | 612 | 266 | 310 | 360 |
| `ancillary/checker_bytes.py` | 597 | 267 | 315 | 356 |
| `ancillary/checker_ast.py` | 639 | 267 | 298 | 360 |
| `ancillary/checker_ast_loop.py` | 689 | 266 | 296 | 369 |

`code/readable_checker.py` is a separately executable expansion, not an omitted
trusted dependency. Its measured size is in `evidence/measurements.json`.
The numerical and logical theory-specific code is entirely inside each checker.
Only the shared Python runtime and standard JSON library are outside those counts.

```sh
python3 reproduce.py
python3 code/checker.py < tests/fixtures/I0_arbitrary_seed.json
python3 code/checker.py < tests/fixtures/contextual_induction_seed_congruence.json
python3 code/checker.py < tests/fixtures/canonical_false.json
```

The first two single-certificate examples accept; the last rejects. Acceptance
requires exit status zero and the exact line `ACCEPT`. A rejected process may
print a traceback. The suite includes 310 complete-program runs, 40 malformed
input checks, and 24 guard-control executions. These finite tests do not
constitute proof-assistant verification of the universal metatheorems.

Reproduction uses Python's standard library and needs no network. Exact delivered
measurements use CPython 3.12.14 and zlib 1.3.2. Other versions may change AST
normalization or compressed byte counts. `python3 measure.py` records the local
runtime's values for inspection. `code/eventually_constant.py` regenerates exact
illustrative sequences; it is not a proof checker or a finite substitute for the
quantified theorem.

Run measurement rewrites or paper rebuilds in a working copy. The supplied
manifest records the delivered files and intentionally reports later changes
to those files.

## Build the paper

```sh
python3 build.py
```

An installed PDFLaTeX distribution with the listed standard packages is required.
The build expands all inputs into `report_standalone.tex`, compiles three times
without shell escape, and writes `report.pdf`. It records layout/reference
warnings in `evidence/build.json`. The delivered PDF was additionally rendered
and visually inspected.

## Source comparison and attribution

The GitHub comparison is pinned to ProveIt commit
`fb2dbd2a33c6b132671a54b029d0bf3cd98c633d`:

https://github.com/VladimirReshetnikov/ProveIt/tree/fb2dbd2a33c6b132671a54b029d0bf3cd98c633d/docs/drafts

The census covers 13 direct ZIP archives, 28 distinct recursively embedded
archives, and 370 distinct Python sources. `evidence/baseline_source_metrics.json`
and `evidence/boundary_classification.json` preserve the exhaustive metrics and
the review of all 31 sources at or below a coordinate minimum. Complete historical
checkers count; helper scripts do not. Repeating the full corpus scan requires the
original pinned ZIPs:

```sh
python3 tools/audit_corpus.py /path/to/ProveIt/docs/drafts corpus_metrics.json
```

The ordinary reproduction command uses only the frozen comparison programs
included here. The arity codec, predecessor packets, scalar arithmetic, and
logical reconstruction are attributed throughout the report. Source hashes are
in `evidence/provenance.json` and `evidence/inherited_provenance.json`. The original
MIT No Attribution license is included, while mathematical attribution is kept.

The symmetry theorem has independent written assistant reviews, preserved as
reviews. They are not external peer review or Lean/Rocq formalizations.
