# Five rules for iPRA with ordinary substitution

This package gives a raw five-pattern clause calculus, CE5, and a written
proof that its ordinary realization is bi-interpretable and equiconsistent
with full first-order intuitionistic primitive recursive arithmetic.

The numerical domain remains the whole domain, equality is actual equality,
and both numerical interpretation composites have graph `x = y`.

## The simplification

CE5 combines the existing computational-equality interface with the existing
clause presentation. It uses raw terms `x`, `0`, `S(t)`, `I(n,a;u.h)` and
formulas `s = t` and `D(x,y).B`. Its five primitive patterns are:

1. Reflexivity.
2. Eval, a deterministic partial computational equality step.
3. Use of a retained conditional-universal clause.
4. Paired elimination with a fresh witness.
5. Witness-directed paired introduction.

Ordinary substitution is used throughout. There is no term normalization
and no equality-template argument in certificates. The current canonical
clause presentation already has five patterns; CE5 does not claim the first
five-rule calculus. It is a new combination of existing component reductions,
with a measured improvement against matched transparent complete checkers.

## Measured complete programs

On CPython 3.12.14, after stripping docstrings and normalizing with
`ast.unparse` plus one line feed:

| Program | Bytes | Significant tokens | AST nodes | Gzip-9 bytes |
| --- | ---: | ---: | ---: | ---: |
| Matched canonical five-rule control | 3175 | 903 | 1035 | 1035 |
| Matched raw six-rule control | 3252 | 930 | 1072 | 1020 |
| **Raw five-rule checker** | **3046** | **853** | **993** | **990** |

The canonical comparison saves 129 bytes (4.1%), 50 tokens, and 42 AST nodes.
All parsing, validation, scope handling, substitution, inference, and output
are counted. Gzip level 9 is reported only for information.
The readable new source is 3456 bytes and compresses to 1191 bytes with
gzip-9, including its explanatory docstring and original formatting.

Final verification: 32 positive examples translated in both directions,
24 rejected adversarial examples, and 112 public command-line runs
(with and without Python optimization) all returned the expected result.

**Limit:** this does not beat the repository's historical 516-byte compact
checker. It improves the transparent fully validated family. There is no
claim of global minimality or a new Lean/Rocq formalization.

## Files

- `report.pdf`: complete compiled report, including inherited arithmetic
  reference proofs and the full new checker listing.
- `report.tex`, `paper/`, `theory/`: editable LaTeX source.
- `code/clausal_eval.py`: complete new standalone verifier.
- `code/matched_control.py`: same-interface raw six-rule control.
- `code/matched_canonical.py`: same-interface canonical five-rule control.
- `code/translate.py`: checked proof transformations between the raw equality
  interfaces, preserving end formulas.
- `tests/verify.py`: meaningful positive, negative, scope, translation, and
  public-interface checks; also recreates normalized and gzip-9 files.
- `examples/`: valid certificates and an invalid iterator-counter attack.
- `evidence/`: exact measurements, verification results, source provenance,
  and PDF inspection record.
- `reference/`: source audit, the pinned README, inherited bridge sections,
  and original licence.
- `theory/rigidity.tex`: proved successor-rigidity-to-zero-induction result,
  with its unresolved full scalar bootstrap explicitly separated.

## Reproduction

From the extracted package root:

```sh
python3 tests/verify.py
python3 tools/build_evidence.py
python3 code/clausal_eval.py < examples/used_induction_hypothesis.json
python3 code/clausal_eval.py < examples/capture_avoiding_witness.json
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The valid examples print `ACCEPT` and return exit status zero. The supplied
invalid example `examples/reject_false_iterator_counter.json` must print
`REJECT` and return a nonzero exit status. Normalized modules have the same
public interface as their readable sources.

`translate.py` exposes `translate(certificate, forward=True)`. Forward maps
the raw six-pattern control to CE5; `forward=False` maps CE5 back. It checks
the input and the produced proof. It is not needed by the standalone
verifier and is not included in the verifier-size metric.

## Public certificate format

The top-level object has exactly `goal` and `proof`. The goal is a closed
Eq/D formula. There are no externally supplied hypotheses or free variables
in this public interface. The mathematical theory permits general open
sequents and arbitrary retained clauses; the verifier checks closed theorems.

The integer `0` denotes zero. Negative integers name fresh parameters
introduced inside proof branches. Positive integers are local bound indices,
starting at 1. Raw successor is `[0,t]`, iterator is `[n,a,h]`, equality is
`[s,t]`, and D is `[B]`. Only the body of an iterator binds its state
variable. D binds two variables: its inner coordinate has index 1, its outer
coordinate index 2. A formula/term validator supplies the expected sort.

The proof tags are:

| Tag | Form | Meaning |
| --- | --- | --- |
| `r` | `["r", term]` | Reflexivity |
| `v` | `["v", major, minor]` | Eval |
| `u` | `["u", index, target, premise]` | Use a retained clause |
| `e` | `["e", goal, major, branch]` | Paired elimination |
| `i` | `["i", goal, witness, branch]` | Paired introduction |

The report specifies every side condition and the exact partial operation
used by Eval. In particular, an iterator counter that is itself an iterator
is not a syntactic successor. The supplied attack example checks this
distinction.

## Sources and proof status

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/tree/fa9d969919315b97796a1dd288f431cd3e41ffca/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The comparison includes the incoming `ipra_clausal_canonical.zip` and
`ipra_scalar_uniqueness.zip`, as well as the fifty filed proposal summaries.
The component mathematics and inherited arithmetic proofs are credited in
the report. The exact raw CE5 combination was not found in that scoped
review; no wider literature-priority claim is made.

The theory equivalence and interpretation composites are written proofs.
Executable finite tests check implementation examples and certificate
translations. They are not a proof-assistant verification of all certificates.

The separate successor-rigidity result is complete only as a reduction to
zero-equation induction. It is not used as an unproved replacement for
full equation induction in CE5.

Original ProveIt sources are supplied under their MIT No Attribution
licence in `reference/LICENSE-ProveIt.txt`. New package code may be used under
the same terms; the provenance of inherited mathematics is retained.

