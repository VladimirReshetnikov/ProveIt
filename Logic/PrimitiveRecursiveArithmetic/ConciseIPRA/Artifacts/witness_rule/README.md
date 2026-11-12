# A deterministic witness rule for iPRA

Research prepared for Vladimir Reshetnikov, 10 November 2026.

## Result and limit

This package establishes a small positive reduction. It does **not** establish
the requested significant foundational breakthrough or an absolute simplest
axiomatization.

The new calculus replaces the independent case/progress choice by one rule:
use equation progress exactly when the matrix is a literal equation and the
chosen existential witness is literally zero; use cases otherwise. The report
proves exact preservation of every native sequent. The omitted rules are
recovered using an unused witness coordinate and the already certified term
`C = I(2, 1; v.0) = 0`. The numerical and formula meanings do not change.
The inherited whole-domain bi-interpretation and equiconsistency with full
first-order intuitionistic PRA therefore transfer.

The current 17-archive supplied snapshot has an attained byte minimum of 558
(separate programs attain 262 tokens and 296 AST nodes). The two selected complete
programs here are:

| Program | Theory | Bytes | Tokens | AST | Gzip-9 |
|---|---|---:|---:|---:|---:|
| `code/checker_choice.py` | Inherited Choice-DI | 550 | 264 | 310 | 342 |
| `code/checker.py` | New deterministic witness rule | 555 | 266 | 312 | 344 |
| `code/checker_explicit_type.py` | Same new rule, ordinary exact-type test | 559 | 266 | 312 | 348 |
| `code/checker_explicit_list.py` | Same new rule, `isinstance` list test | 563 | 266 | 310 | 349 |

The sizes count the complete programs, including their input and verdict code.
The new rule itself costs five bytes relative to the 550-byte control. The
overall byte reduction comes from a small Boolean dispatch change and the
inherited invalid-image convention; the report's ablation separates them.
No selected program beats every old coordinate minimum. Gzip is informational.

`code/readable_checker.py` is an explanatory standalone expansion, also measured
and tested. It is not an imported dependency of a compact checker. All checkers
use only Python and its standard JSON library; neither a proof producer nor an
external axiom database is trusted.

## Open first

- `ipra_witness_rule.pdf`: complete paper, with explicit rules, equivalence,
  checker simulation, comparison, inherited complete iPRA bridge, and a separate
  restricted-congruence appendix.
- `ipra_witness_rule.tex`: standalone LaTeX source with all inputs inlined.
- `main.tex`, `theory/`, `reference/*.tex`: modular authoring sources and exact
  attributed inherited proof fragments.
- `CLAIMS.json`: established results and unresolved requirements.

## Run and reproduce

```sh
python3 reproduce.py
python3 code/checker.py < examples/zero_case_uses_base.json
python3 code/checker.py < examples/nonzero_progress_uses_IH.json
python3 code/checker.py < examples/closed_false.json
```

The two positive examples print `ACCEPT` and exit zero. The false example must
reject with nonzero exit status. Acceptance is **both** exit zero and exactly
`ACCEPT\n` on standard output; tracebacks are only rejection diagnostics.

Certificates are JSON stacks. The last item is the closed goal; earlier
four-field packets are consumed from the end. An unused prefix is permitted.
All canonical falsy major markers in the new witness interface are `[]`.
The witness, not that marker, selects case or progress. The old raw verdict
table must not be reused unchanged for this different certificate interface.
The producer regenerates named proofs and performs the necessary normalization.

The witness suite has 18 positive and 5 negative cases, across three compact
exact-list profiles plus the readable implementation and two Python modes:
184 complete CLI runs. Two mutation controls show that the atom-only progress
guard is necessary. The unchanged-choice checker has 72 separate CLI runs.
All delivered checks pass. The supplementary congruence validator checks six
symbolic proof trees and rejects three side-condition violations. These tests
are finite implementation evidence, not formal proofs of the universal claims.

Reproduction checks the supplied manifest first, then remeasures and reruns the
focused evidence. It does not execute the frozen historical source corpus.
Python standard-library dependencies suffice. Exact reported counts use
CPython 3.12.14 and zlib 1.3.2; other runtime versions may alter normalization or
gzip output. Rebuilding or editing can alter the delivered file hashes, so use
a working copy if you want to retain the original identity record.

```sh
python3 measure.py
python3 build.py
python3 tools/audit_snapshot.py
```

The PDF build needs a normal TeX installation and uses no shell escape. The
build script also handles the supplied environment's source-only TeX setup by
creating a private temporary format. `measure.py --write` intentionally refreshes
measurements and deterministic gzip files. The audit command remeasures the 443
frozen historical sources; it parses their code without executing it.

## Provenance and scope

Pinned GitHub snapshot:

https://github.com/VladimirReshetnikov/ProveIt/tree/76a2651601d17b34d46753f189ea026a21ce8d29/docs/drafts

The census covers 17 direct ZIPs, 32 distinct recursive ZIP payloads, 443 distinct
Python byte strings and 2,239 source occurrences after archive deduplication.
All 36 boundary candidates were inspected: three complete checkers and 33 supporting
utilities. The minimum in a finite corpus is not a proved global lower bound.

The arithmetic basis, paired-binder semantics, logical reconstruction, arity
encoding, certified zero, and arithmetic interpretation proofs are inherited
and attributed. The unused-witness proof gadget is also inherited. The new
mathematical result combines these mechanisms into a deterministic witness
restriction preserving the native consequence relation. The exact combination
was not located in the inspected supplied corpus; no literature-wide priority
claim is made.

The restricted-congruence appendix concerns a **different**, counter-dependent
successor-seeded recursor `R`. It is an incremental inference theorem, not the
theory implemented by the 550/555-byte programs. No checker-size figure is
assigned to that appendix.

The upstream MIT No Attribution license is retained. Mathematical attribution
is preserved independently of the license's permission. No GitHub repository
change was made. The proofs are written mathematics, not Lean/Rocq verification.
