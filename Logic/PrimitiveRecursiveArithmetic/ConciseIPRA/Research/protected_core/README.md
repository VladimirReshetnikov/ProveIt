# Protected equations: a smaller iPRA proof kernel

Start with `report.pdf`; its complete LaTeX source is `report.tex`. The report
states all rules, proves the protected-atom compatibility theorem, gives both
interpretation composites with iPRA, and explains the precise comparison contract.

The construction represents arbitrary equality `s=t` by `W(s)=W(t)`, with
`W(r)=I(0,r;u.0)`, and proves completeness using iterator-headed transport sources.
Its measured gain is modest and is not a claim of absolute minimality.

This directory contains three small standalone certificate checkers, a readable
expansion, an optional strict public-goal checker, frozen comparison programs,
and independent proof production and regression support. The mathematical
equivalence argument belongs to the accompanying research report. Executable
fixtures are evidence about the implementations, not a proof-assistant
verification of that argument.

## Reproduce

Run from any working directory:

```sh
python3 /path/to/this/directory/reproduce.py
```

Only the Python standard library is needed. The frozen measurements were made
with CPython 3.12.14. The command regenerates named certificates, audits every
generated derivation for forbidden literal-zero transport sources and
unguarded atomic D matrices, verifies upstream source hashes, measures all
complete programs, and executes the checkers both normally and with `python -O`.
Current results are in `evidence/validation.json`, `evidence/metrics.json`, and
`evidence/guard_and_source_audits.json`.

For one certificate:

```sh
python3 code/checker_bytes.py < evidence/certificates/protected_computation_zero_local.json
python3 code/checker_tokens.py < evidence/certificates/protected_computation_zero_global.json
```

Acceptance requires exit status zero and exactly `ACCEPT` followed by a newline.
An exception or timeout is not an acceptance. The checkers do not use Python
assertions, so optimization does not remove checks.

## Complete-program measurements

Source is parsed, actual docstrings are removed, and `ast.unparse` plus one final
newline supplies the normalized source. Comments are therefore excluded. Token
counts omit whitespace, comments, indentation and end markers. AST counts use
all nodes. Gzip uses level 9, `mtime=0`, and includes its wrapper.

| Program | Normalized bytes | Significant tokens | AST nodes | Gzip 9 bytes |
| --- | ---: | ---: | ---: | ---: |
| Source-dispatch byte profile | 526 | 266 | 305 | 330 |
| Source-dispatch token profile | 572 | 259 | 289 | 339 |
| Source-dispatch AST profile | 607 | 263 | 283 | 348 |
| Guarded-core byte profile | 527 | 266 | 307 | 335 |
| Guarded-core token profile | 575 | 260 | 290 | 345 |
| Guarded-core AST profile | 607 | 263 | 286 | 349 |
| Protected byte profile | **525** | 265 | 303 | 331 |
| Protected token profile | 571 | **258** | 287 | 339 |
| Protected AST profile | 606 | 262 | **281** | 348 |
| Readable expansion | 1301 | 284 | 326 | 511 |
| Strict protected public-goal checker | 1251 | 505 | 582 | 582 |

The inspected compact envelope moves from `(526 bytes, 259 tokens, 283 AST
nodes)` to `(525 bytes, 258 tokens, 281 AST nodes)`. Each envelope is attained
by three different programs. No single listed program attains all three
coordinates. This is a small reduction against the pinned comparison programs,
not an absolute lower bound or a claim of global minimality. Gzip is an
informational coordinate and increases by one byte for the byte profile.

## Public formulas and raw certificates

Public atomic formulas have an iterator-headed term on each side. The wrapper
`W(s) = I(0,s;u.0)` embeds an arbitrary old equation `s=t` as `W(s)=W(t)`.
Public compound formulas use D. An immediate atomic D matrix is guarded:
`I(y,0;u.h)=I(y,0;u.k)`. The designated contradiction is `W(0)=W(S0)`.

The three compact programs and the readable program implement the permissive
raw certificate protocol inherited from the compared research packages. They
do **not** enforce that a submitted goal belongs to this narrower public
grammar. Arithmetic computation equations, Q resources, and truth aliases are
administrative proof data. Their meanings and the scope codec must be included
in the mathematical account of the protocol. A public-language-only interface
must use `strict_checker.py`, whose entire size is reported above. Its parser is
not silently charged to the 525-byte profile. See `CERTIFICATE_SPEC.md` for the
exact distinction.

The local profiles begin with the retained administrative truth `[]`; the
global token profile begins with no retained assumptions. Their negative-label
numbering conventions and raw aliases are consequently not interchangeable.
Use the separately generated `_local.json` and `_global.json` certificates.

## Evidence and limitations

Eleven named public examples include wrapped computation, protected
reflexivity, compound case introduction and elimination, guarding in both
directions, a 564-instruction induction certificate whose hypothesis is used,
and the guarded implication from `W(0)=W(S0)` to `W(S(S0))=W(0)`.

The finite proof normalizer maintains both directions of each generated
equation, using symmetry only at a nonzero source and joining nonzero terms
through the common zero wrapper. It does not invoke the source-dispatch
package's general theorem about arbitrary hypotheses `0=t`. It rejects an
unsupported zero-source equation leaf or a non-equational transport template
instead of making a correctness claim about them. Every produced D matrix is
audited; the normalizer does not change those matrices.

The executable test support is untrusted and never imported by any checker.
The test suite includes the protected contradiction, witness and eigenparameter
leakage controls, false endpoint and unproved-major controls, malformed input,
and an old zero-source transport certificate that the combined protocol rejects
while accepting its explicitly normalized replacement.

## Provenance

The upstream files are from Vladimir Reshetnikov's ProveIt at commit
`1517d9d79ce33f631e0f82960c849427cbba23bf`, under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/`. Their exact Git blob
hashes, SHA-256 hashes, byte counts and repository paths are recorded in
`evidence/frozen_sources.json`; `reproduce.py` verifies them before running.
The repository's MIT No Attribution license is included at
`reference/LICENSE.txt`. New local code is marked by its location outside the
frozen `reference/` tree; the two frozen producer copies are separately checked.
