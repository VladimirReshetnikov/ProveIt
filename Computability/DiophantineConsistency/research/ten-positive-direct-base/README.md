# Direct-base research: ten positives,107 operations,degree340

This is a separate cost/degree research tradeoff against the accepted
101-operation degree368 equation. It retains ten positive unknowns and
lowers degree by28 at six extra operations. No canonical update is
proposed. All accepted endpoints, pages, common documents and Lean files
remain unchanged.

The complete ordinary proof draft is `PROOF.md`. Its new idea is to
replace the product X=wq by an independent positive coordinate:

    X=q+x, x>0,
    B=(q*K0+X)*C-qF, W=1+q(q-1)L, P=q^4(q-1).

A new -X/q^4 proof term in the carrier first forces q|X after the
projection has recovered X=2^R. Only then do q being a power of2 and
R>3q make X/q^4 an integer. The original transport, first-index,
whole-product and source reconstruction are staged around this order.
The larger carrier uses an explicit strengthened height bound valid
already at r>=35, below the actual r>=48. There is no early division
of X by q or cancellation of H modulo q.

`prototype-equation.json` is the entire literal finite prototype; all107
gates, ten inputs and four fixed ports are live. The evaluator has64
multiplications,25 additions and18 subtractions. `PREFIX_MAP.json`
accounts for every original row and each of the six insertions. The
entire original compact44 tuple is copied byte for byte under
`coefficients/`, with complete gzip/raw hashes. No port is inferred
from the arithmetic box or exchanged with a different tuple.

The exact degree340 certificate has selected coefficient

    [J^156*x^40*i^20*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^156>0.

The highest x-degree part excludes every K0-dependent leading term.
`probe.py` independently expands all35 octic coefficients and its
centered leading component, multiplies the eight-formal-variable
leading expressions, checks the selected coefficient and both actual
whole-tuple degree340 lines. It also checks120 quotient-licensed
modular transformations against the entire accepted parent schedule,
including Z_new=q*Z_old and output_new=q^8*output_old. All parent
manifest/source/port bytes are authenticated. Normal and optimized
runs pass; their receipts and exact output logs are retained.

These are finite prototype and transcription checks, not an independent
implementation of the full semantic compiler. The unbounded draft still
requires ordinary peer acceptance before endpoint promotion. No new Lean
or encoded object-ZFC proof, consistency assertion, optimality claim or
new page is supplied. Lean remains paused.

Reproduce from the repository root:

```sh
python -B Computability/DiophantineConsistency/research/ten-positive-direct-base/probe.py
python -B -O Computability/DiophantineConsistency/research/ten-positive-direct-base/probe.py
```
