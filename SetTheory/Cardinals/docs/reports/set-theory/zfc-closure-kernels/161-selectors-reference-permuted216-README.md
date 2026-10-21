# K216: permuted commands and a reused helper path

This packet constructs a deterministic binary Turing machine with **216 working states and 432 transition rows, including initialization from the completely blank tape**. Its ordinary mathematical proof, composed with the pinned ProveIt numerical-calculus calibration, establishes

```text
ZFC proves: not Halt(K216, blank) <-> Con(ZFC).
```

The primary machine is `machine/k216.tm`. It has one two-way infinite tape, alphabet `{0,1}`, blank symbol `0`, start state `0`, working states `0,...,215`, and separate halt state `216` with no outgoing transitions. Every move is `L` or `R`. A row has the format `state read write direction next`.

**Canonical SHA-256**

```text
b0cf986df02fc0383c788f3d06ac46ac179ed81b3f1546115668c13bf72eeaea
```

The native table has start `0`, dispatcher `84`, and halt `254`. Its SHA-256 is `eff4f5a3e2c81a674d1a799f634ee4606708b79899e65e8c3cb688dc87c954a3`. The canonical dispatcher is `83`; `machine/canonicalization.json` gives the complete state bijection.

## The new reduction

The pinned 217-state predecessor uses the dominated-rho8 numerical calculus. The logical theorem and its finite certificate are inherited. The new construction combines three ideas:

1. Read the additive counter field only within commands that need it. Closed source splices and a reassociation give **202 distinct subtrees**, versus 203 in K217, with the same 4,751 primitive occurrences. The exact source is reconstructed without search from the historical K219 and K217 inputs and compared with the independently calibrated noncommon-input reference.
2. Change native `81/0` from `0 L 92` to `0 L 111`. Both old and new routes have exactly the same three-step effect on every entire tape with a zero under the head. This frees a decoder row that previously had to serve the arithmetic engine.
3. Exchange the command codes for MP and NIP: **NIP=0, DROP=1, MP=2**, while AX retains selector `c+3` and wire fields `[c+3,y,x]`. The early blank-start selector is 2, so it enters MP's local field reader and creates the space needed for initialization. The proof compiler is transported through the tag change, including zero aliases and all natural junk codes.

The resulting primary allocation changes 38 retained rows of the pinned K217 table, deletes native state 163, and adds no state. A second successful assignment, **DROP=0, NIP=1, MP=2**, gives another 216-state machine in `secondary/`. It deletes native state 134 instead.

## Exact verification results

| Check | Primary 210 | Secondary 120 |
|---|---:|---:|
| Working states / transition rows | 216 / 432 | 216 / 432 |
| Distinct source subtrees | 202 | 202 |
| Primitive occurrences | 4,751 | 4,751 |
| Quantified runtime cases proved | 6,176 / 6,176 | 6,176 / 6,176 |
| Compressed symbolic steps | 1,605,450 | 1,605,505 |
| Smallest positive affine duration constant | 6 | 9 |
| Literal blank-start transitions to clean root | 95,674 | 96,244 |

Both machines reach the same complete source frame: native state 84, head −8, header at 57, extra gap 1, logical registers `(N,T,W,A,D,H,X,Y,L)=(4,0,0,0,0,0,0,0,0)`, and forty spare registers of value one. The tape has exactly 95 one-cells and is zero everywhere else. The primary prefix was independently replayed in sparse Python, dense Python, and C++, and also checked step by step after canonical state renaming.

The runtime proof quantifies over arbitrary natural primary registers and gap, and an arbitrary nonempty finite spare list. Literal rows, induction over unary scans, and structural induction over the spare list establish each whole-tape primitive successor or its halt. Every case has positive finite progress. The stored case inventory covers every primitive occurrence and both guards of each decrement; all 432 transition rows occur in the certificates.

The source proof supplies an explicit strong compiler and a cofinal refuting family beyond the actual initial cutoff 4. For Cantor pairing `P` and the encoded compiled suffix `R`, its first-candidate number is

```text
N_Y = P(3, P(Y, P(1, R))) >= Y.
```

This addresses the first-candidate packing convention, the zero NIP tag, and the search cutoff rather than merely asserting that a command renaming is harmless.

## Trust boundary

These are **ordinary mathematical proofs and executable symbolic certificates**, with the inherited numerical-calculus-to-ZFC calibration. There is **no newly compiled Lean or Rocq endpoint for the exact K216 bytes**, nor a new internally checked PA equivalence. The soundness of the symbolic induction rules and their Python implementations remains within the trusted boundary. The archive makes those dependencies and exact inputs available for review. It does not assert unconditional nonhalting, minimality, or universal discovery priority.

## Reproduce offline

Python 3.10 or later, standard library only, with assertions enabled. No network, MILP solver, theorem search, or third-party Python package is required.

```sh
python3 -B verify.py
python3 -B verify.py --runtime --work /tmp/k216-replay
python3 -B verify.py --runtime --secondary-runtime --work /tmp/k216-both-replay
```

The optional work directory must not already exist. The default checks all finite construction, source, blank-start, inherited logical-certificate, and stored-inventory obligations. `--runtime` freshly derives all 6,176 primary runtime cases and compares every ordered receipt. `--secondary-runtime` adds the same fresh proof for the second candidate. Each runtime proof took about two minutes in the construction environment.

An optional independent C++ blank replay is documented in `machine/README.md`. The two native/canonical C++ endpoint receipts are included. The canonical transition table printed in the PDF is generated from the literal machine file.

Rebuild the article with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Integration and provenance

`report.tex`, `report.pdf`, and `sections/` contain the article and full source proof. `machine/` contains the primary machine and literal audits. `source/` and `code/` contain the source inputs and deterministic builders. `evidence/` contains the universal runtime certificates. `secondary/` contains the second candidate. `provenance/` records both direct row recipes and their hashes. `manifest.json` authenticates every delivered file except itself.

The inspected ProveIt commit is `8a1796545e33bf0c4bb52b6c92a6ced17362ca66`. The exact incoming `K217_Dominated_Continuation_2026-10-20.zip` is preserved under `parent/`, including its unchanged nested K218 dominated-rho8 archive. All previous attribution and licensing notices remain intact. See `provenance/ATTRIBUTION.md` and `licenses/`.
