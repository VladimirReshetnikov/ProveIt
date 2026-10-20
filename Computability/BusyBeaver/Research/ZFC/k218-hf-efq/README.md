# HF with explicit explosion: a proof rule and a remaining gap

Consider the proposed replacement of unrestricted rho8 by

```text
HF(A,B,C) = ((C → F) → A) → ((A → C) → (B → C))
EFQ(A)   = F → A,
```

with native `F=R(0,0)=1`, truth code 0, MP, theorem-only GEN, the retained
rho1–rho6/G rows, and the exact gated bundle. The [ordinary findings](findings.md)
prove **closed-theorem double-negation elimination**: any supplied closed proof
of `NN(C)` can be extended to a proof of `B → C` using HF and EFQ, then to `C`
using truth with `B=0`. This does not prove the formula `NN(C) → C` or license
an unproved deduction theorem.

In particular, retained rho6 gives `NN(Z_i)` for `Z_i=Q_i N(Q_i F)`, yielding
a seven-node closed proof of `Z_i`. Conversely, the fragment containing only
truth, HF, EFQ and MP stays within four explicit code families. It cannot
prove even `K(0,F)`. That fragment result excludes neither calibration nor
inconsistency of the full proposed calculus: its quantified bootstrap
already escapes the four-family grammar. **Full calibration remains open.**

One [bounded search](modal-result.json) retained 1,699 universally quantified
numeric schemata in 15.002 seconds: 10 initial schemata, 540 GEN nodes and
1,149 witnessed MP nodes. Its declared limits were 2,500 nodes, syntactic
size 55, and 15 seconds; 1,120 nodes were processed and 1,554,830 ordered
pairs tried. It found none of its identity, K, S, Peirce, formula-DNE or QS
targets. The gated bundle was omitted, and the constructor unifier is
incomplete, including possible native-zero solutions. These absent targets
are bounded observations, not unprovability results.

The [saved derivation DAG](modal-proof.json), [search source](condense.py),
[separate validator](validate.py), [actual validation](validation.json), raw
stdout/stderr and [original freeze](freeze.json) are preserved unchanged.
The validator checks actual schema instantiations, MP and closed GEN; it does
not assume arbitrary formula substitution. The native alias `I(0,0)=0` is
retained throughout. All claims about numerical labels are literal code
claims, not an informal renaming principle.

`opening_encoder` authored the ordinary argument, search and validator,
adapting the earlier bounded constructor search recorded in
[provenance.json](provenance.json) and [its source delta](from-prior-search.diff).
`review_upstream_reflection` independently read the full proof and both
programs, checked every major/minor case in the four-family inversion, and
used an [own inert parser](peer/review.py) to check all 1,699 saved nodes and
the seven-node bootstrap. The [independent receipt](peer/review.json) found
no defect. Neither the peer nor this publication reran the search or a proof
assistant. The accepted [218-state machine](../candidate-k218/README.md)
continues to use its original calculus; this packet has no source price,
transition table, runtime or startup result.

Two reader-only failures remain explicit. The author's
[first validator](history/validator-attempt1/validate.py) treated an identity
mapping as a recursive unifier cycle; the [narrow repair](history/validator-attempt1/repair.diff)
uses simultaneous substitution for the manual proof instantiations. The
search DAG was unchanged. The independent peer's
[first parser](peer/history/own-attempt1/review.py) had a spacing syntax error
and never reached validation; its [tool-result receipt](peer/history/own-attempt1/failure.json)
and [repair](peer/history/own-attempt1/repair.diff) are retained. The receipt
is not represented as a raw process log. [publication.json](publication.json)
maps the exact original files.

To reproduce only the saved-DAG validation, copy the packet to a fresh
scratch directory and run its validator there:

```sh
mkdir /tmp/k218-hf-efq-check
cp -a Computability/BusyBeaver/Research/ZFC/k218-hf-efq/. /tmp/k218-hf-efq-check/
python3 -B /tmp/k218-hf-efq-check/validate.py
```

This reads the stored proof and writes `validation.json` beside the copied
script. It does not run a search. An optional new search is
`python3 -B /tmp/k218-hf-efq-check/condense.py`; it replaces the copied
`modal-proof.json` and `modal-result.json`, so retain the original packet.
Its time cutoff can produce different counts on another machine. Run the
validator afterward to check any newly retained nodes. Python's standard
library suffices.
