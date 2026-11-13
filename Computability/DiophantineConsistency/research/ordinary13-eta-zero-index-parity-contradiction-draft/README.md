# Eta-zero index/parity contradiction: fact-level source draft

`EtaZeroIndexParity.lean.src` proposes a contradiction for model-natural
arithmetic data satisfying the **full hypotheses** of the eta-natural
`indices_ordinary` draft, specialized to `c=Y*k` (eta zero). The complete
first-index and congruence conditions, main Pell index and norm, strong norm,
auxiliary offset equation, positivity assumptions, and rank bounds are written
literally in its theorem signature. No graph valuation or equation zero is
assumed or constructed.

The intended composition is:

1. The eta-natural index draft gives `m=R` and `2*n=R+1`.
2. The latter implies `R` is odd. The first-index hypothesis writes `k` as
   twice a natural Pell ordinate, so `c=Y*k` is even.
3. The separately drafted model parity theorem gives
   `c=ycoord(m,a) ≡ m=R (mod 2)`, so `c` is odd: a contradiction.

The file imports `P72ExactEtaNatural` and `PellOrdinateParity`, proposed
module names for the two pinned `.lean.src` drafts listed in `result.json`.
Neither import is an established object provider. Their own transitive
source/provider requirements and any build ordering remain open. All three
sources are **unelaborated**: this packet provides a proposed modular proof,
not a Lean-verified theorem, and its checker cannot rule out elaboration or
hidden dependency problems.

The arithmetic premises must still be extracted from the specific hypothetical
eta-zero graph in the intended model, including factor-unit cuts, natural
root orientation, the congruence/rank and first-index witnesses, the strong
norm and its signed auxiliary-offset conversion. The graph's fixed ports,
zero maps and iPRA proof translation are also separate. No graph modification
or operation saving is claimed here.

From this directory, reproduce the lexical receipt with

```
python3 -I -S -B check.py > /tmp/eta-zero-index-parity.json
cmp result.json /tmp/eta-zero-index-parity.json
```

The checker pins the two drafts and verifies that every original index
hypothesis is transcribed identically after replacing `c=eta+Y*k` by
`c=Y*k`. It does not run Lean or verify the proof.
