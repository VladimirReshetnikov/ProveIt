# Independent review of the current-port C-fold Cal replay

The pinned author packet is `research/adaptive87-current-cfold-cal-fact-replay/`. Its checker and the separate source-interface audit at `research/adaptive87-current-cfold-index-power-interface-audit/` both reproduce. I found no concrete mathematical or source-signature mismatch in the standard-integer replay, conditional on the cited Pell and rank theorem statements. The check is not a new Lean proof or an all-model/iPRA bridge.

The review traced the stated Cal hypotheses through the positive main orientation and `q⁴ | R+1−k`, including the case 3 divides q. The first Pell classification retains the same tau, k and index n; the main classification retains the same positive d, c and index p. The recurrence quotient gives `k=2n+4*(X*Y²)*w`; because `Y=q³*sY`, it is compatible with the q⁴ rank window. The complete `P72Exact.indices_ordinary` declaration is checked against the pinned source, including its two natural absdiff expressions. These are `|V|` and `|V+u|` at the same graph witnesses even when either signed difference is negative; no extra factor of Delta enters the strong-witness input. Its conclusion supplies `p=R` and `2n=R+1` for the same indices.

With `r=n−1` and `W=4*X*q*sY*w`, the `power_bound` arguments match the source declaration, and `q|3X` with q>=47 supplies X>=16. The projection uses the same main d and c at index R. The independent checker verifies the relevant q-balance reduction in a free integer polynomial ring and checks signed absdiff controls. The final comparison uses representatives `3X,3*2^R` strictly below `H=4a+3`; it does not assume 3 is invertible modulo H. The claimed inequality `2^R>=q²` then follows from `R>=q³` and q>=47.

The author source checker pins the exact 88-row graph wiring; the mathematical replay is a standard-natural application of existing source theorem statements, not a kernel-checked application to this graph. Finite controls and source hashes do not replace a complete historical provider audit. Combining Cal with the separately reviewed parent/child positive-witness maps yields an ordinary positive-integer existence comparison under their recorded port hypotheses; it does not establish an all-model transfer, a current-source Lean theorem, iPRA proof existence, or every possible formal interpretation of Con(ZFC).

Reproduce from the DiophantineConsistency directory:

```sh
python3 -I -S -B reviews/adaptive87-current-cfold-cal-fact-replay-second-independent/check.py > /tmp/adaptive87-cal-independent-current.json
cmp reviews/adaptive87-current-cfold-cal-fact-replay-second-independent/receipt.json /tmp/adaptive87-cal-independent-current.json
```

No Lean/build/staging was performed and no author packet was changed.
