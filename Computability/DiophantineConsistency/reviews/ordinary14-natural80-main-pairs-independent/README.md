# Independent review: natural-80 literal main-pair draft

The [main-pair draft](../../research/ordinary14-natural80-main-pairs-draft/README.md) states mathematically consistent literal root and right-side bindings, under the explicit port representations and guard gap shown in its source. Its proposed composition with the own-zero and gap drafts does not assume gamma positive. The original receipt and the independent receipt below reproduce. This is a source and external algebra review, not Lean elaboration or a checked model theorem.

The independent checker pins 13 relevant sources and checks all 74 literal graph rows against the candidate JSON, including the typed `U`, `a`, `c`, `Dstar` and main-factor field selections. It checks 39 specifically named rows from the beta port through `q`, `X`, `Y`, `R`, the main root and its right side. An exact sparse integer-polynomial calculation independently verifies the cut

```
Dstar = U*(X+a*c) + H*(U*gamma+R+1) - H*k,
```

and the expanded right-side identity `U²*(1+(H+a²)*c²)`. Thus, after the source's beta, MC and MF representations and subtraction casts are valid, the proposed pair `(P,N)` has the same signed value as the literal root. No sign condition on `P-N` or on gamma is needed for a *signed-pair equivalence*.

The beta representation alone suffices for the proposed right-side cut. The root cut also uses represented MC and MF and `F+alpha<q`, with no K0 representation or MC/MF inequality. In the intended natural model, `q=1+J*beta>=1`, so `q²>=1`; the gap implies `F<=q`. These bounds justify casting the natural truncated subtractions `q²-1` and `q-F` as ring subtractions. The gap matters: for example, `q=1`, `F=2` gives natural `q-F=0` while ring subtraction gives `-1`. The explicit hypotheses are therefore essential to this proof route, even though a different argument could use weaker bounds.

For the norm step, the source theorem `unit_square_norm` yields `magnitude(rootPair)² + rhsPair.2 = rhsPair.1` from the main factor being the positive unit. The cited pair-equivalence theorem preserves magnitude, while `Equivalent rhsPair (rhs,0)` means `rhsPair.1 = rhsPair.2 + rhs`. Cancellation yields the proposed magnitude norm; literal equality of `rhsPair` to `(rhs,0)` is stronger than needed. The draft's final client obtains the main unit and guard gap from source-only 80-own-zero drafts and explicitly assumes all four port representations plus `beta>0` and `K0>0`; its signature has no gamma-positivity premise and no MC/MF inequality premise. Those imported own-zero and gap statements are conditional source proposals and have not been re-proved or elaborated by this review.

The checker inspects declaration shapes and proves only the displayed external polynomial cuts. It does not establish that the `simp`, `ring`, `rw`, `nlinarith`, pair-evaluation coercions, or model instances elaborate, or that the transitive providers and axioms are coherent. Nor does the proposed norm by itself furnish the rank-window or Pell premises, prove an iPRA endpoint, or bind symbolic coefficients to bytes or the PDF. Its three `#print axioms` commands have not been executed.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-main-pairs-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-main-pairs-independent/result.json
```
