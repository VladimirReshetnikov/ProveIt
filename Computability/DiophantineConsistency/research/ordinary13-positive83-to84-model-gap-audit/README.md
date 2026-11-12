# Positive 83 to 84: carrier, positivity and model gap

This is a bounded, source-pinned mathematical audit, not a Lean-elaborated
model map, `PolynomialBridge`, or iPRA endpoint. The positive 83 graph has
input w at position 6; the 84 graph has X there. All other positive positions
and the compact port order agree. Their literal rows differ by precisely the
83 gate `X=q*w`, the two 84 gates `E*q` and `U*gamma+E*q`, and the consumer
of that sum. The checker establishes this exact row comparison and proves the
following carrier identity in the free integer polynomial ring:

```
X = q*w, E = X*Y, U = Y*q²,
gamma_prime = gamma_old+w,
U*gamma_old + E*q = U*gamma_prime.
```

Under that substitution, all unchanged residual rows agree, and therefore
so do the two four-square outputs. This is ring algebra; interpreting the
subtractions and all coordinates in an arbitrary model requires positive
witnesses and justified casts.

## From an 84 zero to an 83 zero

With `q>0`, `X>0` and `q∣X` in the model naturals, choose `w>0` with
`X=q*w` and set `gamma_prime=gamma_old+w>0`. The exact ring identity then
preserves every residual. The model client must still extract the stated
facts from the *actual 84 zero*, construct the positive quotient, and prove
the literal evaluation and positivity maps.

One proposed route to `q∣X` uses `X=Exp.exp R`, `q∣3*X`, the actual
represented compact Mersenne beta `q=(Exp.exp d-1)*J+1`, and `d≥4`.
The source theorem `ArithmeticAdaptiveMersenne2011.cancel_three` has exactly
these conditional arithmetic inputs after rewriting the power. It does not
establish them from this 84 literal. A scalar control `q=3, X=8` has `X` a
power of two and `q∣3X` but `q∤X`; it is not a graph zero and does not have
the required compact Mersenne representation. A direct proof of `q∣X` or
another positive-witness construction could replace this route.

`Compact44.FreeJPowerFinish.graph_power` is a source theorem about a
12-input original literal zero with explicit positive port/input hypotheses;
it cannot be applied directly to the 84 graph. The proposed 84→87→original
model maps, exact port casts, and that endpoint's providers remain open. The
older 14-input source-only `ModifiedCarrierFacts.compact_beta_divides_X` is
a useful conditional model interface, not a graph-specific 13-input proof.

## From an 83 zero to an 84 zero

Here X is already `q*w`; the required old coordinate is the model-natural
`gamma_old=gamma_prime−w`. A ring subtraction is insufficient: to make this
coordinate strictly positive one must first prove `w<gamma_prime`, then use
that inequality to justify the natural predecessor and its difference-ring
cast. The isolated values `gamma_prime=1,w=2` show positivity of the two
separate inputs alone does not imply this inequality; they are not claimed to
be part of a graph zero.

The separately source-reviewed but **unelaborated**
`ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance` proposes this
inequality directly, without a new lower bound for the Pell projection
quotient and without needing `X=Exp.exp R`. It takes the natural facts

```
U>0, Y>0, 1≤q, X=q*w, a=X*Y+Y, H=4*a+3,
3≤R, c=ycoord R a, d=xcoord R a,
k=R+1+U*W,
U*d+H*k = U*(X+a*c)+H*(U*gamma_prime+R+1).
```

It is essential that d and c are the x/y coordinates for the *same* actual
oriented main root. The proposal uses a Pell ordinate lower bound and
`d>(a+1)*c` to rule out `gamma_prime≤w` from the subtraction-free balance.
This is a conditional fact-level source theorem: the 83 graph must still
supply each premise, and the theorem plus its imported model/provider chain
has not been compiled or checked in this task. In particular, older notes
which say an additional quotient-growth lemma is unavoidable describe one
possible proof route, not a prerequisite for using this newer direct bound.

For a graph client, the 83 first and main norms, actual no-`E*q` main-root
orientation, compact rank window and early first-index congruence must be
bound to the same tuple. `P72Exact.indices_ordinary` then needs its full
first/main/strong/direct-auxiliary premises and the graph's same strong
coordinate i to turn the congruence into `2*n=R+1` and identify the main
index R. With its same recurrence quotient v, set `W=4*X*q*s*v`; from
`Y=q³*s` and `k=R+1+4*X*Y²*v` obtain `k=R+1+U*W`. The actual signed
main-root orientation must yield the displayed natural balance before the
gamma lemma applies. Compact rank positivity supplies the needed `R≥3`
once those source facts are correctly instantiated.

The source-only `EtaNaturalGraphEarlyIndexDraft.compact_early_index` and
`EtaZeroGrowthDraft.power` concern the exact 85 prototype with the same
no-extra-term main carrier; their results are not automatically facts about
83. Its first carrier is B, whereas 85/81 use B′. One possible route is the
separately unproved easier 83→81 positive-companion zero map, then the
positive-81→85 forward adapter documented in the sibling
`ordinary13-positive81-to83-model-gap-audit`. This retains the same
non-first coordinates but may replace r, and all intermediate literal/model
bindings still need Lean proofs. Alternatively, bind the needed first norm
and early-index facts directly to 83. Neither route justifies applying the
extra-`E*q` residue-90 graph wrapper to the 83 main root.

`research/ordinary14-84-85-ring-client-draft/RingComparison.lean` illustrates
the same local algebra in a different 14-input graph; it is not a proof of
this exact 13-input graph's model map. No positive-coordinate equivalence,
endpoint, fixed-port source/PDF binding, or provider/axiom ancestry follows
from this audit or its receipt.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive83-to84-model-gap-audit/check.py
```
