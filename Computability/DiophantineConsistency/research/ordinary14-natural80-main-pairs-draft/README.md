# Natural 80 literal main-pair bindings: source proposal

`Natural80MainPairs.lean` proposes **unelaborated source-only** literal
main-root and right-side bindings for the partially shifted 74 valuation of
an 80 zero. None of the graph, ring, pair, guard-gap or own-zero drafts has
been compiled here; the `simp`/`ring` cuts and truncated-subtraction casts
may require repair. The checker pins the source and dependencies and runs
500 finite literal arithmetic controls, including 250 with gamma zero. It
does not prove a model theorem, run Lean, or audit axioms.

`rhs_eval`/`rhs_rep` propose that the 74 main right side represents

```
U²*(1+(H+a²)*c²),
U=Y*q², a=X*Y+Y, c=eta+Y*k, H=3+4*a.
```

Only the beta port's representation by a model natural is assumed for this
cut. `root_eval`/`root_rep` propose representing the literal signed Dstar
by `(P,N)`, where

```
R=(alpha+(q−F)*b)*(q²−1)+J*(MC+MF*q),
P=U*(X+a*c)+H*(U*gamma+R+1), N=H*k.
```

Those cuts explicitly assume beta, MC, and MF port representations and
`F+alpha<q`. The gap justifies interpreting `q−F` as natural subtraction;
`q>=1` justifies the `q²−1` cast. There is no positive-gamma premise.

The source's `norm_from_representations` accepts equivalence of the RHS
signed pair to `(rhs,0)`, rather than demanding literal pair equality.
`norm_of_80_zero` proposes composing those cuts with the separate 80 own-zero
units and guard-gap drafts. It explicitly requires representations of all
four ports, `beta>0`, and `K0>0`; MC/MF inequalities are not needed merely
for this norm binding. The rank-window step still requires separate MC/MF
inequalities, and the main norm must still be connected to the
[narrow gamma contradiction](../ordinary14-natural80-gamma-narrow-draft/)
and [fact-level Pell/rank premises](../ordinary14-natural80-gamma-premises-draft/).

The included three `#print axioms` commands have not been executed. This
packet does not establish Lean elaboration, an iPRA proof, a symbolic-to-byte
coefficient equality, a PDF binding, or a fresh provider replay.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-main-pairs-independent/README.md)
checks the literal cuts, subtraction bounds and explicit assumptions without
elaborating the proposed declarations.

```
python3 -I -S -B research/ordinary14-natural80-main-pairs-draft/check_source.py > /tmp/natural80-main-pairs.json
cmp /tmp/natural80-main-pairs.json research/ordinary14-natural80-main-pairs-draft/result.json
```
