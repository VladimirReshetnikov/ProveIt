# Proposed concrete current-port and valuation casts

This is an **unelaborated source-only composition** of the two preceding
forward-index and generic rank-cast drafts. Its proposed final theorem
`ring_half_at_parent_zero` has only the actual positive-shifted 71/60 zero
as an explicit premise and concludes the `2*rank<c` inequality for the
same shifted difference-ring valuation. In particular it is intended to
discharge both cast hypotheses of the prior forward client. **No Lean run
has checked that it succeeds**; until then those casts and the final bound
remain unproved in this new client.

The proposed steps are:

1. Compare the actual integer ports cast into the difference ring with
   `ι` of the model-natural tuple
   `[beta,K,lowPort,highPort+beta]`. The fourth coordinate contains the
   source high-mask shift **once**.
2. Use that tuple and the same shifted valuation to express `core.q` and
   `core.c` as casts of the natural q and c. The latter uses only addition,
   multiplication and powers.
3. Obtain `F<=q` from the forward client's positive natural scalar gap;
   `1<=q` and `1<=q²` follow from its definition. Apply the generic bounded
   subtraction rank-cast lemma, and use `beta*J=q−1` in the difference
   ring to match the literal `Carrier65.core.rank` expression.
4. Apply the earlier `ring_half_of_casts` using the proposed exact rank/c
   equalities.

[`CurrentPortCast.lean.src`](CurrentPortCast.lean.src) uses local imports
`ForwardIndex` and `RankCast` as names for the two predecessor `.lean.src`
files if later materialized. They are not installed Lean modules by virtue
of this packet. The concrete `simp`, cast, finite-index and rank rewrite
steps may need correction when elaborated. Existing theorem/provider and
external graph-byte limitations of all three drafts remain in force.

The companion [checker](check.py) pins the source and checks the current
port tuple declaration, theorem markers and explicit use of both proposed
cast proofs. It does not parse Lean, validate tactics, prove any cast,
authenticate transitive providers, or run a build. The literal 72/46 graph
evaluator, auxiliary unit extraction, positive witness maps, two-way zero
equivalence and iPRA endpoint remain separate obligations.

```
python3 -I -S -B research/current2011-shear-current-port-cast-draft/check.py > /tmp/shear-current-cast.json
cmp /tmp/shear-current-cast.json research/current2011-shear-current-port-cast-draft/result.json
```
