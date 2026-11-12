# Actual residue-main rank-congruence source draft

This packet proposes a model-level route from the **actual 90-row
residue-adjusted main root** to the q⁴ rank congruence and the separate early
first-index wrapper. **No new source, proof tactic or imported provider here
has been elaborated by Lean.**

The draft represents the graph's signed main root by natural pair parts

```
P = U*(X+a*c) + H*(U*gamma + (R+X*Y*q) + 1),
N = H*k.
```

The actual graph main norm and `F≤q` give a natural magnitude norm for
`(P,N)`; `F≤q` is the explicit truncated-rank representation premise. The
source proposes calling `DirectMainNorm.direct_main_orientation` with the
**adjusted rank `R'=R+X*Y*q`**, then turns the resulting positive balance
into `FreeJMainOrientation.FreeJMainCongruence` for an explicitly constructed
12-coordinate **arithmetic tuple**. It calls `rank_congruence_from_main` on
that fact; it does not assume a free-J graph zero or an equality with the old
`core.z` first root.

A further source theorem proposes combining this rank congruence with the
actual graph's first signed norm, its model-natural quotient, and the separate
`ResidueFirstIndexModelDraft.early_index_of_natural_norm` wrapper. It retains
as explicit graph facts a positive J/beta, positive X, `F+alpha<q`, `24≤R`
and the rank window. The proposed conclusion is the **early** q⁴ index
congruence and `k=2n+4Qw`; it does not assert the later exact index.

Model casts and inequalities for the symbolic/physical compact ports, the
graph norm and positivity drafts, transitive provider provenance, later exact
index, Bezout, projection, parent bridge, physical PDF and internal iPRA
endpoint all require separate proofs and Lean verification. This source
accepts a represented natural port tuple and does not authenticate a fixed K.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-main-congruence-model-draft/check.py | cmp - research/ordinary13-residue-main-congruence-model-draft/receipt.json
```

The read-only checker pins the relevant graph/source interfaces and receipts,
replays their deterministic checks, and controls the actual signed-main pair
and arithmetic-balance identity on finite tuples. It never runs Lean or stages.
