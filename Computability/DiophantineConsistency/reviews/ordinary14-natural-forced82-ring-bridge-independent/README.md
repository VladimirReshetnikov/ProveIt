# Independent source review: natural 82-to-86 bridge

The [bridge draft](../../research/ordinary14-natural-forced82-ring-bridge-draft/README.md) states the correct changed-valuation relationship for the two pinned literal graphs, and its proposed model-level existence theorem explicitly assumes the missing three-predecessor condition. The original checker and the independent receipt below both reproduce. No Lean elaboration or semantic model theorem has been checked.

The independent receipt reads both Lean graph blocks and compares every row, variable slot, port slot and selected field tuple to the corresponding pinned JSON. The 86 graph has the three nodes `f=n_f+1`, `r=n_r+1`, `y=n_y+1`; evaluating it after subtracting one at slots 3, 8, 11 makes these nodes exactly the unshifted inputs in the 82 graph. It also replaces the 86 graph's `zeta=n_zeta+1`, `k=eta+zeta`, `g52=k-R`, `r0=g52-1` by `kbase=eta+n_zeta`, `k=kbase+1`, `r0=kbase-R`. Both substitutions are exact commutative-ring identities, including for arbitrary signed integer ports. All other shared DAG rows match after the three node renamings, giving the mathematical changed-valuation identity by structural congruence. This argument does not assert equal outputs at the same valuation.

The model draft's `Related v82 v86` requires the 82 entries at the three slots to be successors of the 86 entries, with all others equal. The source proposes an `InternalZero` equivalence for related valuations, an incrementing 86-to-82 witness map, and an existence equivalence that **takes as a parameter** the assertion that every 82 zero has those three predecessors. It does not establish that assertion from the graph or port hypotheses. The model section assumes `𝗜𝚺₁`; the arbitrary-ring identity itself does not require it.

This review examines source declarations and mathematical graph correspondence, not whether the listed `simp`, `fin_cases`, rewrites, instances, or `rfl` proof steps elaborate. It does not establish the assumed predecessor property, the natural-86 endpoint, an internal iPRA proof, provider/axiom closure, physical-port binding, or the displayed PDF equation.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-ring-bridge-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-ring-bridge-independent/result.json
```
