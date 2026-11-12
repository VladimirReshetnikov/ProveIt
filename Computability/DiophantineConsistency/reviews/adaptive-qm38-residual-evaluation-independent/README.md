# Independent source review: proposed QM38 evaluation identity

The [residual-evaluation draft](../../research/adaptive-qm38-residual-evaluation-draft/README.md)
and this separate source checker reproduce. The proposed statements have the
intended parent/child indices, ordered sum and specialization. No concrete
source-level mismatch was found; this is not a Lean elaboration or an
all-model theorem.

The child residual source contains the complete pinned 160-row child schedule
and its 29 residual names in the parent's 31-residual order with indices 20
and 24 removed. The checker independently reconstructs the ordered expression
DAG and confirms that the literal output is exactly the left-associated sum
of those 29 squares, supporting the proposed `sum_eq_literal := by rfl`.
Each of the 29 proposed residual lemmas was checked in its own theorem block
against the corresponding parent and child indices. The two additional lemmas
target the removed parent indices 20 and 24 after extension. The separate
[external graph review](../adaptive-square-sums38-independent/README.md)
checks those 29 polynomial identities and the two vanishing differences in a
formal integer polynomial ring; it is not a substitute for the Lean proofs.

The proposed `evaluation_identity` rewrites each literal to its ordered sum,
rewrites all 29 retained residuals and two deleted residuals, and removes the
zero squares. Its declared ports are arbitrary integers. The proposed
`evaluation_cut` specializes this identity to `CurrentWindowCarry2011.ports`,
matching the premise in the independently reviewed [conditional model
transfer](../adaptive-qm38-conditional-model-independent/README.md).

All 29 `simp`/`ring` scripts, both dropped-residual proofs, the `rfl`, the final
rewrites and axiom reports are unexecuted in Lean here. Reduction size,
heartbeats, imported provider/companion ancestry, model transport and the
native/reference endpoint remain to be checked in an appropriately guarded
build. No proof of the new iPRA equivalence or formal PDF binding follows from
this source review.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm38-residual-evaluation-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm38-residual-evaluation-draft/source-result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-qm38-residual-evaluation-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-qm38-residual-evaluation-independent/result.json
```
