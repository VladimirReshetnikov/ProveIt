# Additional research and scoped negative evidence

The completed result is the 224-state machine in `../portable/machine`.
These files explain additional formalism choices and failed shortcuts; they
are not substituted for the frozen construction or its full proof chain.

## Mathematical notes

- `conditional_k_calibration.md`: conditional K is equiconsistent with
  unconditional K and ZFC, using a two-marker hereditary-domain interpretation.
- `native_fixed01_calibration.md`: a fixed native input/output choice `(0,1)`
  has the required consistency calibration, including codes 0 and 1, using
  a raw-nonempty upper interpretation.
- `k_schema_obstructions.md`: the rational-order model obstructs deleting K's
  support clause; other logically equivalent shapes are separated from
  unproved weakenings.

The successful K-specific equality interpretation and exact proof-enumerator
adaptation are in `../portable/theory/k_equality_helper_extension.md` and
`../portable/theory/enumerator_adaptation.md`.

## What was measured

| Source alternative | Best relevant source DAG count | Completed smaller machine? |
|---|---:|---|
| Four-pair fusion of the inherited bundle | 211 | No; 225 states |
| Closed existential reassociation | 210 | No; 225 states |
| Canonical membership-code equality helper and final layout | 210 | Yes; 224 states |
| Conditional K direct construction | 212 | No |
| Conditional K with fixed roles `(0,1)` | 219 | No |

These are distinct-subtree counts, including primitive leaves. The direct
conditional screens do not establish working-state counts. Formula length
alone does not determine decoder sharing or state-fold compatibility.

## Negative machine evidence

`reset_counterexample.json`, `blank_reset_hazard.json`, and
`register_invariant_audit.json` retain the exploratory evidence for specific
proposed shortcuts. These JSON records refer to the state labels and basis
identified within the record. They are not claims of exhaustive lower bounds.

In particular, shortening the current eight-zero reset to seven is invalid.
The same valid-frame counterexample was also checked against the final table:
the source occurrence `11101001001000000 / CD1`, with all logical registers
zero and one zero-valued spare, returns correctly in 586 steps under the final
224-state table. Deleting inherited state K50 and changing K34/read0 to target
K75 yields the wrong clean frame after 662 steps. This mutation is separate
from the accepted K157/K191 fold and is not applied to the distributed table.

Search heuristics are intentionally not execution dependencies. The clean
builders deterministically reproduce the accepted source and machine from
pinned bytes, and the independent checkers verify their claimed effects.
