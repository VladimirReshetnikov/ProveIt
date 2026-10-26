# Root review of the signed auxiliary Pell residue

Author: `/root/circuit_reduction`. Independent reviewer: ROOT.
Result: PASS for the full unbounded signed divisibility theorem.

ROOT read every line of the102-line module and30-line focused checks,
and compared their statement with section2 of the accepted ordinary
thirteen-variable proof.

| Source in `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `SignedPellResidue.lean` | `53a42a0e1fcf6b054b70d6aecc9b5d9684a5a0530c1a920ac4628e169104ae2b` |
| `SignedPellResidueChecks.lean` | `05e53c892429a6416ba29fec9769d09cfa10f727ff377bc61486b6db76fa0f01` |

The public theorem has exactly the integer premises

```text
2 <= S
S^2*V^2 - (S^2-1)*y^2 = 1
y congruent to 1 modulo4
```

and concludes `4*S^2` divides `y-1`. It assumes neither a sign nor a size
bound for V or y. The proof classifies the natural absolute-value Pell
pair. Divisibility of the first coordinate by the base forces an odd
index, using the existing checked index congruence. A proved two-step
recurrence gives the full odd-ordinate residue modulo4S². Restoring either
sign of y gives the two possible residues. The supplied modulo-four
condition excludes the negative one, leaving the claimed divisibility.

The focused checks include V=-13,y=-15 at S=2, the higher y=209 solution,
and the genuine y=15 solution disproving the conclusion if the
modulo-four premise is removed. Thus the signed case and the necessary
residue premise are tested directly.

ROOT freshly compiled the module with `lake env lean ... -o ...` and ran
its focused checks; both passed. The four printed theorem-axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`. No admission,
new axiom or native-decide extension occurs. This uses the existing
source-identical Pell dependency cache, rather than claiming a fresh
rebuild of all those ancestors.

This proves the residue used to recover the deleted transport witness.
Its integration with the actual thirteen-coordinate polynomial, the full
soundness map, fresh-seed completeness and native consistency calibration
remain required. No completed Con(ZFC) endpoint is asserted here.
