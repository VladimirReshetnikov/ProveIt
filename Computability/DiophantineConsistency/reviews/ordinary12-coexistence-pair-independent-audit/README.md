# Independent audit of the 70-source coexistence pair

The independent read-only audit exited 0 in tool session 25480. It verifies
the evidence packet from commit `641a64c157`, the recorded launcher exit 0,
and the pair's two successful 70-row sibling states. It independently matches
the two runs' source, object, log and axiom-report hashes for every row, and
reruns the existing comparator read-only with exit 0 and `MATCHED_PASS`.
No Lean compiler was invoked by this audit.

The audit checks the 154 committed evidence files, both copied terminal and
state records, all 140 copied compiler logs and all 140 actual output objects,
the complete output-file inventories, and both 920-entry direct companion
guards. It checks each recorded direct dependency's current hash and the
fresh-project dependency ordering, all 70 snapshot and corresponding
workspace source hashes, the Lean executable and driver pins, all six review
receipts, 1,540 Foundation inventory entries, and 14,764 declared external
guard paths. The provider guard contains 430 present paths and 14,334 recorded
absences. These checks are point-in-time; they do not close all mutation races
or inspect dependencies outside the recorded inventories.

Each sibling's logs contain the same 12 warnings: eight about unused
automatically included section variables, two about unused variable names,
one unused simp argument and one deprecated `push_neg` tactic. The audit
rejects any other warning classification and searches all compiler logs for
errors, `sorry`, `sorryAx` and admissions. None were found. There are 21
printed axiom reports per sibling; their only named axioms are `propext`,
`Classical.choice` and `Quot.sound`. Each of the three endpoint reports lists
those three, with no `sorryAx`. The warnings do not indicate an admitted proof
or alter the stated coexistence claim. These are Lean metatheory dependencies,
not asserted axioms of object-level iPRA.

The target `FreeJProviderChecks` checks coexistence of the model difference
ring, free-J residual and cleared signed-pair identity. It does not prove the
signed graph transport, denominator integrality, fixed-port calibration or
either consistency direction in iPRA. Both siblings use the same historical
Foundation/package provider and compiler. Package-transitive and dynamic
ancestry remain inherited, and the original Foundation wrapper's outer exit
was not captured. Disk monitoring was sampled rather than a quota or continuous
reservation. The recorded original launcher outer exit is a preserved tool
observation, not newly witnessed by rerunning that process.

The phrase *source current* applies to the **70 pinned source paths**: at
the audit's workspace HEAD, all 70 still matched the frozen bytes. Two later
merged files, `ArithmeticOddOrdinateResidue.lean` and
`ModelThirteenRestoration.lean`, were outside that frozen closure and were
not compiled or checked by this pair. Their current hashes and the audited
HEAD are recorded in `CHECK.json`; this result is not a build of every source
now present in the repository.

`CHECK.json` preserves the artifact counts, warning and axiom censuses,
matched-row digest, and historical inputs. `terminal-observation.json` binds
the observed audit exit to the receipt. Run the read-only audit from the
repository root while the original temporary source, provider and output
trees remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-coexistence-pair-independent-audit/audit.py
```
