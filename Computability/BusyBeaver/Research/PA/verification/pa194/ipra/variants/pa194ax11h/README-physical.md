# PA194AX11H literal table and blank startup

The [first AX11H packet](../../../../../docs/pa194_ax11h_research_2026-11-14/machine/)
delivers the exact 194-state dense table `machine.tm` with SHA-256
`c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a`.
Its `labels.json`, `sites.json`, and `instructions.json` match the
[revised source packet](../../../../../docs/pa194_ax11h_research_2026-11-14_2/machines/PA194AX11H/)
byte for byte. The start and halt controls are dense 0 and 194, or native
74 and 254.

[The row certificate](PA194AX11HRows.lean) checks both transitions at each
working state against the reconstructed native table. [The register
operations](PA194AX11HBoxAgreement.lean) apply to arithmetic `IΣ₁`
models. [The initializer](PA194AX11HInitializer.lean) proves that the
literal blank run reaches the revised source root at time 57,922 in every
covered model. Its site-25 path has one more zero than the primary path,
and the following zero padding is shorter by one bit.

[The site checker](PA194AX11HChecks.lean) compares the instruction used by
the actual revised source interpreter with the instruction read from the
literal trie's site. It checks in-range targets and the physical contract
for each checked instruction. Lean verified the aggregate certificate
for all 3,671 sites.

[The controller theorem](PA194AX11HController.lean) proves that the
literal table halts at a model-valued clock exactly when the revised source
run reaches site 10. It uses the finite site checks as its premise and
checks that site 10 is the unique halt instruction. The
[final literal theorem](PA194AX11HPhysicalFinal.lean) supplies the
checked certificate and proves the model-level equivalence. The
[revised source orbit](README-source-orbit.md) gives the interface to
the scheduler command proofs needed for the iPRA consistency equivalence.

From the repository root, supply the checked [candidate source stage](README-candidate.md)
and [PA1944L model stage](../pa1944l/README.md).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
literal=/dev/shm/pa194ax11h-literal
bash "$variants/pa194ax11h/check-physical.sh" "$literal" /dev/shm/pa194ax11h-source /dev/shm/pa1944l-model
bash "$variants/pa194ax11h/check-controller.sh" "$literal" /dev/shm/pa194ax11h-controller
bash "$variants/check-linear-coverage.sh" PA194AX11H "$literal" /dev/shm/pa194ax11h-coverage
bash "$variants/pa194ax11h/check-physical-final.sh" /dev/shm/pa194ax11h-controller /dev/shm/pa194ax11h-coverage /dev/shm/pa194ax11h-final
```
