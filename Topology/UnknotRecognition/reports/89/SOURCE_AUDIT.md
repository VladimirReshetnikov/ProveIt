# Targeted source audit

Date: 12 October 2026. Repository: `VladimirReshetnikov/ProveIt`.

This is a targeted source inspection, not a complete repository audit. The principal pinned code reads used commit `1c0383bd8fdb3865e97f9fbc90171f770106140e`. The default branch was evolving during the research, so the material below is not described as a full simultaneous snapshot of every path.

## Maintained material inspected

- `Topology/UnknotRecognition/fast/fastunknot/normal_parallelity.py`, pinned code read; blob `22cf15ffa11ca85e6a6c350f5d217f1649a01ea2`. Inspected polygon corner systems, free-edge endpoint construction, weighted queries, and fibre-cover conventions.
- `Topology/UnknotRecognition/fast/fastunknot/weighted_orbits.py`, pinned code read; blob `a1bc2e239109cf2cd3481e439c8ac6d49276e798`. Inspected additive half-open inputs, compressed histogram output, certificate structure, generation, and verified unweighted-trace reuse. A certificate contains its own histogram; the new adapter consumes that checked histogram, not an unchecked parallel output field.
- `Topology/UnknotRecognition/fast/fastunknot/weighted_orbit_verify.py`, pinned architectural read; blob `c8a05deff183e490cbafed0978654c390774a100`. The public signature `verify_weighted_orbit_certificate(size, pairings, weight_intervals, certificate, *, dimension=None, check=None)` was additionally confirmed by code search at `361f705d1b858c15bf6adc38119324ecba627dbf`. Native execution remains unperformed.
- `Topology/UnknotRecognition/synthesis/cut_cells.tex`, default-branch prose read; blob `dc12b1a58aedaed78f00b63109b0aa5214832ca1`. Full raw-cut attaching charts and compressed source reconstruction are prior results.
- `Topology/UnknotRecognition/synthesis/parallelity.tex`, default-branch prose read; blob `d7293976bea14fce6b4848bf6a2d7a20134c2491`. All-dimensional source parallelity, the 30T inherited-core and 66T port bounds, and the patterned-admissibility limitation are prior results.
- `Topology/UnknotRecognition/README.md` and the incoming-directory README were inspected for project scope and delivery placement. Historical full-suite counts were not reused as evidence for this package.

## Incoming material

The incoming directory was inventoried through the connected GitHub tools. Its corner-aware, interface-homology, marked-parallelity, four-copy, cancellation, and reduction archive names were visible. Those archives were **not all downloaded or audited**.

The substantive predecessor was read through its prior Library TeX/PDF: *Corner-Aware Boundary Kernels for Compressed Unknot Hierarchies* (12 October 2026), incoming archive `ProveIt_Corner_Aware_Boundary_Kernels_2026-10-12.zip`. Its source pin is `ed166080d7db14dd7a91d07788996f02947dd92a`. The inspected material includes the O(p log p) count compiler, silent-orbit correction, corner-sensitive surgery formula, fixed-interface continuation, and signed-pairing enumeration. These are expressly credited as prior results.

The prior *Bounded-interface integral homology* report was inspected only at the abstract/scope level, to distinguish that independent line of work from the present compiler.

## Primary external references

Agol, Hass, Thurston, *The computational complexity of knot genus and spanning area*, arXiv:math/0205057v2: weighted orbit theorem and the meaning of compressed multiplicity output. The relevant PDF page was also visually checked.

Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*, arXiv:2607.23350v1 (25 July 2026): hierarchy framework and Section 9's separation of iteration counts from operation costs.

No exhaustive literature-priority claim is made. “New” means proved here relative to the inspected material. No source-geometric soundness review of the entire recognizer, full upstream regression run, or native performance benchmark was performed.
