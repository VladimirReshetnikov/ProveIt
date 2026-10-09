# Source audit and relation to previous work

## Fixed repository state

The audit uses commit **3a90fb34146c915328ab8eac6250cc2514f74ed0** of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/3a90fb34146c915328ab8eac6250cc2514f74ed0/Topology/UnknotRecognition), dated 9 October 2026.

The implementation, synthesis, and incoming tree were inspected at this same revision. All 566 materialized baseline fast/ files match their Git blob identities and remain byte-identical in the supplied snapshot. Seventeen historical oracle files are also pinned. The provenance record lists the actual files and their roles.

The live repository may have changed after this pin. No external repository modification, push, pull request, or incoming-package rewrite is part of this delivery.

## What was already implemented

| Existing area | Relevant source | Consequence for this continuation |
|---|---|---|
| Canonical diagram exterior and independent replay | fast/fastunknot/diagram_exterior.py and diagram_exterior_verify.py; synthesis/diagram_exterior.tex | Diagram provenance is already an implemented entry point. It must not be reported as missing. |
| Checked local triangulation changes | fast/fastunknot/pachner23.py, pachner32.py, their independent verifiers, boundary_shellings.py | Legal move construction and manifold validation are reused rather than claimed as new. |
| Primitive cocycles and gauge optimization | fast/fastunknot/normal_cocycle.py, cocycle_span.py; synthesis/cocycle_seeds.tex and related gauge sections | Transport avoids repeating this extraction after every move; it does not invent the seed method. |
| Euler optimization on a minimum-span face | synthesis/cocycle_euler.tex and cocycle_face.tex | Optimizing a representative in a fixed triangulation does not solve the escape problem. |
| Coherent obstruction and escape | synthesis/coherent_obstruction.tex and coherent_escape.tex | The eight-tetrahedron genus-two fixture and previous fresh-gauge escape motivate the exact transport continuation. |
| Compressed component and essential-disc queries | fast/fastunknot/normal_surface_components.py and normal_disk_kernel.py | The new source consumer uses the general component kernel, including split fibres. |
| Weighted interval orbit replay | fast/fastunknot/weighted_orbits.py and weighted_orbit_verify.py | Orbit algorithms and their maintained certificates are dependencies. New work constructs and decodes a marked-order query. |

The prior cocycle-reuse audit contains 84 source cases. The compact supplied fixture copies only those source records, in their original order; comparison with the full pinned source record was exact. A sixteen-crossing cutoff selects the measured 82 cases.

## Incoming packages read

The twelve original incoming ZIP files were inventoried and their bytes matched the pinned repository blobs. Ten concern this task:

| Package | Relevant scope and continuation boundary |
|---|---|
| unknot_quadrilateral_support_kernel_20261009.zip | Support-sensitive normal kernels; geometric source and search obligations remain separate. |
| ProveIt_Unknot_Sparse_Incidence_Research.zip | Sparse normal incidence and compressed kernel cost. |
| unknot_topology_spectra_20261009.zip | Component spectra and certified weighted topology information. |
| ProveIt_UnknotRecognition_Research_2026-10-09.zip | Prior geometric/retriangulation continuation and remaining discovery conditions. |
| unknot_power_conjugacy_20261008.zip | Group-theoretic compression, complementary to the present geometric interfaces. |
| unknot_compiled_certificates_20261009.zip | Compiled orbit/certificate handling; not a new triangulation move interface. |
| unknot_component_certificates_20261009.zip | Component certificate infrastructure reused conceptually here. |
| ProveIt_Sparse_Port_Incidence_2026-10-08.zip | Port/component incidence without arbitrary ordered pointwise gluing. |
| ProveIt_Compiled_Port_Quotients_2026-10-08.zip | Compiled port quotients; cyclic order and arbitrary pointwise maps explicitly remain outside the inspected contract. |
| proveit_selective_orbit_transfer_research.zip | Selective orbit transfer and its cost accounting. |

The two other packages named ProveIt_Research_2026-10-08 concern different mathematics and were screened out. The complete inventory preserves their filenames and the article members inspected. The original ZIPs are not duplicated in this new report.

Component incidence cannot determine a cyclic order. The new interface addresses this exact missing datum for finitely many distinct geometric marks, while still requiring geometric construction of the marks and side labels. It does not silently generalize sparse-port certificates into an arbitrary three-dimensional gluing compiler.

## Primary literature and attribution

1. **Agol–Hass–Thurston**, The computational complexity of knot genus and spanning area, Transactions of the AMS 358 (2006), 3821–3850. [Primary preprint](https://arxiv.org/abs/math/0205057). The orbit-counting and weighted-orbit polynomial bounds are established prior work. Their theorem, combined with the proved input-size bounds here, supplies the theoretical compressed-time foundation.

2. **Marc Lackenby**, The efficient certification of knottedness and Thurston norm, Advances in Mathematics 387 (2021), 107796. [Author manuscript](https://people.maths.ox.ac.uk/lackenby/knp13nov20.pdf). Theorem 9.2 and its proof in Section 9.4 recover ordered attachment intersections by deleting distinguished points and applying weighted orbit computations to the intervening arcs. This is the direct theoretical predecessor of the marked-boundary method. Proposition 10.3 also gives polynomial-bit cocycle transport during boundary simplification. The current contribution is a certified native interface and an elementary exact endpoint-encoding optimization, with specialized local transport formulas.

3. **Garoufalidis–Hodgson–Hoffman–Rubinstein**, The 3D-index and normal surfaces, Illinois Journal of Mathematics 60 (2016), no. 1, 289–352. [Primary preprint](https://arxiv.org/abs/1604.02688). DOI: 10.1215/ijm/1498032034. Section 12.4 discusses normal surfaces under 2–3 moves, including the three-quadrilateral annulus around the new edge. The local annulus/two-disc phenomenon is not new. This report gives proved exact min/max formulas for transported coherent fibres and uses them in the implementation; no unqualified priority claim is made.

4. **Marc Lackenby**, Unknot recognition in quasi-polynomial time, Oxford talk, March 2021. [Author slides](https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford.pdf). The stated announced bound is 2^{O((log n)^3)} = n^{O((log n)^2)}. This report does not replace it with the narrower n^{O(log n)} shorthand. The latter occurs here only under a separately stated bounded-depth hypothesis.

5. **Marc Lackenby**, Incompressible surfaces, hierarchies and unknot recognition, arXiv:2607.23350v1, 25 July 2026. [Primary preprint](https://arxiv.org/abs/2607.23350). Theorem 14.4 supplies a compressed cutting interface under its stated hypotheses. The hierarchy/certificate results are relevant infrastructure, but are not treated here as a complete published proof of the announced quasi-polynomial discovery bound. The checked author publication list and primary sources did not supply a separate complete published algorithm proof for that announcement.

6. **Regina developers**, Regina: Software for low-dimensional topology. [Official project](https://regina-normal.github.io/). The independent experiments use Python distribution 7.4.1, engine version 7.4. Regina is an external oracle and optional dependency, not part of the native producer.

All article theorems clearly separate established background, newly derived identities, implemented contracts, measured observations, conditional search bounds, and unimplemented follow-up lemmas.

## Measurement and correction lineage

The original transport local/corpus records refer to four source files preserved exactly in fast/transport_research/measured_sources_before_callback_fix.zip. The subsequent correction shields externally raised callback exceptions from malformed-input handlers; mathematical formulas, candidate policies, and certificate schemas are unchanged. Original source hashes were not replaced.

The final scoring benchmark was rerun on the corrected source with alternating arms. The final marked-order comparison was also rerun on corrected source, retaining all raw wall and CPU samples, full-output comparisons, six replayable reference certificates, and source hashes that were checked unchanged during measurement.

Earlier native/literal and small-mark observations remain explicitly marked as pre-correction. Their numerical payload was preserved. The table-generation script uses the final paired data for the headline comparisons and does not mix those samples with the earlier run.

Final retained-proof replay and full-suite logs refer to the deliverable snapshot. This is mathematical and computational research evidence, not formal proof-assistant verification.
