# Source notes and audit boundaries

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspection pin: 781594d886f8dc56069221e2b56bd1e94d9c6e5f

Source read at this pin:

    Analysis/FabiusFunction/Lean/FabiusFunction/GeometricUniformDictionary.lean

Blob: 0cd2da0560566005b456aa1968ebe232936805dd

The relevant interface fixes the normalized law Y_q = (1-q) sum q^j V_j and
its convolution/transform/cumulant dictionary. The new article independently
proves the analytic identities it uses. The repository was not rebuilt.

The preserved README for the Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier
package was also read. It identifies the original August 30, 2026 report as
Part XI of geometric_q_fabius_frontiers.tex. The full consolidated volume was
not obtained through the source interface; no exhaustive audit is claimed.

## Earlier companion article

The user's Library supplied `q_fabius_boundary.pdf`, 22 pages, dated September
30, 2026, titled "The Unit-Circle Barrier for the q-Fabius Transform". Its
normalization, endpoint finite-order expansion, cyclotomic moment-pole theorem,
and further questions were read. Pages 12–14 were also inspected visually.

The present paper addresses a precisely specified endpoint growth-and-summation
problem related to that paper's Section 11.2. Its minimal-denominator conjecture
(Section 11.1) is not resolved. The companion PDF is not redistributed here and
was not assumed to be part of the repository at the current inspection pin.

## Primary literature

The embedded bibliography cites:

- Arias de Reyna, compact-support Fabius/Rvachev function, arXiv:1702.05442.
- NIST DLMF, Sections 4.36, 24.2, and 25.6.
- Garoufalidis–Zagier, Nahm sums at roots of unity, arXiv:1812.07690.
- Garoufalidis–Kashaev, quantum-dilogarithm resurgence, arXiv:2008.12465v2.
- Sauzin, 1-summability and resurgence, arXiv:1405.0356.

The general Borel–Laplace and q-product techniques are established methods.
Their use here is not advertised as a new general theory. The source comparison
was focused and did not establish worldwide priority for the exact combined
q-Fabius endpoint theorem. Search failures or missing formal declarations were
not treated as evidence that a mathematical statement was historically open.
