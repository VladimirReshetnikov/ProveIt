# Independent approval of the three-tail Lorentzian obstruction

Approved October 1, 2026, at15:47 UTC. The exact source is pinned in approval.json. Its historical submitted-status sentence is superseded by this review; no mathematical correction was needed.

## Abstract transform and parameter family

The Boolean feasibility definition has |I|+|J|−|T|=q, so its displayed degree q+3 is correct. Restricting to an old nonloop and deleting it commutes with the existential allocation, hence gives contraction without witness multiplicity. The three doubled directions (1,0),(0,1),(1,1) represent exactly the stated rank-two matroid.

A direct literal matroid-union basis checker independently examined all210 candidate rank-six subsets of the ten-element union construction and found109 bases. Selecting all three marked elements gives the exact coefficients13,44,112. Its parametric recount gives3p+h,2p²+3ph,p³+3p²h; the discriminant expands to3p²h(15h−4p). Each basis is counted once even when multiple allocations exist.

The elementary nontransversality proof is correct in presentations with any number of slots: two parallel nonloops force the same singleton neighborhood. Distinct classes force distinct slots, producing a forbidden independent triple. Contraction of the universal old element in the displayed rank-three transversal seed gives precisely these three parallel classes. The graph adds two private old tails for a saturating matching; setting their selected variables to zero recovers the claimed quadratic.

## Actual graph and stronger diagonal failure

The graph has six left vertices, seven right vertices and14 edges. Independent literal Hall tests cover all1,716 equal-cardinality endpoint candidates and find397 feasible endpoint pairs. No matching multiplicity is used. The displayed size-six matching is valid, so actual matching rank equals six.

For private head weights4, all other activities1, the full scalar coefficients are[1,23,195,743,1234,744,112]. The selected-variable derivative and specialization have exactly the stated four-by-four Hessian. The two old sum-zero directions have eigenvalue−112; the remaining two-dimensional restriction is positive definite, with determinant48. Thus its inertia is exactly(2,2,0).

The second independent Hall checker recounts the complete three-variable homogenization at tail activities(100,100,100,100,1,1) and head activities(1,1,1,8,8,8,1). It independently reconstructs the general L,p coefficient formulas, not only the numerical specialization. At L=100,p=8, the normalized t^4 coefficient is exactly21260800x²+4688240xz+258845z², with discriminant−33412806400. It is the t=0 specialization of a positive multiple of the fourth derivative. Equivalently, its positive-definite Hessian is a principal block of that derivative Hessian. This contradicts Lorentzianity of the proposed homogenization.

Both displayed scalar gamma polynomials and all ten integer normalized Newton-gap numerators check exactly; all gaps are strictly positive. Thus these examples obstruct the particular multivariate and three-variable Lorentzian constructions. They are not scalar rank-six ULC counterexamples, and they do not exclude another construction or proof of scalar ULC.

## Reproducibility

All three independent checkers use only the Python standard library and reject disabled assertions. They accept --output-dir for portable temporary-directory replay. Their receipts and source hashes are pinned in approval.json. They do not import the producer's code. The exact finite counterexamples themselves constitute the proof of failure; no floating-point eigenvalue or solver output is used.
