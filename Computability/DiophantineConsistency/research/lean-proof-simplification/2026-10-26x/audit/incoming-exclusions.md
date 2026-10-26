# Current incoming exclusions

Source pin: `1e2a853935a6155cbcf2aa199aaca51946c4fff9` (26 October 2026).
All proposed, optional, deferred, and further-question mechanisms below are
assumed applied for the user's novelty constraint. Archive compiler logs are
historical evidence, not checks of this review's candidates.

## diophantine-lean-further-simplifications-2026-10-26.zip

Examined the README, entire substantive report sections, and late novelty audit.
The report was prepared at `23f631ea07fff8632eb8cd92286f7621bbe051c0`.

* Exact object-formula specification normalization with a local `simp only`
  list for `Sat`, atomic specification theorems, `scons`, and determined
  existential witnesses; retain the expression induction but replace binder
  bookkeeping with this semantic fold. Targets include eight Object modules.
  Evidence: `report.tex`, sections 3 and the target appendix.
* A common positive-scale Pell ratio bound, plus reuse of the lower comparison
  across ordinary and half-binomial normalizations. Evidence: section 4.
* Optional integer recovery by two error budgets using `Nat.floor_eq_iff`,
  including arbitrary denominator `s >= 2`. Evidence: section 5.
* Optional observed internal certificate-set closure under empty set, union,
  and insertion, with step monotonicity and injective observation encodings.
  Evidence: section 6; `examples/ObservedClosure.lean` and `ClosureClients.lean`.

## diophantine-lean-further-simplifications-2026-10-26 (1).zip

Examined the README, report sections, optional-prototype discussion, and the
60-family prior exclusion ledger. Source `6f46a5e3480a2fa2e45993b8090826f256aeaa56`.

* Exact equality between the existing list codec and mathlib's library codec;
  derive typed parent checking from an already proved raw theorem. The optional
  list-length bound is included. Evidence: report section 2 and patches 01/02.
* One local quadratic coefficient-fiber theorem, covering diagonal multiplicity,
  selective zero coefficients and an optional mixed-product prototype.
  Evidence: report section 3, patch 03 and `optional/PairFiber.lean`.
* Absolute-value second-coordinate minimality for Pell fundamental units;
  optional general `y^2` minimum-coordinate criterion. Evidence: report section 4,
  patch 04 and `optional/PellMinimum.lean`.
* Shared bounded interval first-exit/minimal-counterexample selection, with its
  strict-prefix property, for left and right strip walls. Evidence: report section 5
  and patch 05. Its negative aggregate line saving does not make it eligible again.

## diophantine-lean-structural-refinements-2026-10-26.zip

Examined the README, entire main report, future questions, 98-item prior
exclusion audit, and scope/validation notes. Source `4b3dd4efb10f1af27143a6142380322131968726`,
exclusion refresh `23f631ea07fff8632eb8cd92286f7621bbe051c0`.

* Parameterized Pell ratio estimate, including further scale clients and possible
  perturbation interfaces. Evidence: report section 2.
* Sharper common native-rank envelope `(2*q-1)*(q^2-1) <= nativeRank`, with
  consequences `rank >= 40` and `rank > 3*q`; further strengthened bounds from
  genuine source equations and minimizing downstream assumptions. Section 3.
* Integer induction centered at a seed or translated to zero for interval
  propagation, including choice-free and choice-using variants. Section 4.
* Bounded first-failure/prefix certificate, including general reuse. Section 5.
* Shared-edge representation of Wang step rows: one bridge signal determines
  horizontal matching. The actual `stepTile` equality and Allowed integration
  are unfinished but explicitly proposed, so remain excluded. Section 6 and 9.
* `le_abs'.mp` cleanup for the absolute-value trace-bound disjunction. Section 7.

## Narrow fresh mechanisms screened

1. `WangTiles942HelicalQuotient.row_zero_of_helix`: turn a helix orbit into an
   integer function with period one and use `Function.Periodic.int_mul_eq`.
   This differs from the pending centered interval induction: it removes local
   induction altogether by recognizing rigidity of the actual orbit.
2. `WangTiles942CycleBand.marked_word_of_halt` and
   `WangTiles942BandMarker.canonicalWord_properties`: prove the exact quotient
   construction's matching and band binding before packaging it existentially,
   then reuse that fact when adding marker uniqueness. The fresh contribution
   is elimination of a duplicated new completeness pipeline; canonical witness
   interfaces as a general principle have precedents and are not claimed new.

The independent a-r audit found no occurrence of these helical or canonical
cycle-band targets in reports, companion notes, or supplied Lean prototypes.
Round o explicitly declined a general new additive quotient framework for
short existing periodic-plane wrappers; these narrowly scoped changes do not
introduce such a framework.
