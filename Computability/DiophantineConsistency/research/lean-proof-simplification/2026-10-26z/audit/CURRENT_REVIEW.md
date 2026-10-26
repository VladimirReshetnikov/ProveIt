# Current independent review: four retained directions

**Proof source pin:** `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
**Final exclusion cutoff:** `7def5e00ef3593b296eb595add1d955d27121d0c`.

**Delivery identity check:** `45ac0dfc366f798d4686070a89d66e8dafdb6879` only relocates the audited Round3 packet to v and updates status/index metadata. The 22-packet substantive corpus and four-direction review are unchanged; see `DELIVERY_CHECK.md`.

This is the current review for delivery. The earlier five-direction review is superseded. `FRESHNESS.md` controls the final novelty decisions: its 22-packet corpus excludes the independently rediscovered interval induction and all shared-edge construction work. Only the following four mechanisms remain recommendations. Fifteen selected target/dependency modules are byte-identical between the two pins.

## 1. Integer periods for helical rows and seam status

The helical vector `(w,-1)` has the right signs: translating `(x,t)` by `t` times it yields `(x+t*w,0)`. This handles negative time, zero/negative width and arbitrary result type without new hypotheses. The seam proof correctly turns the already established one-step equivalence into a proposition-valued period-one invariant; it does not assert the tiles themselves are constant.

The exact-signature generic helical theorem and period-one helper compiled with Lean 4.32.0. The observed log lists only `[propext, Quot.sound]`. This does not establish a whole production-module build or a baseline/candidate axiom comparison for the actual seam theorem. The seam adaptation explicitly uses `propext`; that use is disclosed. Updated source comments match the new proofs.

The retained patch removes eleven declaration lines from `row_zero_of_helix` (19→8, body 16→5) and four from `seam_iff_zero` (8→4, body 7→3). Both module files together change 253→238 physical lines. No new helper declaration or import is added to the production patch.

No corresponding vector-period simplification was found in the refreshed corpus. It is distinct from both the now-excluded interval induction and earlier finite-cell/modular geometry.

## 2. Fixed-index Pell-six threshold

The exact chain is

`A(A²−1)² < A⁵ ≤ xn_A(5) ≤ yn_A(6) ≤ yn_A(p) = c`.

The original assumptions `1 < A`, `6 ≤ p`, `c = yn_A(p)` are preserved. The positive recurrence makes the third inequality `Nat.le_add_right`; no variable predecessor, truncated-subtraction restoration, base comparison or exact-polynomial helper remains.

The final `PellAnchorSmall.lean` compiled successfully, exit 0, using Lean 4.32.0 with `-j1`. `PellAnchorSmall-validation.json` records 112.978 seconds and the exact command. Its log lists `[propext, Classical.choice, Quot.sound]`. This is an isolated exact-signature theorem importing only Mathlib's Pell module; it is not a full `NativePellBootstrap` rebuild.

Pinned declaration lines 217–231 change 15→11, proof body 13→9: **four physical lines removed**, with no new production helper. The exact patch applies to the pin. Together the two retained small mechanisms propose nineteen lines removed across three theorem declarations; no timing improvement is inferred.

The refreshed packets' Pell changes concern parameterized ratios, fundamental-unit minimality and a stronger native-rank envelope. Their copied `large_of_six_le` bodies still use the old variable-exponent argument. The fixed-index anchor remains additional within the reviewed corpus.

## 3. Symbolic color moments for selector masses

The actual coefficient is affine:

`weight(t)=1025+1024W+262144N+134217728E+34359738368S`.

For two signal rows of target q, bit summation gives north total 1, south total 4q+5 and twice the rail on the active horizontal side. The proposed symbolic coefficients 171798956034, 137438953472 and direction coefficients 2048/268435456 are arithmetically correct. For b∈{0,1}, the low cutoff `headColor q b≤45` is equivalent to q≤21.

Independent Python reconstruction from the authenticated action data reproduces the full and filtered numerical masses. It is not a Lean proof. The symbolic core's recorded compiler attempt timed out at 300 seconds without a successful result; numerical and full-client Lean validation remain open. The intended rank-sum theorem must assume the actual ordered target list or an initial segment, not an arbitrary duplicate/unsorted list.

No net source reduction or performance benefit is established. Charge the bit-pair identity, target statistics, rank-sum theorem and cutoff adapter. The proposal remains different after balanced chunk assembly and packed-field descriptors are treated as already installed: it changes the certified quantities. Taking credit for the old weighted chunk ladder would violate the novelty boundary.

## 4. Canonical recognition of arbitrary allowed operating rows

The new obligation is the converse whole-row invariant: an arbitrary allowed, horizontally/temporally matching strip row with the encoded upper configuration equals the existing `stepTile` at every interior position. The entire explicit step-row/shared-edge construction is already proposed in packet U and Round3 and is assumed available at zero new credit.

The proposed recognition route is noncircular. `StepConstruction`'s local import closure has no `RowStep` path. Existing `far_pass` depends on `no_south 438`, whose finish/reset contradiction does not use `south_step` or `row_step`. The existing source-state premise allows an action to enter halt target 215; no premise that the next state remains live is introduced.

A stronger proposed route shares a boundary-aware zero-edge lemma for adjacent nonhead cells. Its left-wall, right-wall and two-plain-cell branches have sufficient bounds from the encoded interior head, and the matching equalities have the correct orientation. This gives an actual-row edge-shape theorem without a state/direction case split. Its Lean source remains explicitly unvalidated.

The finite table check found 942 distinct tiles but 936 distinct `(west,north,east)` keys. Exactly five keys are ambiguous: the four pass/finish keys `(0,0,0)`, `(0,1,0)`, `(0,432,0)`, `(0,433,0)`, and reset key `(1,438,1)` with its three possible south colors. Excluding north 438 and south 438 leaves 935 unique keys/tiles. This independently supports a guarded local determinism lemma; it is Python evidence, not a Lean theorem. The no-finish and no-reset guards must remain explicit.

No exact nonreset/nonfinish three-color-determinism proposal was found in earlier notes/code. Nevertheless, treat this local classification as a charged consequence of the already assumed table/fiber APIs, not as an additional independent invention. The new contribution is the canonical converse composition and its recognition clients.

Neither the conservative receiver-tile prototype nor the stronger edge-recognition route has a successful project compiler result here. Nor is net source reduction measured. Moving `south_step`'s partition into `row_eq_stepTile` can add signature/wrapper overhead; the stronger invariant must pay for itself through actual migrated clients. The optional uniqueness corollary is a consequence of the same invariant, not a fifth proposal.

## Final review disposition

No mathematical blocker was found for the two exact local replacements. Their patch applicability is confirmed; their stated compiler scopes are precise. The two larger directions have concrete mathematical contracts and data evidence but remain costed migration proposals with explicit remaining proof/build work. The final report must not reintroduce interval induction, shared-edge generation, or their advertised integration adapters as new recommendations.
