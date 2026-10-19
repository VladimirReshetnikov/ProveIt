# Independent review: replacing rho4 by double-B6 collapse

Date: 2026-10-18. Reviewed document: `../logical_routes/double_b6_route.md`,
SHA-256 `d57404b068af425a6350023c7fee57b6e61d02791e8ea35e152c7ea313d9c171`.
Original numerical calculus: pinned ProveIt
`7ba1598461c6e485c5aeb8f673c0b1d571f8012b`, `Code254.lean`.

## Verdict

The exact proposed replacement is ordinarily interderivable with original rho4,
using only retained rho6, rho2/QI, rho8, MP and GEN. The two complete native
numerical calculi therefore derive exactly the same codes, including 1. The
proof works with relative falsity F=1, arbitrary numerical matrices and indices,
coincident indices, and the exceptional truth alias 0. No fresh-variable rule,
new EFQ axiom, commutation assumption in the forward proof, or stronger ambient
set theory is required.

This is a logical source transformation, not a verified new binary table. The
inspected cost experiment reports 273 working states, so presently offers no
sub-246 result. Its `calibration_proved=false` is correctly scoped to that
experiment's unclosed table pipeline; it does not refute the ordinary logical
interderivation proved here.

## Explicit reusable algebraic lemma

Let `I(A,B)=4P(A,B)`, `N A=I(A,1)`, `Q_i A=4P(i,A)+2`, and
`D_i A=N(Q_i(N A))`. Let a numerical derivability predicate be closed under MP
and GEN and contain rho8, QI, and every retained B6 instance
`I(D_i(Q_i A), A)`. Write `A <= B` when `I(A,B)` is derivable and `A ~= B`
when both directions are derivable.

1. Rho8 supplies the classical implicational basis (K, S, Peirce), as already
   formalized by `Code254.implicational`. EFQ follows without rho4: K gives
   `F <= D_i(Q_i A)` since the latter expression is `X -> F` with
   `X=Q_i(N(Q_i A))`; compose with retained B6. This is exactly the existing
   `c254_efq` argument, which uses rho6 and K/S only. Classical double negation
   and contraposition are consequently valid with this literal relative F.
2. QI and GEN lift any derivable `A <= B` to `Q_i A <= Q_i B`. Contraposition,
   Q-monotonicity and contraposition again lift it to `D_i A <= D_i B`.
   Equivalences can thus be replaced inside arbitrary finite Q/D contexts.
   In particular all double-negation simplifications below are **derived
   equivalences**, not unlicensed syntactic equations for numerical codes.
3. Contraposing B6 at matrix N A yields
   `N(N A) <= N(D_i(Q_i(N A)))`.
   Expand D and use classical double-negation equivalence to obtain
   `A <= Q_i(D_i A)`. This B form uses no commutation row.
4. Assume all DB instances `D_a(D_b(Q_a(Q_b C))) <= C`.
   Put `C=D_b(D_a A)`. The B instances give
   `A <= Q_a(D_a A)` and `D_a A <= Q_b C`.
   Lift the second under Q_a and compose to get `A <= Q_a(Q_b C)`.
   Lift under the ordered context D_a D_b and apply DB at C:
   `D_a(D_b A) <= D_a(D_b(Q_a(Q_b C))) <= D_b(D_a A)`.
5. Swap a and b in that last conclusion and put A=N P. Contraposition gives
   `N(D_a(D_b(N P))) <= N(D_b(D_a(N P)))`.
   The left side is equivalent to `Q_a(Q_b P)` and the right to
   `Q_b(Q_a P)`, by expansion and Q-monotone transport of double-negation
   equivalences. This is exactly old rho4, with the correct orientation.
6. Conversely, assuming old rho4, lift it under D_a D_b:
   `D_a(D_b(Q_a(Q_b P))) <= D_a(D_b(Q_b(Q_a P)))`.
   Lift B6_b at matrix Q_a P under D_a, then apply B6_a at P. Their composite
   is precisely DB at a,b,P.

All six steps are finite schema-derived derivations. Apply induction on a
native derivation to replace the sole changed axiom in either direction;
all other axiom constructors, bundle gates, truth, MP and GEN are unchanged.
Consequently the predicates coincide on **every** natural code, not just on
well-formed decoded formulas. Numerical coincidences between different
formula expressions do not affect any inference. This gives an ordinary
ZFC proof of equivalence of their derivability of 1; the existing native
calibration to inconsistency of ZFC therefore remains available.

## Source and machine obligations

The target AST in the document is exact:
`Imp(Ex(a,Ex(b,All(a,All(b,c)))),c)`.
Its postfix macro word is
`a,b,a,b,c,all,all,exists,exists,c,imp`, length 11, the same length as the old
commutation word. Equal length does not imply equal grammar sharing/state cost.
The inspected compiler checks its original row expression before replacing it
and checks the whole symbolic emission stack afterward. It retains rho6 and
QI. New DB is still an outer implication and hence cannot numerically equal 1,
so the AX no-first-F fact and the abstract MP-first compiler reviewed separately
remain applicable, with the new fourth axiom leaf.

Any claimed machine improvement must still tie its actual literal table to
this changed source, prove macros and reachable entry/scratch contracts, prove
finite blank startup, and count every working state. Neither the original
literal table proof nor the logical interderivation silently establishes these
changed-machine obligations. No fresh Lean theorem is needed to regard the
ordinary interderivation as valid; there is simply no checked Lean artifact
for this replacement yet.

## Supplemental finite diagnostics

The existing modal checker was freshly rerun with assertions enabled, without
modifying its source or output. Results are saved as `double_b6_modal_fresh.json`
and `.log`: 4,164 symmetric-relation pairs, 33,032 valuations, 66,064 B6 checks,
and 4,164 schema-equivalence checks all pass. These are globally quantified
finite-frame tests over domains of size 1,2,3; they are not a proof for all
frames or the native numerical calculus. The algebraic derivation above is
the proof. The diagnostic script should add a `not __debug__` guard if it is to
be used as a durable certification command, since `python -O` removes its
assertions. This harness improvement is unrelated to validity of the ordinary
proof.

No producer file, shared checkout, external repository, or user computer was
modified in this review.
