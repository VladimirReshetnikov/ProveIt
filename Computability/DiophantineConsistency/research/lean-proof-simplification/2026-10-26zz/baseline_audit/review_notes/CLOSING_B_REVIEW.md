# Closing packet B: rank / zero-test / base-unit review

Packet: `proveit-lean-rank-zero-test-2026-10-26`.
Report SHA256: `e7a988abf60ebd55b1749ba33422d493d43482dca48e1cb6c69eaf5f9ba3714c`.
All 35 materialized file identities and honest per-file read scopes are in `CLOSING_B_COVERAGE.json`.

## Reading boundary

Read in full: report, README, metric macros; all five substantive evidence notes (`mathematical_review`, `novelty_audit`, `candidate_novelty_decisions`, `structural_candidates`, `arithmetic_candidates`); all six Lean kernels/source-shaped fixtures; and all three proposed patches. This is 17 complete semantic reads. Bulk original/proposed modules were inventoried and hashed, not freshly read in full; their changed theorem contracts and bodies were read through complete patches, source-shaped fixtures, and accompanying reviews. Metadata/large prior-hit indexes were schema/sample-inspected and inventoried only. No included scripts, Lean or Lake were executed.

## Outcomes now assumed fully available

### B01 — Sharp upper native-rank deficit

Report lines 119–240; `arithmetic_candidates.txt` section A; `RankUpperEnvelope.lean`, `RankWindowClient.lean`, `RankSourceFixture.lean`; `rank-upper.patch`.

For integers with `q = 1 + J*beta`, positive `F`, `alpha`, `J`, positive `C=q-F-alpha`, and strict upper masks `MC<beta`, `MF<2*beta`, the exact rank

`R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J`

satisfies `R ≤ q^4-q^3-q-1`. The deficit is the sum of

- `q*(q^2-1)*(F-1)`;
- `(q^2-1)*(C-1)`;
- `(q+1)*(J-1)`;
- `J*((beta-MC-1)+q*(2*beta-MF-1))`.

All factors are nonnegative by integer discreteness and `q≥3`. Neither mask port needs a lower bound. The actual `NativePellBootstrap.source_window_bound` adapter consumes unchanged source transport/rank/scale facts and the real source arities. Reduced-box equality is attained at `J=F=C=1`, `alpha=q-2`, maximal integer masks; no full source-solution attainability is asserted.

**Reserved follow-ons:** stronger full-source upper margins excluding the reduced extremizer; public upper-envelope API if real consumers justify overhead; use of `E-R≥q³+q+1` to discharge additional `source_window_bound` consumers. Distinguish inner native rank from unrelated outer encodings.

### B02 — Zero-test selector without the idempotence premise

Report lines 242–341; `structural_candidates.txt`; `ZeroTestTwoRows.lean`; `zero-test-two-rows.patch`.

Over a commutative semiring with cancellation away from zero, `u≠0`, `b*n=0`, `n+b*u=u` force `b=if n=0 then 1 else 0`. The zero branch cancels `u`; the nonzero branch uses no-zero-divisors. The literal external-natural and internal-object certificate adapters are granted, including the exact internal typeclass bridge and `slack+1≠0` for arbitrary nonstandard internal slack. Production bodies explicitly clear the unused Boolean field; certificate definitions and all three stored rows remain fixed.

**Guards:** `u≠0` essential; arbitrary semirings with zero divisors do not satisfy this conclusion. Natural slack is required by the external adapter; no assumption that internal naturals equal standard `Nat` is made.

**Reserved follow-ons:** inspect other algebraic certificates for guarded redundancy derived by cancellation of separately certified nonzero factors. A separate versioned zero-test encoding may remove the Boolean row only with all compiler, row/count, degree, object-interpretation and downstream equivalence checks. The pairing selector is expressly not presumed redundant.

### B03 — Actual controller base unit from parity

Report lines 343–387; arithmetic notes section B; two ControllerBase kernels/fixtures; `controller-base-unit.patch`.

Use `B=2^94517`, `Odd d`, `Odd auxiliary` to show `B` is a unit modulo `(d*auxiliary)*auxiliary^k`, including `k=0`. The exact proof uses `Nat.coprime_two_left`, `ZMod.isUnit_iff_coprime`, `Nat.cast_pow`, and `IsUnit.pow`, leaving the huge power symbolic. The actual `block_base_isUnit` no longer uses positive exact order, but the module's other orbit/order dependencies remain. Do not count this endpoint or generic coprime/unit assembly as new.

## Effect on round 7 candidates

- **Outer-seed hKr:** no overlap identified in this packet. The sharp native-rank upper deficit and its window clients do not supply the parent's direct `lt_yn_of_two_le` lower-index reuse in outer seed construction. This is only a packet-specific negative finding, not the final corpus verdict.
- **Exact combined-coefficient reuse (C):** no overlap identified in this packet. It does not discuss `abs_coeff_combined_le`, `coeff_combined_at_entry`, or a new exact-kernel coefficient consumer. The inherited V08/T03/C01/NF023 audit remains necessary; textual absence alone is not a novelty proof.
- **Logical endpoint B from residual search:** already excluded by old zd follow-on, independent of this packet.

## Trust boundary

The packet reports successful Lean 4.32.0 mathematical-kernel and conditional-fixture checks, but not a full production build. These are historical reported validations, not rerun here. For counterfactual novelty all advertised guarded outcomes/adapters are granted irrespective of that limitation. No current validation, performance improvement, stronger source existence, or new axiom claim is inferred.
