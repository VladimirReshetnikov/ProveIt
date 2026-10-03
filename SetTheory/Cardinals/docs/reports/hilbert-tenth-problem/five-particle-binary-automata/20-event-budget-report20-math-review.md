# Independent mathematical review of Report 20

Date: 2026-10-03

Verdict: **Pass within the stated theorem-level scope.** No mathematical or source-fidelity issue was found in the reviewed draft. The final live-rank clarification and presentation-only changes were checked before recording the hash below.

Reviewed `report20.tex` SHA-256:
`0bbfe74369a3b9b6a72d7e97b104d7cda9207a886950307c0d15ddb94427d975`

## Checks

- The E/P arithmetic indices agree with the pinned Report 19 proof: moving P blocks precede home P factors, and negative near-phase indices precede positive ones. All inclusive travel ranges and block boundaries agree.
- The statement fixes the source, exact mass, horizon, and total changing-factor budget. The natural canonical input interface, complete auxiliary uniqueness, endpoint conditions, zero-horizon specialization, and empty/singleton cases are consistent with the frozen schema.
- The fixed candidate slots, signed incidence order, dummy totalization, all-raw-key competitor test, and simultaneous factor output preserve the source semantics. The stable minimum and separate absence/completion round justify exactly k+T nonidle rounds and acceptance at R=T+K exactly when k<=K.
- Canonical signed arithmetic, comparisons, fixed positive divisor quotient/remainder, and Boolean gates have unique natural extensions. The proof explicitly constrains losing and inactive computations, so uniqueness covers the full auxiliary tuple.
- The primitive ledger, residual degree, monomial/expansion bounds, source/table charges, and newly included per-macro accounting are internally consistent. In particular, the listed raw-slot costs total 65n+53+32bc; subsequent displacement and sorting allowances give 192n^2+113n+64nbc, below the stated 200n^2+120n+64nbc+20 bound. Source/descriptor and scheduler allocations fit the separate conservative macro bounds.
- The height bound is appropriately conditional on the specified implementation: valid masked parameters, one-hot source selection, fieldwise class lookup, stable first-hit context extraction, and no unnecessary large intermediates. The distinction between accepting witnesses and arbitrary submitted values is explicit.
- The implemented mass-two example correctly uses three anchor/gap inputs rather than the general four signed-coordinate inputs. Sample ledger arithmetic is consistent. The draft does not claim a shipped arbitrary-mass coefficient exporter, real-witness equivalence, fixed arity for unknown horizons, or mass-two universality.

## Limits of this review

This was a mathematical and source-fidelity review against the frozen schema proof, its independent audit, and the Report 19 proof; the relevant descriptor implementation was also inspected. It was not a fresh executable replay, a complete independent coefficient reconstruction, or a machine-checked proof. The 10000 prefactor and H_* remain conservative existence bounds for the stated explicit circuit construction, not measured output from a general compiler.
