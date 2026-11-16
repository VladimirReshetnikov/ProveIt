# Source audit

Repository inspected: `VladimirReshetnikov/ProveIt`.

Pinned snapshot used for this report:
`58627ed89814ba122e1f0f012f1aba103cda267b` (2026-11-16).

## Canonical architecture

- `Logic/PrimitiveRecursiveArithmetic/README.md`
  - identifies `ConciseIPRA`, `Derivations`, `Bridge`, and `docs/proofs`;
  - states that ordinary `Prf PRAAx` is the portable interface;
  - distinguishes checked libraries from unverified delivered packets.
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
  - selects ordinary ConciseIPRA as the canonical portable presentation;
  - places reusable object arithmetic in `IPRADerivations`;
  - records bridge, open-sequent, and migration work.
- `Logic/PrimitiveRecursiveArithmetic/ENDPOINTS.md`
  - records exact checked boundaries, replay commands, toolchain, and
    representative application endpoints.

## Object calculus and arithmetic

- `ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
  - inductive `Prf`;
  - `subst`, `weaken`, `trans`, `exE`, and equality substitution.
- `Derivations/Lean/IPRADerivations/Core/Basic.lean`
  - object arithmetic symbols;
  - arbitrary-term defining equations;
  - `inst` and open quantifier-free induction `ind`.
- `Derivations/Lean/IPRADerivations/Core/Search.lean`
  - bounded least-zero search;
  - `search_spec`, `search_found`, and `search_minimal`.
- `Derivations/README.md`
  - checked reusable layers: semiring, order, monus, pairing, simultaneous
    recursion, bounded sums, division, gcd, Bezout, descent, linear algebra,
    and theorem modules.

## Prior framework packets inspected

- `docs/proofs/foundations/ipra_finite_query_normal_form_2026-11-16/`
- `docs/proofs/foundations/ipra_kifcr_framework_2026-11-16/`
- `docs/proofs/foundations/FINER-iPRA-framework-2026-11-16/`
- `docs/proofs/foundations/ipra_cbip_framework_2026-11-16/`
- `docs/proofs/foundations/scoped_certificate_realization_ipra_2026-11-16/`
- `docs/proofs/foundations/ipra_bounded_reflection_2026-11-16/`
- `docs/proofs/foundations/ipra_embedding_framework/`
- `docs/proofs/algebra/ipra_observation_algebra_2026-11-16/`

The report reuses their strongest ideas: finite-query certificates, explicit
residuals, bounded interaction programs, demand closure, finite strategies,
stable observations, and certificate escape analysis.  Its distinct addition
is one typed query-indexed interface calculus with a composition theorem stated
directly at the `Prf PRAAx` boundary and a residual-elimination hierarchy.

## Application packets sampled

- `docs/proofs/analysis/lambert_w_ipra_2026-11-16/README.md`
- the packet index in `docs/proofs/README.md`, including analysis, probability,
  topology, algebra, geometry, and Diophantine examples.

These samples were used to ensure the framework addresses actual recurring
obstacles rather than an invented generic problem.

## External background

- Bishop and Bridges, *Constructive Analysis* (1985).
- Kohlenbach, *Applied Proof Theory* (2008).
- Kohlenbach and Oliva, proof mining.
- Escardo and Oliva, finite selection/strategy interpretations.
- Salehi, intuitionistic primitive recursive arithmetic.

External background is explanatory.  The concrete Lean plan is based on the
pinned ProveIt source interfaces above.
