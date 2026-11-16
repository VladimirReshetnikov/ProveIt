# Source audit

## Repository baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Audited directory: `Logic/PrimitiveRecursiveArithmetic`
- Pinned audit commit: `bce5113f44d613f5625c274128ee761f35486fc5`
- Repository head at the final check: `a2f72b0cdf57f8a3fefd34b272c3d471385e819c`
- Inspection date: 2026-11-15 America/Los_Angeles (2026-11-16 UTC)
- Access mode: read-only, through GitHub file/commit APIs. The upstream repository was not modified or rebuilt.

A direct contents-API comparison found the audited iPRA subtree unchanged at the final head. The entry object identifiers were:

| Entry under `Logic/PrimitiveRecursiveArithmetic` | Git object at both commits |
|---|---|
| `ConciseIPRA` | `622927389849d1e4c3b5f813b8481b7674974acc` |
| `README.md` | `1340d58e7f9c97cc8593341f5e80452633a2b77d` |
| `docs` | `996363773c5e9f09fa826e0cc943f55af059d8dd` |

Thus the report remains pinned to a stable snapshot even though unrelated commits advanced `main` during preparation.

The root README reports 66 proof packets and explicitly warns that the packets were filed as delivered rather than independently verified. It identifies `PR`, `PTm`, `PRAAx`, `Prf`, and the theorem `pra_iff_native` as the formal endpoint. The report therefore distinguishes:

1. human mathematics;
2. exact finite reference programs;
3. native Lean propositions;
4. actual object-theory values of type `Prf PRAAx`.

## Main inspected repository sources

| Path | Role in this package |
|---|---|
| `Logic/PrimitiveRecursiveArithmetic/README.md` | Current repository status, packet count, and verification caveat. |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md` | Native scalar core and relation to usual iPRA. |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd`. |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean` | Exact theorem `pra_iff_native`. |
| `docs/proofs/foundations/ipra_coherent_methods_2026-11-15/` | Finite presentation/contract composition and several small embedded derivations. |
| `docs/proofs/foundations/ipra_local_global/` | Variable-length recursion and local-to-global numerical constructions. |
| `docs/proofs/foundations/ipra_finite_observation/` | Finite observations, no-universal-evaluator warning, proof/computation horizon distinction. |
| `docs/proofs/foundations/ipra_embedding_framework/` | Demand-driven finite observations, certificate-relative mathematics, and exact/approximate boundaries. |
| `docs/proofs/foundations/ipra_framework/` | Finite contracts, Booleanization, bounded search, quotient-free presentations. |
| `docs/proofs/foundations/ipra_finite_use_framework_2026-11-15/` | Latest prior framework: finite-use relational composition, branch invariance, robust finite covers. |
| `docs/proofs/algebra/ipra_stable_observables/` | Stable observables and impossibility of complete effective bound certificates. |
| `docs/proofs/diophantine-number-theory/diophantine_geometry_ipra/` | Projective point codes, height enumeration, conics, descent, and finite generation interfaces. |
| `docs/proofs/diophantine-number-theory/faltings_ipra/` | General positive height bound remains missing; count bounds do not locate points. |
| `docs/proofs/diophantine-number-theory/siegel_ipra/` | Explicit Runge subcase; general positive height/list and count targets remain open. |
| `docs/proofs/diophantine-number-theory/mordell_weil_ipra/` | Finite descent conditional on actual quotient representatives. |

## What is new relative to those packets

The earlier packets already develop finite observations, finite contracts, relational finite-use composition, stable outputs, and point/height arithmetic. This package does **not** rename those ideas. Its new layer is algebraic-geometric and proof-relevant:

- quotient rings by explicit ideal-combination witnesses;
- localization equality by annihilator witnesses;
- a primitive-recursive constructor turning a unit-ideal cover into a cover by arbitrary common powers;
- an explicit finite principal-cover gluing algorithm for modules, valid with zero divisors;
- finite affine-atlas data with certified localization isomorphisms and cocycles;
- structure-sheaf and quasi-coherent-module equalizer contracts;
- a finite Čech computation of `O(d)` on projective space, including a concrete `P^1` normal form.

## External mathematical sources

The external sources are used for comparison with conventional algebraic geometry, not as hidden axioms of the arithmetic proofs.

- The Stacks Project, tags `00CM`, `01HR`, `01HX`, `01I6`, `01JA`, `01EO`, `01XS`, and `0B5K`: localization, affine schemes, principal opens, quasi-coherent modules, gluing, and projective-space cohomology.
- Bruno Buchberger, 1965 thesis / 2006 English translation: Gröbner-basis algorithm and finite reduction certificates.
- Thierry Coquand and Henri Lombardi, *A logical approach to abstract algebra* (2006): constructive extraction from abstract algebraic arguments.
- Jujian Zhang, *Formalising the Proj Construction in Lean* (ITP 2023): comparison point for conventional Lean scheme formalization.
- The user-specified Wikipedia article is used only as an orientation checklist of affine, projective, computational, and scheme-theoretic topics.

## Audit limits

The audit was targeted, not a line-by-line review of all 66 packets. The archive does not assert that every prior claim is correct, and it does not rebuild the upstream Lean project. It records exact claims used as baselines and gives independent finite validation for its own executable algorithms.
