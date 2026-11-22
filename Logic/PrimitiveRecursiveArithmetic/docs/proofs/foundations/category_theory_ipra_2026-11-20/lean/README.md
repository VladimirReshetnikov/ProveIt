# Lean artifacts: exact scope and status

## Status

The new files `CategoryIPRA/LocalYoneda.lean`,
`CategoryIPRA/Representability.lean`, and `CategoryIPRA/Density.lean`
are **uncompiled integration drafts**, written against the source interfaces in ProveIt commit
`72d37f6d06fa7b5bd0a46732060446d1cffa3f2d` and the repository's Lean
`v4.32.0` toolchain. No Lean executable was available in the generation
environment. This package does not claim local kernel verification of the new
files or of their imported dependency closure. They have no `sorry`, `admit`, or
new axiom declaration; the absence of placeholders does not establish that
elaboration succeeds.

The report's human proofs are complete mathematical arguments at the explicitly
stated presentation-wise level. The roadmap distinguishes those arguments from
the implementation work remaining for a fully checked Lean development.

## What the existing repository really supplies

The inspected ProveIt sources do **not** merely prove ordinary category theory
in Lean's ambient logic. Their conclusions have the form

```lean
Γ ⊢[PRAAx] φ
```

Here `φ : Fm PTm n` is a first-order formula, `PTm n` is term syntax containing
explicit primitive-recursive symbols, and `PRAAx` is the object theory.
`Pres.Laws` gives object-language derivations of the category laws at arbitrary
term substitutions and hypotheses. This is the right architecture for the
requested result. Arbitrary Lean functions `Nat → Nat` would not be an
adequate substitute for `PTm` syntax.

Relevant existing modules and declarations:

| Module under `IPRADerivations/Foundations` | Definitions or declarations inspected |
|---|---|
| `PresentedCategory.lean` | `Pres`, `Pres.Laws`, `inverse_unique`, `section_monic`, `retraction_epic`, `monic_split`, `terminal_unique`, `natAdd_laws` |
| `Yoneda.lean` | `Fam`, `FamLaws`, `NatLaws`, `yoneda`, `yoneda_closed`, `repr_natural`, `repr_eval`, `rep`, `rep_laws`, `yoneda_rep`, `yoneda_rep_arrow` |
| `Adjunction.lean` | `Fun`, `Fun.Laws`, `Adj`, `Adj.Laws`, `CorrLaws`, `psi_phi`, `phi_psi`, `corr_tri_left`, `corr_tri_right`, `corr_eta_nat`, `corr_eps_nat`, `galois_closed` |
| `SplitEquivalence.lean` | `Split`, `Split.Laws`, `G_hom`, `G_congr`, `G_id`, `G_comp`, `sec_nat`, `etaInv_eta`, `eta_etaInv`, `eta_nat` |
| `FiniteLimits.lean` | `proj_lt`, `proj_compat`, `factor_lt`, `factor_proj`, `limit_unique` |
| `FiniteSetClosed.lean` | `evc`, `curryc`, `exp_beta`, `exp_eta`, `exp_unique` |
| `UniversalEvaluatorObstruction.lean` | `no_universal_primitive_recursive_evaluator`, `diagonal_obstruction` |

The finite-set modules have explicit positivity guards; their raw theorems must
not be quoted as already covering every empty-set case. The Python model and
the report handle those cases explicitly, and the roadmap records the Lean
extension that is still required.

## New adapter

`CategoryIPRA/LocalYoneda.lean` defines a law record for a transformation at
one fixed family parameter and one fixed representing object. The upstream
`NatLaws` asks for a term uniformly valid at every parameter and representing
object, which is a stronger sufficient hypothesis. The new `AtLaws` record
avoids that unnecessary restriction. Its Yoneda identity, element typing,
representable specialization, and inducing-arrow typing are object-language
derivation constructors; `from_uniform` connects it to the upstream interface.

`CategoryIPRA/Representability.lean` adds three short derivation constructors:

1. `represented_faithful`: equality of the two precomposition actions at the
   identity implies equality of the arrows.
2. `representable_inverse_left`: the first round trip of specified inverse
   natural transformations gives the first inverse equation of their inducing
   arrows.
3. `representable_inverse_right`: the second round trip gives the other inverse
   equation.

`CategoryIPRA/Density.lean` adds four direct derivation constructors for value
typing, canonical value evaluation, the generator round trip, and reindexing.
These are the algebraic part of the report's density presentation. Full tuple
encoding and the universal cocone record remain roadmap work.

Each conclusion is a derivation in the existing iPRA object language. The code
does not posit an internal set of all natural transformations and never
evaluates an arbitrary PR program.

## Standalone source package

The `Upstream/` directory contains the complete in-repository import closure
for the selected categorical modules, copied from the pinned commit. The Lake
configuration declares separate `ConciseIPRA`, `IPRADerivations`, and
`CategoryIPRA` libraries. Mathlib remains an external dependency pinned to the
same `v4.32.0` release as ProveIt. This package does not bundle its compiled
cache or the Lean executable.

With Lean/Elan installed and network access to the pinned dependencies, run:

```bash
cd category_ipra/lean
lake update
lake exe cache get
lake build CategoryIPRA
lake env lean CategoryIPRA/Audit.lean
```

These are reproduction instructions, not a claim that these commands have
been executed successfully in the generation environment. The default target
imports the three new adapters and the selected existing categorical results.

## Integration into a full ProveIt checkout

The new adapters ultimately import `IPRADerivations.Foundations.Yoneda`.
They can be moved together into the existing derivations library at the pinned
commit, with their module paths adjusted to that library's namespace. The
standalone package above is the supplied reproduction route; it avoids any
need to alter an existing checkout's Lake configuration merely to review the
new files.

After successful compilation, audit declarations and print their axioms in
the existing project. A proof of object-language derivability can use Lean's
metatheory without adding the corresponding principle to iPRA; what matters
for the object result is the definition of `Prf`, the permitted axioms, and
the actual constructed derivation. An independently serialized PR proof
checker and a proof of its equivalence to `Prf` would strengthen the audit but
are not claimed complete by this package.

See `formalization_roadmap.md` for definitions and the path to the remaining
theorems.
