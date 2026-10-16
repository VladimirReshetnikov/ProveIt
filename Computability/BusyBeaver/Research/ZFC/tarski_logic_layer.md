# The machines' logical engine in Lean

Every calibrated ZFC proof search in this project keeps the same logical
rows: Mira-Cult's 254-state machine (verified upstream in Coq by Jeff) and
every complete-logic control recorded in
[logical_engine_completeness.md](logical_engine_completeness.md), such as the
279-state full-logic PSC control. The reduced equality-free calculi behind
the 248–252-state experiments are refuted by the finite-sort model of
[typed_countermodel.md](typed_countermodel.md); any calibrated sub-254
machine in this family must therefore keep a complete quantifier and
equality layer. Until now its soundness and completeness existed only inside
the imported Coq development (`ZF/stdzf/coq/L1_LMeta.v`, `Std_alpha.v`,
`Std_H.v` and `ZF/m254/coq/logic/*` at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`). This note records an
independent Lean proof. No Coq file was ported or executed; the derivations
below were reconstructed from the classical Tarski/Kalish–Montague route.

## Statements

All modules are under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Module | Result |
|---|---|
| `Kalmar.lean` | For any `imp : α → α → α` and `bot`, a predicate closed under MP containing K, S, Peirce and ex falso contains every instance of every classical `{→, ⊥}` tautology (`tautology_complete`). No injectivity of `imp` is assumed, so code aliases such as `imp 0 0 = 0` are harmless. |
| `TarskiCalculus.lean` | Named formulas `NF` over `∈`, `=`, `⊥`, `→`, `∀`; Tarski semantics; the calculus `Thm Ax` whose rules are exactly MP, generalization, theory axioms `Ax` and the rows below; `soundness`. |
| `TarskiDerived.lean` | Propositional toolkit; quantifier monotonicity; the B axiom from `rho6`; `vac_of_not_occurs` (vacuity for **every** formula not containing the label, although the rows only give it for atoms); equality is an equivalence relation. |
| `TarskiLeibniz.lean` | `leibniz`: `x = y → (φ ↔ φ[y/x])` without rebinding; `spec`: `∀x φ → φ[y/x]`; `spec_self` (the T axiom); `alpha_fwd`/`alpha_bwd`. No substitution row exists in the calculus. |
| `TarskiClean.lean` | Clean formulas (no rebinding), depth relabelling `cl`, the semantic substitution lemma `sat_rn`, and `cl_equiv : ⊢ φ ↔ cl K d φ`. |
| `TarskiComplete.lean` | `completeness`: validity in every model of `Ax` (all formulas of `Ax` true under all assignments) implies `Thm Ax`. Henkin construction over labels; see below. |
| `Lukasiewicz.lean` | (Codex agent) Attributed port of the 107 condensed-detachment certificates of Jeff's `CD254.v`: `rho8` alone yields K, S and Peirce; `rho6` adds ex falso; `Tarski.classical` and the unconditional `Tarski.complete`. |
| `TarskiFalsity.lean` | The machines' relative falsity `F = Rel(0,0)`: `ThmG (rel 0 0) Ax` is the literal row set; it is sound for irreflexive models and complete for `⊥`-free theories and targets with respect to irreflexive models (`alias_sound`, `alias_complete`). The comparison axiom IR is not needed as a row. |

The rows, in the machine's parameter order, are

```text
rho8  ((c → u) → a) → ((a → c) → (b → c))        Lukasiewicz
rho2  ∀a (b → c) → (∀a b → ∀a c)
rho4  ∀a ∀b c → ∀b ∀a c
rho6  ∃a ∀a b → b                                  ∃ = ¬∀¬
rho1  ∃a (a = b)
rho7  c = a → (c = b → a = b)
rho5  c = a → (c ∈ b → a ∈ b)
rho3  a = b → (c ∈ a → c ∈ b)
V∈/V= R(a,b) → ∀c R(a,b), gated by c ≠ a, b
```

matching `Codes254.v:103–110` upstream. In `ThmG F`, `¬A` is `A → F`.

## Proof outline

1. **Propositional.** `rho8` gives K, S and Peirce by condensed detachment;
   ex falso is K followed by `rho6` (`⊥ → ∃0∀0 b → b`). Kalmár's argument then
   yields every tautology instance.

   The certificate is search-determined. An independent given-clause search
   (`lukasiewicz_search.cpp`, replayed and checked step by step by
   `lukasiewicz_cd.py`) with size bound 19 and pick-given ratio 5 finds a
   107-line chain, `results/lukasiewicz-proof.txt`. Its 106 derived formulas
   coincide exactly with the 106 derived certificates of the attributed port;
   the remaining line is the axiom. Anyone can therefore regenerate the
   certificate from `CCCpqrCCrpCsp` alone:

   ```sh
   g++ -O2 -std=c++17 -o lukasiewicz_search lukasiewicz_search.cpp
   ./lukasiewicz_search 19 5 100000000 K=CpCqp P=CCCpqpp S=CCpCqrCCpqCpr > proof.txt
   py -I lukasiewicz_cd.py --from-proof proof.txt        --compare-lean ../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean
   ```

   The C++ program is untrusted; the Python replay re-derives each step with
   its own unifier, and the Lean kernel checks the committed certificates.
2. **Vacuity.** For `i` absent from `φ`, `φ → ∀iφ` by induction: implication
   uses `∃i a → a` (from `rho6` and the induction hypothesis) and a classical
   case split; quantifiers use `rho4`.
3. **Equality and substitution.** `rho1`, `rho7` and atomic vacuity give
   reflexivity, symmetry and transitivity. `rho3`/`rho5` (membership) and
   `rho7` (equality atoms) give Leibniz's law for whole formulas, moving
   `x = y` under binders with `V=`. Specialization to `y` then follows from
   `∃x (x = y)` and existential elimination for the `x`-free instance.
4. **Henkin model.** A Lindenbaum chain visits every formula infinitely
   often. A rejected `∀aχ` (no rebinding of `a`) receives a fresh witness at
   every visit. Theory formulas are axioms of `Thm`, never hypotheses, so a
   witness only needs to avoid finitely many hypotheses and the theory is
   never renamed. The domain is the labels modulo provable equality; `rho1`
   and the unbounded witnesses give every class arbitrarily large
   representatives, which the universal case of the truth lemma uses.
5. **Clean forms.** `cl_equiv`, proved in the empty theory and transported by
   soundness, moves the target and the closures of the theory axioms into the
   clean fragment where the truth lemma holds.
6. **Relative falsity.** Replacing `⊥` by `F` maps derivations to derivations
   (`thm_tau`). IR becomes `∀0 (F → F)`, a generalized identity.

## Obligation map for row minimization

The proof shows exactly where each row is consumed; deleting a row must
re-establish the corresponding lemma by other means.

| Row | Consumed by |
|---|---|
| `rho8` | all propositional reasoning (via K, S, Peirce) |
| `rho6` | ex falso, the B axiom, existential elimination |
| `rho2` | quantifier monotonicity, generalization over hypotheses |
| `rho4` | vacuity of quantified formulas only |
| `rho1` | reflexivity of `=`, specialization, rich equality classes |
| `rho7` | reflexivity, symmetry, transitivity, Leibniz for `=` atoms |
| `rho5`, `rho3` | Leibniz for `∈` atoms; membership congruence of the model |
| `V∈`, `V=` | base cases of vacuity; `V=` moves `x = y` under binders |

Two consequences for compiler experiments:

* Symmetry of `=` is used essentially (for the reverse half of Leibniz),
  so `rho7` cannot be dropped merely because the theory is equality-free.
* Only atomic vacuity with `c ≠ a, b` is needed, which is exactly the
  machines' gate.

## A calibrated equality-free *language* (design analysis, unmeasured)

Soundness of a row is only needed in one extensional model of the theory
(V, or L), not in every structure. In an extensional model the formula
`U(x,y) := ∀z (x ∈ z → y ∈ z)` defines equality. Replacing every equality
atom of the rows by `U` therefore gives rows that are true in V, while the
same translation argument as `thm_tau` transports every derivation of the
primitive-equality calculus. For an equality-free theory true in V this is a
**calibrated, complete** engine whose formulas contain no equality atoms, so
the three-tag codec applies. Being complete, it cannot have an unconditional
nonrefutation model of the kind that sinks the reduced equality-free calculi.
The bound label of `U(i,j)` must avoid `i` and `j` (for example `i + j + 1`);
each translated row is then true in every extensional model: `U(c,a) → (c ∈ b
→ a ∈ b)` is even logically valid, and the others hold because `U` is
identity there (take `z = {x}`).

It is not obviously cheaper. `U` replaces six equality atoms (one in `rho1`,
three in `rho7`, one each in `rho5`/`rho3`), each costing about four
constructor calls instead of one, while saving the `V=` row (vacuity of `U`
is derivable once its bound label avoids the vacuity label) and the equality
constructor. A rough estimate is a net loss of several states under the
public backend. No compilation has been measured, and the bound-label
condition for `V=` still needs a checked choice. It is recorded as a
calibrated alternative, not a recommendation.

## Scope

These theorems concern named formulas and the abstract row calculus. They do
not yet connect numerical codes (`Base3Syntax`, `Bottom3Syntax`, the
upstream dual-Cantor base-4 codec) to `NF`, the gated theory bundle to a
set-theory schema, the enumerator, the compiler, or any literal table. They
supply the logical half of each such calibration in Lean.
