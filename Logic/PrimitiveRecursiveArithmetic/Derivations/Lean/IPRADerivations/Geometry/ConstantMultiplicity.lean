import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# A closed two-chain has constant coefficients (`conway_criterion_ipra_2026-11-16`, `lem:constantmultiplicity`)

Packet: `geometry/conway_criterion_ipra_2026-11-16`, `05_torus_cycle.tex`, lemma
`lem:constantmultiplicity`: "If `Z = ∑_σ c_σ σ`, `c_σ ∈ ℕ`, `∂Z = 0`, then there is a natural
number `k` such that `c_σ = k` for every `σ`." Proof: "the coefficient of either orientation of
`e` in `∂Z` is `c_σ − c_τ`. Since `∂Z = 0`, adjacent face coefficients are equal. ... the
certificate includes a finite spanning tree of this dual graph rooted at a chosen face.
Traverse its explicitly listed vertices in parent-before-child order. Quantifier-free induction
on the traversal index propagates the equality `c_σ = c_root`."

The faces are listed as `j < F` in traversal order, with coefficient `c(j, x)`, root `0` and
parent `par(j, x) < j` for `j > 0`; the hypothesis is the equality across each tree edge,
`c(j) = c(par(j))`, which `∂Z = 0` gives at the edge shared by the two faces.

* `eqB`, `inst2_eqB`: the bit `[c(j) = c(0)]`;
* `prop_step`: if all faces below `J` agree with the root and `J` is the root or agrees with
  its parent below `J`, then all faces below `J + 1` agree with the root;
* `propagate`: the bit `∀ j < F, c(j) = c(0)` is one. The induction on the traversal index is
  quantifier-free: the statement about all earlier faces is one bit
  (`Foundations/BoundedReflection`);
* `constant_multiplicity`: `c(j) = c(0)` for every `j < F`; the constant `k` is `c(0)`.

Not derived: that the dual graph of the triangulation is connected (the spanning tree is part
of the certificate) and the incidence computation of `∂Z`.
-/

namespace LeanProofs.IPRA.Geometry.ConstantMultiplicity

open_ipra
open LeanProofs.IPRA.Foundations.BoundedReflection (allB allB_zero allB_succ all_elim)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.Signum (sg sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (c par : PTm 2)

/-- The bit `[c(j, x) = c(0, x)]`. -/
def eqB : PTm 2 := eqb c (Syn.subst ![zero, var 1] c)

theorem inst2_eqB (j x : PTm n) : inst2 (eqB c) j x = eqb (inst2 c j x) (inst2 c zero x) := by
  simp only [inst2, eqB, subst_eqb, Syn.subst_subst]
  congr 1
  congr 1; funext i; fin_cases i <;> simp

/-- One face more: `J` is the root, or agrees with its parent, which was visited before. -/
theorem prop_step {J x : PTm n} (hQ : Γ ⊢[PRAAx] allB (eqB c) J x ≐ one)
    (hJ : Γ ⊢[PRAAx] (J ≐ zero) ⋎ (lt (inst2 par J x) J ⋏
      (inst2 c J x ≐ inst2 c (inst2 par J x) x))) :
    Γ ⊢[PRAAx] allB (eqB c) (succ J) x ≐ one := by
  have key : Γ ⊢[PRAAx] inst2 c J x ≐ inst2 c zero x := by
    refine .orE hJ (congrInst2 c Prf.hyp0 (.eqRefl x)) ?_
    have ne := all_elim (eqB c) (hQ.wk (ψ := lt (inst2 par J x) J ⋏
      (inst2 c J x ≐ inst2 c (inst2 par J x) x))) (Prf.andE₁ Prf.hyp0)
    rw [inst2_eqB] at ne
    exact (Prf.andE₂ Prf.hyp0).eqTrans (eq_of_eqb_ne ne)
  refine (allB_succ (eqB c) J x).eqTrans ?_
  rw [inst2_eqB]
  have s : Γ ⊢[PRAAx] sg (eqb (inst2 c J x) (inst2 c zero x)) ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (eqb_of_eq key))).eqTrans (sg_succ zero)
  ipra_lc 𝔞 (sg (eqb (inst2 c J x) (inst2 c zero x))) * natEq hQ + natEq s

/-- The tree edges: every face below `F` is the root or agrees with an earlier face. -/
abbrev treeHyp (F x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift F) ⟶ ((var 0 ≐ zero) ⋎
    (lt (inst2 par (var 0) (Syn.shift x)) (var 0) ⋏
      (inst2 c (var 0) (Syn.shift x) ≐ inst2 c (inst2 par (var 0) (Syn.shift x)) (Syn.shift x)))))

/-- The induction formula; variable `0` is the number of visited faces. -/
abbrev propF (F x : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift F) ⟶ (allB (eqB c) (var 0) (Syn.shift x) ≐ one)

/-- All faces agree with the root. -/
theorem propagate {F x : PTm n} (H : Γ ⊢[PRAAx] treeHyp c par F x) :
    Γ ⊢[PRAAx] allB (eqB c) F x ≐ one := by
  let invariant := allB (eqB c) (var 0) (Syn.shift x) ≐ one
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst F) by simpa [invariant] using result
  refine qfIndUpTo F trivial ?_ ?_
  · simpa [invariant] using allB_zero (Γ := Γ) (eqB c) x
  · simp [invariant]
    exact .impI (prop_step c par Prf.hyp1 (.impE H.allOpen.wk.wk Prf.hyp0))

/-- `lem:constantmultiplicity`: every coefficient equals the coefficient of the root. -/
theorem constant_multiplicity {F x j : PTm n} (H : Γ ⊢[PRAAx] treeHyp c par F x)
    (hj : Γ ⊢[PRAAx] lt j F) : Γ ⊢[PRAAx] inst2 c j x ≐ inst2 c zero x := by
  have ne := all_elim (eqB c) (propagate c par H) hj
  rw [inst2_eqB] at ne
  exact eq_of_eqb_ne ne

end LeanProofs.IPRA.Geometry.ConstantMultiplicity
