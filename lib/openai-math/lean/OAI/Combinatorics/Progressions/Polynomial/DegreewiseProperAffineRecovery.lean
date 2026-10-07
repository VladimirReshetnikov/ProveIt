import OAI.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem degreewise_proper_affine_recovery {B : Type*} [Fintype B] {I : B → Type*}
    [∀ d, Fintype (I d)] (hP : 0 ≤ P) (a : ZMod N → ∀ d, I d → ℝ) (c : ∀ d, I d → ℝ)
    (l : B → ℕ) (hl : ∀ d, 0 < l d) (ε : B → ℝ) (hε : ∀ d, 0 < ε d)
    (hsmall : ∀ d, 2 * (l d : ℝ) * ε d ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (l d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d) :
    let n := Fintype.card (Σ d, I d)
    ∃ J' ⊆ H, J'.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * H.card ≤ (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : ∀ d, I d → ℝ) (β : Fin r → ∀ d, I d → ℝ),
        (r : ℝ) ≤ properAffineRankBound P n ∧
        Set.InjOn ξ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ j, |x j| ≤ (R j : ℤ)) ∧ h = h₀ + ξ x ∧
          ∀ d, ∃ q ∈ realDenominatorGrid (l d),
            ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤ 2 * ε d := by
  intro n
  let a' : ZMod N → (Σ d, I d) → ℝ := fun h i => a h i.1 i.2
  let c' : (Σ d, I d) → ℝ := fun i => c i.1 i.2
  let l' : (Σ d, I d) → ℕ := fun i => l i.1
  let ε' : (Σ d, I d) → ℝ := fun i => ε i.1
  have hnear' : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l',
      ∀ i, |c' i + (a' (rankQuadrupleParameters t 1) i + a' (rankQuadrupleParameters t 2) i -
        a' (rankQuadrupleParameters t 0) i - a' (rankQuadrupleParameters t 3) i) - q i| ≤ ε' i := by
    intro t ht
    choose q hq he using hnear t ht
    have hq' : ∀ d, ∃ v : I d → ℤ, ∀ i, (v i : ℝ) = (l d : ℝ) * q d i := by
      intro d
      obtain ⟨v, hv⟩ := hq d
      exact ⟨v, fun i => congrFun hv i⟩
    choose v hv using hq'
    refine ⟨fun i => q i.1 i.2, ⟨fun i => v i.1 i.2, fun i => hv i.1 i.2⟩, ?_⟩
    intro i
    have hi := (norm_le_pi_norm (c i.1 +
      (a (rankQuadrupleParameters t 1) i.1 + a (rankQuadrupleParameters t 2) i.1 -
        a (rankQuadrupleParameters t 0) i.1 - a (rankQuadrupleParameters t 3) i.1) - q i.1)
      i.2).trans (he i.1)
    simpa only [a', c', ε', Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs] using hi
  obtain ⟨M, _hM, _hMsmall, _hMerror, J₀, hJ₀H, _hJ₀, _hsize₀, r, R, Φ,
      hrank, _hvolume, J', hJ'J₀, hJ, _hretain, hsize, _hscale, base, hproper, hα, hβ, hrepr⟩ :=
    D.proper_affine_graph_recovery hP a' c' l' (fun i => hl i.1) ε' (fun i => hε i.1)
      (fun i => hsmall i.1) hnear'
  let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
  let R' := fun i => R i / (2 * k)
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let ξ := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let α := variableCoefficientLift l' (reduce base).2
  let β := fun j => variableCoefficientLift l' (ψ (Pi.single j 1))
  have hinj : Set.InjOn ξ {x | ∀ i, |x i| ≤ (R' i : ℤ)} := by
    intro x hx y hy hxy
    exact hproper ((mem_centeredIntegerBox R' x).mpr hx)
      ((mem_centeredIntegerBox R' y).mpr hy) hxy
  refine ⟨J', hJ'J₀.trans hJ₀H, hJ, hsize, r, R', ξ, (reduce base).1,
    (fun d i => α ⟨d, i⟩), (fun j d i => β j ⟨d, i⟩), hrank, hinj,
    (fun d i => hα ⟨d, i⟩), (fun j d i => hβ j ⟨d, i⟩), ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, _hgraph, q, hq, he⟩ := hrepr h hh
  obtain ⟨v, hv⟩ := hq
  refine ⟨x, hx, hspace, ?_⟩
  intro d
  refine ⟨fun i => q ⟨d, i⟩, ⟨fun i => v ⟨d, i⟩, funext (fun i => hv ⟨d, i⟩)⟩, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (hε d).le)).mpr
  intro i
  simpa only [a', ε', Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    Real.norm_eq_abs] using he ⟨d, i⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
