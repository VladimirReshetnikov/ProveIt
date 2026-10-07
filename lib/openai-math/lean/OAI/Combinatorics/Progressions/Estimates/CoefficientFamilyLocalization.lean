import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficientCubeFamily_localize {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖) :
    ∃ a : Option Empty → Fin c.cellCount, ∃ k : ∀ j, Option I → Fin (d j).cellCount,
      (∀ t : Option Empty → Fin c.cellLength, c.cell a t ∈ scalarCubeDomain Empty) ∧
      (∀ j (t : Option I → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain I) ∧
      τ (Fin.last (n + 1)) ≤
        ‖𝔼 t : Option Empty → Fin c.cellLength, 𝔼 u : ∀ j, Option I → Fin (d j).cellLength,
          F (c.cell a t) (fun j => (d j).cell (k j) (u j))‖ := by
  let : Nonempty (Option Empty → Fin c.cellLength) := ⟨fun _ => ⟨0, c.cellLength_pos⟩⟩
  let q := FiniteProbabilityWeights.pi (fun j => (d j).source)
  let H (z : Option Empty → ℝ) := q.complexMean (fun x => F z (fun j => (d j).point (x j)))
  have hH (z) : ‖H z‖ ≤ 1 :=
    (q.norm_complexMean_le_mean_norm _).trans
      ((q.mean_mono (fun x => hF z _)).trans_eq (q.mean_const 1))
  obtain ⟨a, ha, hmiddle⟩ := c.localize (hτ 0) hc H hH hbias
  let G (x : Fin n → Option I → ℝ) := 𝔼 t : Option Empty → Fin c.cellLength, F (c.cell a t) x
  have hG (x) : ‖G x‖ ≤ 1 :=
    (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect (fun t _ => hF _ x)).trans_eq (Fintype.expect_const 1))
  have htail : τ 1 ≤ ‖q.complexMean (fun x => G (fun j => (d j).point (x j)))‖ := by
    rw [q.complexMean_finset_expect]
    exact hmiddle
  obtain ⟨k, hk, hlast⟩ := scalarCubeFamily_localize (fun _ => I) d (fun j => τ j.succ)
    (fun j => hτ j.succ) hd G hG htail
  refine ⟨a, k, ha, hk, ?_⟩
  rw [Finset.expect_comm]
  exact hlast

end Erdos3

end

end OAI
