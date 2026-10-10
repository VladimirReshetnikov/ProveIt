import GowersSzemeredi.Proofs16AffineChartCompletion

/-! Common Sanders-strength chart data and a finite cell partition.
The original domains need not intersect. Completion is performed on each
cell and agrees with a map only on its own active domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def sandersChartRadius (p : Real) : Real :=
  Real.exp (-(OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant*(p+1))) / (2*Real.pi)

theorem sandersChartRadius_pos (p : Real) : 0 < sandersChartRadius p := by
  unfold sandersChartRadius
  positivity

/-- A finite family of dense order-eight maps has linear parts on one Bohr
domain. No intersection of the original domains is required. -/
theorem exists_common_sanders_chart_data {N : Nat} [NeZero N] {k : Type*} [Fintype k]
    (D : k → Finset (ZMod N)) (theta : k → ZMod N → ZMod N) {p : Real} (hp : 0 ≤ p)
    (hF : ∀ i, FreimanHom 8 (D i) (theta i))
    (hD : ∀ i, Real.exp (-p)*N ≤ ((D i).card : Real)) :
    ∃ (Gamma : Finset (ZMod N)) (psi : k → ZMod N → ZMod N),
      (Gamma.card : Real) ≤ Fintype.card k *
        (1+OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant*(p+1)^4) ∧
      (∀ i, IsFreimanLinearOn (bohr Gamma (sandersChartRadius p)) (psi i) ∧ psi i 0 = 0) ∧
      ∀ i, ∀ a ∈ D i, ∀ b ∈ D i, theta i a-theta i b = psi i (a-b) := by
  choose G rho psi hG hrho hrhopos hpsi hzero hdiff using
    fun i => sanders_linear_part (D i) (theta i) (hF i) hp (hD i)
  let Gamma := Finset.univ.biUnion G
  have hsub : ∀ i, G i ⊆ Gamma := fun i x hx =>
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩
  refine ⟨Gamma,psi,?_,?_,hdiff⟩
  · have hc : (Gamma.card : Real) ≤ ∑ i, ((G i).card : Real) := by
      exact_mod_cast Finset.card_biUnion_le
    calc (Gamma.card : Real) ≤ ∑ i, ((G i).card : Real) := hc
      _ ≤ ∑ _i : k, (1+OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant*(p+1)^4) :=
        Finset.sum_le_sum fun i _ => hG i
      _ = _ := by simp; ring
  · intro i
    exact ⟨(hpsi i).mono ((bohr_anti (hsub i) _).trans (bohr_mono_radius _ (hrho i))),hzero i⟩

def chartCellSignature {N M : Nat} [NeZero N] [NeZero M] (Gamma : Finset (ZMod N))
    (x : ZMod N) : Gamma → Fin M := fun t => dirichletCell M (t.1*x)

def chartCell {N M : Nat} [NeZero N] [NeZero M] (Gamma : Finset (ZMod N))
    (s : Gamma → Fin M) : Finset (ZMod N) :=
  Finset.univ.filter fun x => chartCellSignature Gamma x = s

theorem chart_cell_mem_own {N M : Nat} [NeZero N] [NeZero M]
    (Gamma : Finset (ZMod N)) (x : ZMod N) :
    x ∈ chartCell Gamma (chartCellSignature (M := M) Gamma x) := by
  simp [chartCell]

/-- Cell differences lie in the common Bohr domain at the specified radius. -/
theorem chart_cell_difference_mem {N M : Nat} [NeZero N] [NeZero M]
    (Gamma : Finset (ZMod N)) (s : Gamma → Fin M) {rho : Real} (hcell : 1 ≤ rho*M)
    {x y : ZMod N} (hx : x ∈ chartCell Gamma s) (hy : y ∈ chartCell Gamma s) :
    x-y ∈ bohr Gamma rho := by
  have hMR : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsig := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
  have hc := dirichletCell_close (congrFun hsig ⟨t,ht⟩)
  have hcR : (centeredAbs (t*x-t*y) : Real)*M < N := by exact_mod_cast hc
  have hsmall : (centeredAbs (t*x-t*y) : Real) < N/M := (lt_div_iff₀ hMR).mpr hcR
  have hlarge : (N : Real)/M ≤ rho*N := by
    rw [div_le_iff₀ hMR]
    nlinarith only [hcell,hN]
  rw [mul_sub]
  exact hsmall.le.trans hlarge

theorem chart_cell_count {N M : Nat} [NeZero N] [NeZero M] (Gamma : Finset (ZMod N)) :
    Fintype.card (Gamma → Fin M) = M^Gamma.card := by
  simp

def chartCellBase {N M : Nat} [NeZero N] [NeZero M] (Gamma : Finset (ZMod N))
    (s : Gamma → Fin M) : ZMod N :=
  if h : (chartCell Gamma s).Nonempty then h.choose else 0

theorem chart_cell_base_mem {N M : Nat} [NeZero N] [NeZero M] (Gamma : Finset (ZMod N))
    (s : Gamma → Fin M) (h : (chartCell Gamma s).Nonempty) : chartCellBase Gamma s ∈ chartCell Gamma s := by
  unfold chartCellBase
  rw [dif_pos h]
  exact h.choose_spec

/-- Every cell has a completion which is Freiman on the entire cell and
retains exactly the active values; empty cells need no special input. -/
theorem chart_cell_completed_data {N M : Nat} [NeZero N] [NeZero M]
    (Gamma D : Finset (ZMod N)) (theta psi : ZMod N → ZMod N)
    (s : Gamma → Fin M) {rho : Real} (hcell : 1 ≤ rho*M)
    (hpsi : IsFreimanLinearOn (bohr Gamma rho) psi)
    (hdiff : ∀ a ∈ D, ∀ b ∈ D, theta a-theta b = psi (a-b)) :
    let C := chartCell Gamma s
    let completed := affineChartCompletion C D theta psi (chartCellBase Gamma s)
    IsFreimanLinearOn C completed ∧ ∀ x ∈ C, x ∈ D → completed x = theta x := by
  intro C completed
  refine ⟨?_,fun x hx hDx => affine_chart_completion_agree C D theta psi _ hdiff hx hDx⟩
  by_cases hC : C.Nonempty
  · exact affine_chart_completion_freiman C D Gamma theta psi
      (chart_cell_base_mem Gamma s hC) hpsi (fun x hx y hy => chart_cell_difference_mem Gamma s hcell hx hy)
  · intro x1 x2 x3 x4 h1 _ _ _ _
    exact (hC ⟨x1,h1⟩).elim

/-- Choose a four-cell pattern for the already selected good quadruples.
The count loss is explicit, and no relation is discarded after this choice. -/
theorem exists_quadruple_chart_cells {N M : Nat} [NeZero N] [NeZero M]
    (Gamma : Finset (ZMod N)) (Q : Finset (Fin 4 → ZMod N)) :
    ∃ s : Fin 4 → Gamma → Fin M,
      Q.card ≤ M^(4*Gamma.card) *
        (Q.filter fun q => ∀ j, q j ∈ chartCell Gamma (s j)).card := by
  let color : (Fin 4 → ZMod N) → (Fin 4 → Gamma → Fin M) :=
    fun q j => chartCellSignature Gamma (q j)
  let W : Finset (Fin 4 → Gamma → Fin M) := Finset.univ
  have hW : W.Nonempty := ⟨fun _ _ => 0,Finset.mem_univ _⟩
  obtain ⟨s,hs,hmax⟩ := Finset.exists_max_image W (fun s => (Q.filter fun q => color q = s).card) hW
  have hsum : Q.card = ∑ t ∈ W, (Q.filter fun q => color q = t).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hcard : W.card = M^(4*Gamma.card) := by
    simp only [W,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
    rw [← pow_mul]
    congr 1
    omega
  have heq : (Q.filter fun q => color q = s) = (Q.filter fun q => ∀ j, q j ∈ chartCell Gamma (s j)) := by
    ext q
    simp only [Finset.mem_filter,chartCell,Finset.mem_univ,true_and]
    exact and_congr_right fun _ => funext_iff
  refine ⟨s,?_⟩
  calc Q.card = ∑ t ∈ W, (Q.filter fun q => color q = t).card := hsum
    _ ≤ ∑ _t ∈ W, (Q.filter fun q => color q = s).card := Finset.sum_le_sum hmax
    _ = M^(4*Gamma.card) * (Q.filter fun q => ∀ j, q j ∈ chartCell Gamma (s j)).card := by
      rw [Finset.sum_const,nsmul_eq_mul,hcard,heq]
      simp

end LeanProofs.GowersSzemeredi
