import GowersSzemeredi.Proofs16SixteenFreimanFibres
import GowersSzemeredi.Proofs16MilicevicStructure

/-! The actual graph of active column domains is a dense Freiman bihomomorphism.
Its horizontal fibres inherit the native order-eight index identity; its
vertical fibres are the original Freiman-linear Bohr domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def activeColumnGraph {N : Nat} [NeZero N] (S : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (rho : Real) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => p.1 ∈ S ∧ p.2 ∈ bohr (T p.1) rho

/-- Exact fibrewise counting of the original local domains. -/
theorem active_column_graph_card {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (rho : Real) :
    (activeColumnGraph S T rho).card = ∑ x ∈ S, (bohr (T x) rho).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (fun p hp => (Finset.mem_filter.mp hp).2.1)]
  apply Finset.sum_congr rfl
  intro x hx
  have heq : (activeColumnGraph S T rho).filter (fun p => p.1 = x) = {x} ×ˢ bohr (T x) rho := by
    ext p
    simp only [activeColumnGraph,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_product,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-,hy⟩,hpx⟩
      exact ⟨hpx,by simpa only [hpx] using hy⟩
    · rintro ⟨hpx,hy⟩
      exact ⟨⟨hpx.symm ▸ hx,by simpa only [hpx] using hy⟩,hpx⟩
  rw [heq,Finset.card_product,Finset.card_singleton,one_mul]

/-- Uniform local rank gives an explicit positive pair-density bound. -/
theorem active_column_graph_density {N d : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) {rho delta : Real}
    (hr : 0 < rho) (hS : delta * N ≤ S.card)
    (hT : ∀ x ∈ S, (T x).card ≤ d) :
    (delta / (refinementCells rho : Real)^d) * (N : Real)^2 ≤
      (activeColumnGraph S T rho).card := by
  let M := refinementCells rho
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero M := ⟨ne_of_gt hM⟩
  have hMR : (0 : Real) < M := by exact_mod_cast hM
  have hN : (0 : Real) ≤ N := Nat.cast_nonneg _
  have hcell : 1 ≤ rho*(M : Real) := by
    have h := Nat.le_ceil (1/rho)
    rw [div_le_iff₀ hr] at h
    simpa only [M,refinementCells,mul_comm] using h
  have hrows : ∀ x ∈ S, (N : Real)/(M : Real)^d ≤ (bohr (T x) rho).card := by
    intro x hx
    have h := (bohr_card_lower (T x) M hcell).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM (hT x hx)))
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (by simpa only [mul_comm] using h)
  have hcount : (S.card : Real) * ((N : Real)/(M : Real)^d) ≤ (activeColumnGraph S T rho).card := by
    rw [active_column_graph_card,Nat.cast_sum]
    calc (S.card : Real)*((N : Real)/(M : Real)^d) = ∑ _x ∈ S, (N : Real)/(M : Real)^d := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx => hrows x hx
  calc (delta/(refinementCells rho : Real)^d)*(N : Real)^2 =
        (delta*N)*((N : Real)/(M : Real)^d) := by dsimp only [M]; ring
    _ ≤ S.card*((N : Real)/(M : Real)^d) := mul_le_mul_of_nonneg_right hS (by positivity)
    _ ≤ _ := hcount

/-- Native horizontal order-eight identities and vertical Freiman domains
supply the exact E-bihomomorphism interface, with E={0}. -/
theorem active_column_graph_bihom {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (hF : ∀ y, FreimanHom 8 (S.filter fun x => y ∈ bohr (T x) rho) (fun x => L x y))
    (hL : ∀ x ∈ S, IsFreimanLinearOn (bohr (T x) rho) (L x)) :
    IsEBihomomorphism (activeColumnGraph S T rho) (fun p => L p.1 p.2) {0} := by
  constructor
  · intro x1 x2 x3 x4 y hadd h1 h2 h3 h4
    have hf : FreimanHom 2 (S.filter fun x => y ∈ bohr (T x) rho) (fun x => L x y) :=
      IsAddFreimanHom.mono (by norm_num) (hF y)
    have hmem : ∀ x, (x,y) ∈ activeColumnGraph S T rho → x ∈
        (S.filter fun x => y ∈ bohr (T x) rho : Finset (ZMod N)) := by
      intro x hx
      exact Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2
    have he := hf.add_eq_add (hmem _ h1) (hmem _ h2) (hmem _ h3) (hmem _ h4) hadd
    apply Set.mem_singleton_iff.mpr
    linear_combination he
  · intro x y1 y2 y3 y4 hadd h1 h2 h3 h4
    have hx : x ∈ S := (Finset.mem_filter.mp h1).2.1
    have hy1 := (Finset.mem_filter.mp h1).2.2
    have hy2 := (Finset.mem_filter.mp h2).2.2
    have hy3 := (Finset.mem_filter.mp h3).2.2
    have hy4 := (Finset.mem_filter.mp h4).2.2
    have he := hL x hx y1 y2 y3 y4 hy1 hy2 hy3 hy4 hadd
    apply Set.mem_singleton_iff.mpr
    linear_combination he

end LeanProofs.GowersSzemeredi
