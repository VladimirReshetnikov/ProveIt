import GowersSzemeredi.Proofs16OriginalEightAgreementMass
import GowersSzemeredi.Proofs16FreimanImageRadiusExpansion

/-! Enlarge original eight-tuple agreements to the full natural domain
where the chosen map and all eight original column maps are defined. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Full endpoint-domain data for an original eight-tuple defect. -/
theorem original_eight_endpoint_data {N d s : Nat} [NeZero N]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (rho : Real)
    (hTpsi : Tpsi.card ≤ s) (hpsi : IsFreimanLinearOn (bohr Tpsi rho) psi)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x))
    {a : ZMod N} {t : ColumnAnchorTuple N 7} (ht : t ∈ columnAnchorFibre U 7 a) :
    (Tpsi ∪ columnListSpectrum T (columnAnchorList t)).card ≤ s+8*d ∧
      IsFreimanLinearOn (bohr (Tpsi ∪ columnListSpectrum T (columnAnchorList t)) rho)
        (fun y => psi y-columnAnchorEval (fun x => L x y) (columnAnchorList t)) := by
  have hpoints : ∀ x ∈ columnAnchorList t, x ∈ X :=
    fun x hx => hUX ((Finset.mem_filter.mp ht).2.1 x hx)
  have hlength : (columnAnchorList t).length=8 := by simp [columnAnchorList]
  have hsrcCard := columnListSpectrum_card_le T (columnAnchorList t) (fun x hx => (hcol x (hpoints x hx)).1)
  rw [hlength] at hsrcCard
  refine ⟨(Finset.card_union_le _ _).trans (Nat.add_le_add hTpsi hsrcCard),?_⟩
  let D := bohr (Tpsi ∪ columnListSpectrum T (columnAnchorList t)) rho
  have hpsiD : IsFreimanLinearOn D psi := hpsi.mono (by
    intro y hy
    dsimp only [D] at hy
    rw [bohr_union] at hy
    exact (Finset.mem_inter.mp hy).1)
  have hsrcD : ∀ x ∈ columnAnchorList t, IsFreimanLinearOn D (L x) := by
    intro x hx
    apply (hcol x (hpoints x hx)).2.mono
    intro y hy
    dsimp only [D] at hy
    rw [bohr_union] at hy
    exact (mem_columnListSpectrum_bohr T _ rho y).mp (Finset.mem_inter.mp hy).2 x hx
  have hsum := columnAnchorEval_freiman D L (columnAnchorList t) hsrcD
  intro y1 y2 y3 y4 h1 h2 h3 h4 he
  have ep := hpsiD y1 y2 y3 y4 h1 h2 h3 h4 he
  have es := hsum y1 y2 y3 y4 h1 h2 h3 h4 he
  linear_combination ep-es

/-- The same original tuple family agrees on the full original-radius
intersection, with a rank-controlled factor in the image cap. -/
theorem original_eight_agreement_expand_domain {N d s K : Nat} [NeZero N]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (Tpsi : Finset (ZMod N)) (psi : ZMod N → ZMod N) (a : ZMod N)
    {rho r : Real} (hr : 0 < r) (hrle : r ≤ rho)
    (hTpsi : Tpsi.card ≤ s) (hpsi : IsFreimanLinearOn (bohr Tpsi rho) psi)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x)) :
    originalEightAgreementSet U T L Tpsi psi a r K ⊆
      originalEightAgreementSet U T L Tpsi psi a rho ((refinementCells r)^(s+8*d)*K) := by
  intro t ht
  obtain ⟨htFibre,htImage⟩ := Finset.mem_filter.mp ht
  have hdata := original_eight_endpoint_data X U hUX T L Tpsi psi rho hTpsi hpsi hcol htFibre
  exact Finset.mem_filter.mpr ⟨htFibre,freiman_image_expand_radius _ _ hr hrle hdata.1 hdata.2 htImage⟩

end LeanProofs.GowersSzemeredi
