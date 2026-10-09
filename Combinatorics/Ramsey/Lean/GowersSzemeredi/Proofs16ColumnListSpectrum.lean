import GowersSzemeredi.Proofs16ColumnWordDomains
import GowersSzemeredi.Proofs16RefinementKernel

/-! Frequency and Freiman-linearity bounds for alternating column lists. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def columnListSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (as : List (ZMod N)) : Finset (ZMod N) := as.toFinset.biUnion T

theorem columnListSpectrum_card_le {N d : Nat} (T : ZMod N → Finset (ZMod N))
    (as : List (ZMod N)) (hT : ∀ x ∈ as, (T x).card ≤ d) :
    (columnListSpectrum T as).card ≤ as.length*d := by
  apply Finset.card_biUnion_le.trans
  calc (∑ x ∈ as.toFinset, (T x).card) ≤ ∑ _x ∈ as.toFinset, d :=
      Finset.sum_le_sum fun x hx => hT x (List.mem_toFinset.mp hx)
    _ = as.toFinset.card*d := by simp
    _ ≤ as.length*d := Nat.mul_le_mul_right d (List.toFinset_card_le as)

theorem mem_columnListSpectrum_bohr {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (as : List (ZMod N)) (r : Real) (y : ZMod N) :
    y ∈ bohr (columnListSpectrum T as) r ↔ ∀ x ∈ as, y ∈ bohr (T x) r := by
  constructor
  · intro hy x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro t ht
    exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr ⟨x,List.mem_toFinset.mpr hx,ht⟩)
  · intro hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro t ht
    obtain ⟨x,hx,ht⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp (hy x (List.mem_toFinset.mp hx))).2 t ht

theorem columnAnchorEval_freiman {N : Nat} (S : Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (as : List (ZMod N))
    (hL : ∀ x ∈ as, IsFreimanLinearOn S (L x)) :
    IsFreimanLinearOn S (fun y => columnAnchorEval (fun x => L x y) as) := by
  induction as with
  | nil => intro _ _ _ _ _ _ _ _ _; rfl
  | cons a as ih =>
    have ht := ih (fun x hx => hL x (List.mem_cons_of_mem a hx))
    intro u v z t hu hv hz ht' he
    have ea := hL a (by simp) u v z t hu hv hz ht' he
    have eb := ht u v z t hu hv hz ht' he
    dsimp only [columnAnchorEval]
    linear_combination ea-eb

theorem columnAnchorEval_zero {N : Nat} (f : ZMod N → ZMod N)
    (as : List (ZMod N)) (hf : ∀ x ∈ as, f x = 0) : columnAnchorEval f as = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [columnAnchorEval,hf a (by simp),ih (fun x hx => hf x (List.mem_cons_of_mem a hx)),sub_zero]

def columnRepresentationDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (as : List (ZMod N)) (w : ColumnWord N as.length) (y : ZMod N) : ZMod N :=
  columnAnchorEval (fun x => L x y) as-columnWordEval (fun x => L x y) w

/-- The defect uses only the anchor and output spectra. -/
theorem columnRepresentationDefect_freiman {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (as : List (ZMod N)) (w : ColumnWord N as.length) (rho : Real)
    (hL : ∀ x ∈ as ++ columnWordEntries w, IsFreimanLinearOn (bohr (T x) rho) (L x)) :
    IsFreimanLinearOn (bohr (columnListSpectrum T (as ++ columnWordEntries w)) rho)
      (columnRepresentationDefect L as w) := by
  let S := bohr (columnListSpectrum T (as ++ columnWordEntries w)) rho
  have hLS : ∀ x ∈ as ++ columnWordEntries w, IsFreimanLinearOn S (L x) := by
    intro x hx a b c d ha hb hc hd he
    exact hL x hx a b c d
      ((mem_columnListSpectrum_bohr T _ rho a).mp ha x hx)
      ((mem_columnListSpectrum_bohr T _ rho b).mp hb x hx)
      ((mem_columnListSpectrum_bohr T _ rho c).mp hc x hx)
      ((mem_columnListSpectrum_bohr T _ rho d).mp hd x hx) he
  have ha := columnAnchorEval_freiman S L as
    (fun x hx => hLS x (List.mem_append_left _ hx))
  have hw := columnAnchorEval_freiman S L (columnWordEntries w)
    (fun x hx => hLS x (List.mem_append_right _ hx))
  intro a b c d hya hyb hyc hyd he
  have ea := ha a b c d hya hyb hyc hyd he
  have ew := hw a b c d hya hyb hyc hyd he
  simp only [columnRepresentationDefect,columnWordEval_eq_entries]
  linear_combination ea-ew

end LeanProofs.GowersSzemeredi
