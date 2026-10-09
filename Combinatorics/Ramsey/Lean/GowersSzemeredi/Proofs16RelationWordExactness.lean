import GowersSzemeredi.Proofs16RelationWordEndpoints
import GowersSzemeredi.Proofs16PrimeSmallRange

/-! In a prime cyclic target, bounded-image compatible words are exact
on a smaller endpoint Bohr domain. The spectrum is unchanged, and the
radius cost is explicit in the word length and relation image bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem relationWordDefect_freiman {N : Nat} (D : Finset (ZMod N))
    (F : ZMod N → ZMod N → ZMod N) (as : List (ZMod N)) (w : ColumnWord N as.length)
    (hF : ∀ x ∈ as ++ columnWordEntries w, IsFreimanLinearOn D (F x)) :
    IsFreimanLinearOn D (relationWordDefect F as w) := by
  have ha := columnAnchorEval_freiman D F as
    (fun x hx => hF x (List.mem_append_left _ hx))
  have hw := columnAnchorEval_freiman D F (columnWordEntries w)
    (fun x hx => hF x (List.mem_append_right _ hx))
  intro a b c d h1 h2 h3 h4 he
  have hA := ha a b c d h1 h2 h3 h4 he
  have hW := hw a b c d h1 h2 h3 h4 he
  simp only [relationWordDefect, columnRepresentationDefect, columnWordEval_eq_entries]
  linear_combination hA-hW

theorem relationWordDefect_normalized {N : Nat}
    (F : ZMod N → ZMod N → ZMod N) (as : List (ZMod N)) (w : ColumnWord N as.length)
    (hF : ∀ x ∈ as ++ columnWordEntries w, F x 0 = 0) :
    relationWordDefect F as w 0 = 0 := by
  unfold relationWordDefect columnRepresentationDefect
  rw [columnWordEval_eq_entries,
    columnAnchorEval_zero (fun x => F x 0) as (fun x hx => hF x (List.mem_append_left _ hx)),
    columnAnchorEval_zero (fun x => F x 0) (columnWordEntries w) (fun x hx => hF x (List.mem_append_right _ hx))]
  simp

/-- Bounded-image relations give exact endpoint identities with radius
`r / (9^ell * M^(2*ell-1))` and no new frequencies. -/
theorem coherent_relation_word_exact {N ell : Nat} [NeZero N] [Fact N.Prime]
    (A B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    {r : Real} (hr : 0 ≤ r) (M : Nat)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i))
    (hF : ∀ x ∈ A, IsFreimanLinearOn (freimanFrequencyBohr B theta r x) (F x) ∧ F x 0 = 0)
    (hR : ∀ a b c d, R a b c d → ColumnQuadImageRelation
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F r M a b c d)
    (a : ZMod N) (as : List (ZMod N)) (w : ColumnWord N (a::as).length)
    (ha : ∀ x ∈ a::as, x ∈ A) (hw : w ∈ relationWordRepresentations A R (a::as))
    (hMN : M^(2*as.length+1) < N) :
    ∀ y ∈ bohr (relationWordEndpointSpectrum
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) (a::as) w)
      ((r/(9 : Real)^(a::as).length)/(M^(2*as.length+1) : Nat)),
      columnAnchorEval (fun x => F x y) (a::as) = columnWordEval (fun x => F x y) w := by
  let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
  let Gamma := relationWordEndpointSpectrum T (a::as) w
  let s := r/(9 : Real)^(a::as).length
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsr : s ≤ r := div_le_self hr (one_le_pow₀ (by norm_num))
  have hindex : ∀ x ∈ (a::as) ++ columnWordEntries w, x ∈ A := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ha x hx
    · exact columnWordEntries_mem A w (relationWordRepresentations_spec A R (a::as) w hw).1 x hx
  have hFreiman : IsFreimanLinearOn (bohr Gamma s) (relationWordDefect F (a::as) w) := by
    apply relationWordDefect_freiman
    intro x hx
    apply ((hF x (hindex x hx)).1).mono
    intro y hy
    have ht := (mem_bohr_relation_word_endpoints T (a::as) w s y).mp hy x hx
    exact bohr_mono_radius _ hsr ht
  have hzero : relationWordDefect F (a::as) w 0 = 0 :=
    relationWordDefect_normalized F (a::as) w (fun x hx => (hF x (hindex x hx)).2)
  have himage := coherent_relation_word_image_card_le A B theta F R hr M htheta hR a as w ha hw
  intro y hy
  have h := freiman_small_image_zero Gamma hs (relationWordDefect F (a::as) w)
    hFreiman hzero himage hMN y hy
  exact sub_eq_zero.mp h

end LeanProofs.GowersSzemeredi
