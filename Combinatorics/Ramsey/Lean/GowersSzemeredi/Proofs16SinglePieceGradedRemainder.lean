import GowersSzemeredi.Proofs16SinglePieceRemainder

/-! The graded remainder piece (Notes L.10, G1).

`remainder_piece_on` nests one provider per non-top cube vertex. All of them
share one worst-case pair `(C, W)`. Vertex `e` is a pullback to the face of
dimension `|e| + 1`, so its natural provider comes from the cover in that
dimension, which is much cheaper for small faces.

Here the vertices are graded by any function `g` with `g e < K` on non-top
vertices. Block `j` (`vertexBlock k g j`) is nested with the uniform pair
`(C j, W j)`, and the blocks are composed in the order `j = 0, 1, …, K − 1`:
* `gradedNestC C n K θ` is the nest of the blocks' densities, where
  `n j = |vertexBlock k g j|`;
* `gradedNestW` is the matching width;
* `remainder_piece_graded_on` is `remainder_piece_on` with graded providers.
With one block it is the uniform nest. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The nest of `K` uniform blocks: block `j` nests `n j` copies of `C j`. -/
def gradedNestC (C : Nat → Real → Real) (n : Nat → Nat) : Nat → Real → Real
  | 0 => id
  | j + 1 => fun t => nestC (fun _ => C j) (n j) (gradedNestC C n j t)

/-- The width of the graded nest. -/
def gradedNestW (C : Nat → Real → Real) (W : Nat → Real → Nat → Nat) (n : Nat → Nat) :
    Nat → Real → Nat → Nat
  | 0 => fun _ L => L
  | j + 1 => fun t L =>
      nestW (fun _ => C j) (fun _ => W j) (n j) (gradedNestC C n j t) (gradedNestW C W n j t L)

theorem gradedNestC_pos_le {C : Nat → Real → Real}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < C j t ∧ C j t ≤ 1) (n : Nat → Nat) :
    ∀ K t, 0 < t → t ≤ 1 → 0 < gradedNestC C n K t ∧ gradedNestC C n K t ≤ 1 := by
  intro K
  induction K with
  | zero => intro t ht ht1; exact ⟨ht, ht1⟩
  | succ K ih =>
    intro t ht ht1
    obtain ⟨h0, h1⟩ := ih t ht ht1
    exact nestC_pos_le (c := fun _ => C K) (fun _ => hC K) (n K) _ h0 h1

/-- A nest of monotone widths is monotone in the input width. -/
theorem nestW_mono_L {c : Nat → Real → Real} {w : Nat → Real → Nat → Nat}
    (hw : ∀ i t, Monotone (w i t)) : ∀ r t, Monotone (nestW c w r t) := by
  intro r
  induction r with
  | zero => intro t a b hab; exact hab
  | succ r ih => intro t a b hab; exact hw r _ (ih t hab)

/-- The non-top vertices of grade `j`. -/
def vertexBlock (k : Nat) (g : (Fin k → Bool) → Nat) (j : Nat) : Finset (Fin k → Bool) :=
  Finset.univ.filter fun e => e ≠ (fun _ => true) ∧ g e = j

/-- **The graded blocks.** After `J` blocks, one sub-box carries maps agreeing
with every vertex of grade `< J` on a `gradedNestC … J θ` fraction. -/
theorem graded_vertex_blocks {N k : Nat} [NeZero N] [Fact N.Prime]
    {C : Nat → Real → Real} {W : Nat → Real → Nat → Nat}
    {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    (g : (Fin k → Bool) → Nat)
    (Dom : (Fin k → Bool) → Finset (Point N (k + 1)))
    (hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor (C (g e)) (W (g e)) (Dom e) (section16TranslatedVertex phi x0 e))
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < C j t ∧ C j t ≤ 1) (hW : ∀ j t, Monotone (W j t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N (k + 1)) (H : Finset (Point N (k + 1))) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → H ⊆ Dom e)
    (hHc : theta * P.carrier.card ≤ H.card) :
    ∀ J : Nat, ∃ (R : Box N (k + 1)) (nu : (Fin k → Bool) → Point N (k + 1) → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      gradedNestW C W (fun j => (vertexBlock k g j).card) J theta P.width ≤ R.width ∧
      (∀ e, e ≠ (fun _ => true) → g e < J → IsMultilinear (nu e)) ∧
      gradedNestC C (fun j => (vertexBlock k g j).card) J theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ∀ e, e ≠ (fun _ => true) → g e < J →
          section16TranslatedVertex phi x0 e x = nu e x).card := by
  intro J
  induction J with
  | zero =>
    refine ⟨P, fun _ _ => 0, hP, Finset.Subset.refl _, le_rfl, fun e _ he => absurd he (by omega),
      ?_⟩
    rw [Finset.filter_true_of_mem fun x hx => ⟨hHP hx, fun e _ he => absurd he (by omega)⟩]
    exact hHc
  | succ J ih =>
    obtain ⟨R, nu, hR, hRP, hRw, hnu, hRc⟩ := ih
    set n : Nat → Nat := fun j => (vertexBlock k g j).card with hndef
    set Hs := H.filter fun x => x ∈ R.carrier ∧ ∀ e, e ≠ (fun _ => true) → g e < J →
      section16TranslatedVertex phi x0 e x = nu e x with hHsdef
    obtain ⟨hρ0, hρ1⟩ := gradedNestC_pos_le hC n J theta hθ hθ1
    have hblock : ∀ e ∈ vertexBlock k g J, LocalPieceFor (C J) (W J) (Dom e)
        (section16TranslatedVertex phi x0 e) := by
      intro e he
      obtain ⟨hne, hge⟩ := (Finset.mem_filter.mp he).2
      have h := hvert e hne
      rw [hge] at h
      exact h
    obtain ⟨R2, mu2, hR2, hR2R, hR2w, hmu2, hR2c⟩ := LocalPieceFor.simultaneous_finset
      (vertexBlock k g J) hblock (hC J) (hW J) hρ0 hρ1 R Hs hR
      (fun x hx => (Finset.mem_filter.mp hx).2.1)
      (fun e he => fun x hx =>
        hHD e (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hx).1) hRc
    refine ⟨R2, fun e => if g e = J then mu2 e else nu e, hR2, hR2R.trans hRP, ?_, ?_, ?_⟩
    · exact (nestW_mono_L (fun _ => hW J) _ _ hRw).trans hR2w
    · intro e hne he
      dsimp only
      split_ifs with hge
      · exact hmu2 e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hge⟩)
      · exact hnu e hne (by omega)
    · refine hR2c.trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
      intro x hx
      simp only [Hs, Finset.mem_filter] at hx ⊢
      obtain ⟨⟨hxH, -, hxnu⟩, hxR2, hxg⟩ := hx
      refine ⟨hxH, hxR2, fun e hne he => ?_⟩
      split_ifs with hge
      · exact hxg e (by simp only [vertexBlock, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hne, hge⟩)
      · exact hxnu e hne (by omega)

/-- **One multilinear map for the remainder, with graded providers.** -/
theorem remainder_piece_graded_on {N k : Nat} [NeZero N] [Fact N.Prime]
    {C : Nat → Real → Real} {W : Nat → Real → Nat → Nat}
    {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    (g : (Fin k → Bool) → Nat) (K : Nat) (hgK : ∀ e, e ≠ (fun _ => true) → g e < K)
    (Dom : (Fin k → Bool) → Finset (Point N (k + 1)))
    (hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor (C (g e)) (W (g e)) (Dom e) (section16TranslatedVertex phi x0 e))
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < C j t ∧ C j t ≤ 1) (hW : ∀ j t, Monotone (W j t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N (k + 1)) (H : Finset (Point N (k + 1))) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → H ⊆ Dom e)
    (hHc : theta * P.carrier.card ≤ H.card) :
    ∃ (R : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      gradedNestW C W (fun j => (vertexBlock k g j).card) K theta P.width ≤ R.width ∧
      IsMultilinear mu ∧
      gradedNestC C (fun j => (vertexBlock k g j).card) K theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ section16PhiRemainder phi x0 x = mu x).card := by
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  have hEmem : ∀ e ∈ E, e ≠ fun _ => true := fun e he => (Finset.mem_filter.mp he).2
  obtain ⟨R, nu, hR, hRP, hRw, hnu, hRc⟩ :=
    graded_vertex_blocks g Dom hvert hC hW hθ hθ1 P H hP hHP hHD hHc K
  refine ⟨R, fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x, hR, hRP, hRw,
    ?_, ?_⟩
  · have hsum := (IsMultilinear.finset_sum E
      (fun e x => (-1 : ZMod N) ^ (k + boolWeight e) * nu e x)
      (fun e he => (hnu e (hEmem e he) (hgK e (hEmem e he))).const_mul _)).const_mul (-1)
    have hfun : (fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x) =
        fun x => (-1) * ∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x :=
      funext fun x => by ring
    rw [hfun]
    exact hsum
  · refine hRc.trans ?_
    exact_mod_cast Finset.card_le_card fun x hx => by
      obtain ⟨hxH, hxR, hxg⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxH, hxR, ?_⟩
      simp only [section16PhiRemainder]
      rw [← hEdef]
      congr 1
      exact Finset.sum_congr rfl fun e he => by
        rw [hxg e (hEmem e he) (hgK e (hEmem e he))]
        push_cast [Int.cast_negSucc]
        ring

end LeanProofs.GowersSzemeredi
