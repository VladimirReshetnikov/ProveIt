import GowersSzemeredi.Proofs16RelationWordImages
import GowersSzemeredi.Proofs16ColumnWordIdentity

/-! Exact arbitrary-relation words are the existing exact column words.
This lets the direct zero ladder use the already proved auxiliary-frequency
removal theorem without introducing any Freiman frequency-structure input. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Transfer a compatible word when its relation is an exact local-map identity. -/
theorem relation_word_exact_representation {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (hR : ∀ a b c d, R a b c d → ∀ y,
      y ∈ bohr (T a) r → y ∈ bohr (T b) r → y ∈ bohr (T c) r → y ∈ bohr (T d) r →
      columnQuadDefect L a b c d y = 0) :
    ∀ (as : List (ZMod N)) (w : ColumnWord N as.length),
      (∀ x ∈ as, x ∈ B) → w ∈ relationWordRepresentations B R as →
        w ∈ columnWordRepresentations B T L r as := by
  have htriple : ∀ a : ZMod N, a ∈ B → ∀ t ∈ relationTripleRepresentations B R a,
      t ∈ columnTripleRepresentations B T L r a := by
    intro a ha t ht
    obtain ⟨hm, he, hr⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_product] at hm
    obtain ⟨h1, h2, h3⟩ := hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_, ?_, ?_⟩⟩
    · intro i; fin_cases i
      · exact ha
      · exact h2
      · exact h1
      · exact h3
    · change a+t.2.1 = t.1+t.2.2
      linear_combination he
    · intro y hy
      have hz := hR a t.1 t.2.2 t.2.1 hr y (hy 0) (hy 2) (hy 3) (hy 1)
      change L a y+L t.2.1 y = L t.1 y+L t.2.2 y
      unfold columnQuadDefect at hz
      linear_combination hz
  have hquad : ∀ q ∈ mixedRelationQuadruples B B R, q ∈ exactColumnQuadruples B T L r := by
    intro q hq
    obtain ⟨_, h0, h2, h1, h3, he, hr⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, he, ?_⟩
    · intro i; fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · intro y hy
      have hz := hR (q 0) (q 2) (q 3) (q 1) hr y (hy 0) (hy 2) (hy 3) (hy 1)
      unfold columnQuadDefect at hz
      linear_combination hz
  intro as
  induction as with
  | nil => intro w _ _; exact Finset.mem_univ w
  | cons a as ih =>
    cases as with
    | nil =>
      intro w ha hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        htriple a (ha a (by simp)) w.1 (Finset.mem_filter.mp hw).2⟩
    | cons b as =>
      intro w ha hw
      obtain ⟨_, hy, hz, hq⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htriple a (ha a (by simp)) _ hy,
        ih _ (fun x hx => ha x (List.mem_cons_of_mem a hx)) hz, hquad _ hq⟩

/-- Remove the auxiliary frequencies of an exact relation word with the
existing kernel theorem. The endpoint spectrum and maps are unchanged. -/
theorem relation_word_identity_remove_aux {N d : Nat} [NeZero N] [Fact N.Prime]
    (X B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho) (hBX : B ⊆ X)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (hR : ∀ a b c d, R a b c d → ∀ y,
      y ∈ bohr (T a) r → y ∈ bohr (T b) r → y ∈ bohr (T c) r → y ∈ bohr (T d) r →
      columnQuadDefect L a b c d y = 0)
    (a : ZMod N) (as : List (ZMod N)) (has : ∀ x ∈ a::as, x ∈ B)
    (w : ColumnWord N (a::as).length) (hw : w ∈ relationWordRepresentations B R (a::as))
    (hN : refinementKernelCap (4*(as.length+1)*d) (2*as.length*d) rho r < N) :
    ColumnWordIdentity T L (refinementKernelRadius (4*(as.length+1)*d) (2*as.length*d) rho r)
      (a::as) w :=
  column_word_identity_remove_aux X B T L hrho hr hrle hBX hT hL hzero a as
    (fun x hx => hBX (has x hx)) w (relation_word_exact_representation B T L r R hR _ w has hw) hN

end LeanProofs.GowersSzemeredi
