import GowersSzemeredi.Proofs16Lemma6

/-! # Fibre geometry and mass estimates for Lemma 16.9 -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The paper's appended-coordinate map is the canonical final-coordinate map. -/
theorem appendCoordinate_eq_snoc {N k : Nat} (x : Point N k) (y : ZMod N) :
    appendCoordinate x y = Fin.snoc x y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendCoordinate]
  · simp [appendCoordinate, j.isLt]

@[simp] theorem section16Init_appendCoordinate {N k : Nat} (x : Point N k) (y : ZMod N) :
    section16Init (appendCoordinate x y) = x := by
  rw [appendCoordinate_eq_snoc, section16Init_snoc]

@[simp] theorem section16Last_appendCoordinate {N k : Nat} (x : Point N k) (y : ZMod N) :
    section16Last (appendCoordinate x y) = y := by
  rw [appendCoordinate_eq_snoc]
  simp [section16Last]

/-- The last-coordinate product is the injective image of the finite product. -/
theorem lastProductSet_eq_image {N k : Nat} [NeZero N]
    (A : Finset (Point N k)) (I : Finset (ZMod N)) :
    lastProductSet A I = (A ×ˢ I).image (fun z => Fin.snoc z.1 z.2) := by
  classical
  ext x
  simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product]
  constructor
  · intro hx
    exact ⟨(Fin.init x, x (Fin.last k)), hx, Fin.snoc_init_self x⟩
  · rintro ⟨⟨y, z⟩, hyz, rfl⟩
    simpa only [section16Init_snoc, section16Last, Fin.snoc_last] using hyz

/-- Cardinalities multiply, without assumptions about progression presentations. -/
theorem lastProductSet_card {N k : Nat} [NeZero N]
    (A : Finset (Point N k)) (I : Finset (ZMod N)) :
    (lastProductSet A I).card = A.card * I.card := by
  rw [lastProductSet_eq_image, Finset.card_image_of_injective]
  · exact Finset.card_product A I
  · intro a b hab
    apply Prod.ext
    · have h := congrArg (fun x : Point N (k + 1) => section16Init x) hab
      simpa only [section16Init_snoc] using h
    · have h := congrArg (fun x : Point N (k + 1) => x (Fin.last k)) hab
      simpa only [Fin.snoc_last] using h

/-- A good base subset retains the same density in its full product. -/
theorem lastProductSet_good_mass {N k : Nat} [NeZero N]
    (A G : Finset (Point N k)) (I : Finset (ZMod N)) (eta : Real)
    (hsub : G ⊆ A) (hmass : (1 - eta) * (A.card : Real) ≤ G.card) :
    lastProductSet G I ⊆ lastProductSet A I ∧
      (1 - eta) * ((lastProductSet A I).card : Real) ≤ (lastProductSet G I).card := by
  classical
  constructor
  · intro x hx
    have h := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub h.1, h.2⟩
  · rw [lastProductSet_card, lastProductSet_card]
    push_cast
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg I.card)

/-- Intersecting two good subsets loses at most the sum of their losses. -/
theorem good_intersection_mass {X : Type*} [DecidableEq X]
    (S F G : Finset X) (alpha beta : Real) (hF : F ⊆ S) (hG : G ⊆ S)
    (hFm : (1 - alpha) * (S.card : Real) ≤ F.card)
    (hGm : (1 - beta) * (S.card : Real) ≤ G.card) :
    (1 - alpha - beta) * (S.card : Real) ≤ (F ∩ G).card := by
  have hcard := Finset.card_union_add_card_inter F G
  have hsub : F ∪ G ⊆ S := Finset.union_subset hF hG
  have hbound := Finset.card_le_card hsub
  have hcard' : ((F ∪ G).card : Real) + (F ∩ G).card = F.card + G.card := by exact_mod_cast hcard
  have hbound' : ((F ∪ G).card : Real) ≤ S.card := by exact_mod_cast hbound
  nlinarith

/-- Every last-coordinate fibre of a multilinear function is globally affine. -/
theorem IsMultilinear.linearOn_last_fibre {N k : Nat} [NeZero N]
    {mu : Point N (k + 1) → ZMod N} (hmu : IsMultilinear mu) (h : Point N k) :
    LinearOn Finset.univ (fun x => mu (appendCoordinate h x)) := by
  classical
  obtain ⟨c, hc⟩ := hmu
  refine ⟨∑ e : Fin k → Bool, c (Fin.snoc e true) * ∏ i, if e i then h i else 1,
    ∑ e : Fin k → Bool, c (Fin.snoc e false) * ∏ i, if e i then h i else 1, ?_⟩
  intro x _
  dsimp only
  rw [appendCoordinate_eq_snoc, hc,
    ← (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.snocEquiv, Fin.prod_univ_castSucc, Finset.sum_mul,
    mul_assoc, add_comm]

/-- Add two affine maps on a shared domain. -/
theorem LinearOn.add {N : Nat} {A : Finset (ZMod N)} {f g : ZMod N → ZMod N}
    (hf : LinearOn A f) (hg : LinearOn A g) : LinearOn A (fun x => f x + g x) := by
  obtain ⟨a, b, hf⟩ := hf
  obtain ⟨c, d, hg⟩ := hg
  refine ⟨a + c, b + d, ?_⟩
  intro x hx
  dsimp only
  rw [hf x hx, hg x hx]
  ring

/-- Multiply an affine map by a constant. -/
theorem LinearOn.const_mul {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : LinearOn A f) (c : ZMod N) : LinearOn A (fun x => c * f x) := by
  obtain ⟨a, b, hf⟩ := hf
  refine ⟨c * a, c * b, ?_⟩
  intro x hx
  dsimp only
  rw [hf x hx]
  ring

/-- Restriction preserves affine agreement. -/
theorem LinearOn.mono {N : Nat} {A B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : LinearOn B f) (hsub : A ⊆ B) : LinearOn A f := by
  obtain ⟨a, b, hf⟩ := hf
  exact ⟨a, b, fun x hx => hf x (hsub hx)⟩

/-- An affine map on a partial domain has a globally affine extension. -/
theorem LinearOn.exists_extension {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {f : ZMod N → ZMod N} (hf : LinearOn A f) :
    ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧ ∀ x ∈ A, f x = ell x := by
  obtain ⟨a, b, hf⟩ := hf
  exact ⟨fun x => a * x + b, ⟨a, b, fun _ _ => rfl⟩, hf⟩

end LeanProofs.GowersSzemeredi
