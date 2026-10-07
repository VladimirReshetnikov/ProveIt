import GowersSzemeredi.Proofs16CoordinatePermutations

/-! Multiply-linear covers are invariant under coordinate permutations,
with exactly the same quantitative parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

@[simp] theorem Box.coordinateReindex_symm {N k : Nat} (P : Box N k)
    (e : Fin k ≃ Fin k) : (P.coordinateReindex e).coordinateReindex e.symm = P := by
  cases P
  simp only [Box.coordinateReindex]
  congr 1
  funext i
  simp

@[simp] theorem Box.coordinateReindex_symm' {N k : Nat} (P : Box N k)
    (e : Fin k ≃ Fin k) : (P.coordinateReindex e.symm).coordinateReindex e = P := by
  simpa only [Equiv.symm_symm] using P.coordinateReindex_symm e.symm

theorem MultiplyLinear.coordinateReindex {N k : Nat} [NeZero N]
    {gamma r : Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinear gamma r Gamma) (e : Fin k ≃ Fin k) :
    MultiplyLinear gamma r
      (Gamma.image (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2))) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h theta ht ht1 (P.coordinateReindex e.symm) (hP.coordinateReindex e.symm)
  refine ⟨M, q, H.image (LeanProofs.GowersSzemeredi.coordinateReindex e),
    fun j => (Q j).coordinateReindex e,
    fun j i x => mu j i (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x),
    ?_, ?_, ?_, fun j => (hproper j).coordinateReindex e, hq, ?_,
    fun j i => (hmu j i).coordinateReindex e.symm, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := (Box.coordinateReindex_mem_carrier (P.coordinateReindex e.symm) e y).mpr (hH hy)
    simpa only [Box.coordinateReindex_symm'] using hh
  · rw [Finset.card_image_of_injective _ (LeanProofs.GowersSzemeredi.coordinateReindex e).injective]
    simpa using hHcard
  · simpa using hpart.coordinateReindex e
  · intro j
    simpa using hwidth j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.coordinateReindex_mem_carrier (Q j) e a).mp hx
    have haH := (LeanProofs.GowersSzemeredi.coordinateReindex e).injective.mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

theorem MultiplyLinearFunction.coordinateReindex {N k : Nat} [NeZero N]
    {gamma r : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (h : MultiplyLinearFunction gamma r B phi) (e : Fin k ≃ Fin k) :
    MultiplyLinearFunction gamma r (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
      (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x)) := by
  classical
  have hh := MultiplyLinear.coordinateReindex h e
  have heq : (partialGraph B phi).image
      (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2)) =
      partialGraph (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
        (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x)) := by
    simp [partialGraph, Finset.image_image, Function.comp_def]
  rw [heq] at hh
  exact hh

/-- Reindexing may use two separately presented finite coordinate types;
their dimensions agree because the coordinate map is an equivalence. -/
theorem MultiplyLinearFunction.reindex {N k l : Nat} [NeZero N]
    {gamma r : Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (h : MultiplyLinearFunction gamma r B phi) (e : Fin k ≃ Fin l) :
    MultiplyLinearFunction gamma r (B.image (fun x i => x (e i)))
      (fun x => phi (fun i => x (e.symm i))) := by
  have he : k = l := by simpa using Fintype.card_congr e
  subst l
  exact h.coordinateReindex e

theorem CoordinateFace.multiplyLinear_of_reparametrization {N d l m : Nat} [NeZero N]
    (F : CoordinateFace N d l) (G : CoordinateFace N d m) (e : Fin m ≃ Fin l)
    (hmap : ∀ x, F.map x = G.map (fun i => x (e i)))
    {B : Finset (Point N d)} {phi : Point N d → ZMod N} {gamma r : Real}
    (h : MultiplyLinearFunction gamma r (G.domain B) (G.pullback phi)) :
    MultiplyLinearFunction gamma r (F.domain B) (F.pullback phi) := by
  classical
  have hh := h.reindex e.symm
  have hdomain : (G.domain B).image (fun x i => x (e.symm i)) = F.domain B := by
    ext x
    rw [CoordinateFace.mem_domain]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [hmap]
      simpa using (CoordinateFace.mem_domain G B y).mp hy
    · intro hx
      refine Finset.mem_image.mpr ⟨fun i => x (e i), ?_, ?_⟩
      · rw [CoordinateFace.mem_domain, ← hmap]
        exact hx
      · funext i
        simp
  have hphi : (fun x => G.pullback phi (fun i => x (e i))) = F.pullback phi := by
    funext x
    exact congrArg phi (hmap x).symm
  rw [hdomain] at hh
  simpa only [Equiv.symm_symm, hphi] using hh

end LeanProofs.GowersSzemeredi
