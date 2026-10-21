import BusyBeaver.ZFC.KSeed222

/- Candidate refactor. Ordinary proof checked by inspection, not compiled here.
   No new axioms, admitted goals, or changes to the numerical calculus. -/
namespace SetTheory.BusyBeaver.ZFC.SeedTransport
open KSeed222
universe u v

theorem map {V : Type u} {W : Type v}
    {m : V → V → Prop} {n : W → W → Prop}
    {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (surj : Function.Surjective f)
    (hm : ∀ x y, n (f x) (f y) ↔ m x y)
    (hR : ∀ x y, S (f x) (f y) ↔ R x y)
    {A : V} (h : SeedProp m R A) : SeedProp n S (f A) := by
  obtain ⟨C, root, closed⟩ := h
  refine ⟨f C, ?_, ?_⟩
  · intro y hy
    obtain ⟨y, rfl⟩ := surj y
    obtain ⟨z, hz, hzC⟩ := root y ((hR A y).mp hy)
    exact ⟨f z, (hR A z).mpr hz, (hm z C).mpr hzC⟩
  · intro y hy
    obtain ⟨y, rfl⟩ := surj y
    obtain ⟨x, hxy, sub⟩ := closed y ((hm y C).mp hy)
    refine ⟨f x, (hR x y).mpr hxy, ?_⟩
    intro x' hx' y' hy'
    obtain ⟨x', rfl⟩ := surj x'
    obtain ⟨y', rfl⟩ := surj y'
    have sub' : ∀ w, m w x' → m w y := by
      intro w hw
      exact (hm w y).mp (hx' (f w) ((hm w x').mpr hw))
    obtain ⟨z, hz, hzC⟩ := sub x' sub' y' ((hR x' y').mp hy')
    exact ⟨f z, (hR x' z).mpr hz, (hm z C).mpr hzC⟩

theorem congr {V : Type u} {m R S : V → V → Prop} {A : V}
    (hRS : ∀ x y, R x y ↔ S x y) :
    SeedProp m R A ↔ SeedProp m S A := by
  constructor
  · exact map id (fun x => ⟨x, rfl⟩) (fun _ _ => Iff.rfl)
      (fun x y => (hRS x y).symm)
  · exact map id (fun x => ⟨x, rfl⟩) (fun _ _ => Iff.rfl) hRS

end SetTheory.BusyBeaver.ZFC.SeedTransport
