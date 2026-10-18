import GowersSzemeredi.Proofs16PowerCoverTransport

/-! Declarations of `Proofs16PowerCoverTransport` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Translation changes neither exceptional mass, graph count, exponent,
nor minimum parent width. No unit-parameter comparison is used. -/
theorem LargeBoxMultilinearCover.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {Gamma : Finset (Point N k × ZMod N)} {rho C e T : Real}
    (h : LargeBoxMultilinearCover Gamma rho C e T) (t : Point N k) :
    LargeBoxMultilinearCover (Gamma.image (fun z => (z.1 + t, z.2))) rho C e T := by
  intro P hP hT
  obtain ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, hc⟩ :=
    h (P.translate (-t)) (hP.translate (-t)) (by simpa using hT)
  refine ⟨M, q, H.image (fun x => x + t), fun j => (Q j).translate t,
    fun j i x => mu j i (x + -t), ?_, ?_, ?_, fun j => (hproper j).translate t,
    hq, ?_, fun j i => (hmu j i).translate (-t), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]
    simpa using hm
  · simpa using hp.translate t
  · intro j
    simpa using hw j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨i, hi⟩ := hc j a ((Box.translate_mem_carrier _ _ _).mp hx)
      ((add_left_injective t).mem_finset_image.mp hh) b hab
    exact ⟨i, by simpa using hi⟩

end LeanProofs.GowersSzemeredi
