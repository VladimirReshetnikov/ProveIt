import GowersSzemeredi.Proofs13QuadraticEndpoints

/-! Declarations of `Proofs13QuadraticEndpoints` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem stage135_full_cell_small_affine {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (Q : ModAP N) (hQ : 3 ≤ Q.length)
    (a b : ZMod N) {s : Real} (hs : 0 ≤ s)
    (hdiam : diameterAtMostReal (Q.carrier.image (stage135AmbientQuadratic a b)) s)
    {h : ZMod N} (hh : h ∈ Q.carrier) :
    (centeredAbs ((a * h + b) * Q.step) : Real) ≤ 4 * s := by
  exact stage135_full_cell_small_affine_of_pairwise hprime hodd Q hQ a b hs
    (fun x hx y hy => hdiam.centeredAbs_sub_le (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)) hh

end LeanProofs.GowersSzemeredi
