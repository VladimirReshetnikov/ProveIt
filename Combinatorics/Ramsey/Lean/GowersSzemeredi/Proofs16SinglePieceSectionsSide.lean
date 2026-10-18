import GowersSzemeredi.Proofs16SinglePieceSections

/-! Declarations of `Proofs16SinglePieceSections` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

/-- The dimension-`k` input: one dense multilinear piece on a proper sub-box. -/
def LocalMultilinearPieceAt (k : Nat) (gamma : Real) (c : Real → Real)
    (w : Real → Nat → Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (theta : Real), 0 < theta → theta ≤ 1 →
    ∀ (P : Box N k) (B : Finset (Point N k)) (phi : Point N k → ZMod N),
      P.IsProper → B ⊆ P.carrier → theta * P.carrier.card ≤ B.card →
      HasProductProperty B phi gamma →
      ∃ (R : Box N k) (mu : Point N k → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧ IsMultilinear mu ∧
        c theta * R.carrier.card ≤ (B.filter fun x => x ∈ R.carrier ∧ phi x = mu x).card

/-- **The input gives providers.** -/
theorem LocalMultilinearPieceAt.localPieceFor {d : Nat} {gamma : Real} {c : Real → Real}
    {w : Real → Nat → Nat} (hprov : LocalMultilinearPieceAt d gamma c w)
    {N : Nat} [NeZero N] [Fact N.Prime] {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (hprod : ∀ B ⊆ Dom, HasProductProperty B g gamma) : LocalPieceFor c w Dom g :=
  fun theta hθ hθ1 P H hP hHP hHD hHc =>
    hprov N theta hθ hθ1 P H g hP hHP hHc (hprod H hHD)

/-- The density of the lifted piece. -/
def singlePieceDensity (c : Real → Real) (theta : Real) (q : Nat) : Real :=
  singlePieceTheta theta q * c (c (singlePieceTheta theta q))

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open Classical
variable {A : Type*} [DecidableEq A] {N : Nat}

/-- **One multilinear piece on a line-covered cell**, from providers for the
cross-sections `φ(·, x)`. -/
theorem single_piece_on_line_cell_of_slices {k q : Nat} (hk : 0 < k)
    {c : Real → Real} {w : Real → Nat → Nat}
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (T : Box N k) (J : ModAP N) (hT : T.IsProper) (hJ : J.IsProper) (hTne : T.carrier.Nonempty)
    (hTd : T.commonDiff ≠ 0) (hJstep : J.step = T.commonDiff)
    (hshort : 2 * (T.axis ⟨0, hk⟩).length ≤ N) (hTJ : (T.axis ⟨0, hk⟩).length ≤ J.length)
    (D : Finset (Point N k × ZMod N)) (hD : D ⊆ T.carrier ×ˢ J.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1) (hq : 0 < q)
    (hDc : theta * T.carrier.card * J.carrier.card ≤ D.card)
    (hJq : 2 * (q : Real) ^ 2 ≤ theta ^ 3 * J.length)
    (cls : Point N k × ZMod N → Fin q) (phi : Point N k × ZMod N → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N) (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hphi : ∀ p ∈ D, phi p = ell p.1 (cls p) p.2)
    (Dom : ZMod N → Finset (Point N k))
    (hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))
    (hDom : ∀ p ∈ D, p.1 ∈ Dom p.2)
    (hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1
        ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceDensity c theta q * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card :=
  single_piece_on_line_cell_of_scheme hk (localPieceScheme c w hc hw) T J hT hJ hTne hTd hJstep
    hshort hTJ D hD hθ hθ1 hq hDc hJq cls phi ell hell hphi Dom hsl hDom hwidth

/-- **One multilinear piece on a line-covered cell**, from the dimension-`k`
input and the product property of the cross-sections. -/
theorem single_piece_on_line_cell {k q : Nat} (hk : 0 < k) {gamma : Real}
    {c : Real → Real} {w : Real → Nat → Nat} (hprov : LocalMultilinearPieceAt k gamma c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (T : Box N k) (J : ModAP N) (hT : T.IsProper) (hJ : J.IsProper) (hTne : T.carrier.Nonempty)
    (hTd : T.commonDiff ≠ 0) (hJstep : J.step = T.commonDiff)
    (hshort : 2 * (T.axis ⟨0, hk⟩).length ≤ N) (hTJ : (T.axis ⟨0, hk⟩).length ≤ J.length)
    (D : Finset (Point N k × ZMod N)) (hD : D ⊆ T.carrier ×ˢ J.carrier)
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1) (hq : 0 < q)
    (hDc : theta * T.carrier.card * J.carrier.card ≤ D.card)
    (hJq : 2 * (q : Real) ^ 2 ≤ theta ^ 3 * J.length)
    (cls : Point N k × ZMod N → Fin q) (phi : Point N k × ZMod N → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N) (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hphi : ∀ p ∈ D, phi p = ell p.1 (cls p) p.2)
    (hprod : ∀ x ∈ J.carrier, ∀ B : Finset (Point N k), (∀ h ∈ B, (h, x) ∈ D) →
      HasProductProperty B (fun h => phi (h, x)) gamma)
    (hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :
    ∃ (S : Box N (k + 1)) (R : Box N k) (I : ModAP N) (mu : Point N (k + 1) → ZMod N),
      S.IsProper ∧ IsLastCoordinateBoxProduct S R I ∧ R.carrier ⊆ T.carrier ∧
      S.carrier ⊆ lastProductSet T.carrier J.carrier ∧
      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1
        ≤ S.width ∧
      IsMultilinear mu ∧
      singlePieceDensity c theta q * S.carrier.card ≤
        (D.filter fun p => appendCoordinate p.1 p.2 ∈ S.carrier ∧
          phi p = mu (appendCoordinate p.1 p.2)).card :=
  single_piece_on_line_cell_of_slices hk hc hw T J hT hJ hTne hTd hJstep hshort hTJ D hD
    hθ hθ1 hq hDc hJq cls phi ell hell hphi (fun x => Finset.univ.filter fun h => (h, x) ∈ D)
    (fun x hx => hprov.localPieceFor fun B hB =>
      hprod x hx B fun h hh => (Finset.mem_filter.mp (hB hh)).2)
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hp⟩) hwidth

end

end LeanProofs.GowersSzemeredi
