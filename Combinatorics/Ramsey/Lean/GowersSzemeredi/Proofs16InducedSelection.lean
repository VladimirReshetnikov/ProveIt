import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs10ProgressionLinearity

/-! # Constructing the induced map used by the Section 16 partition argument -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The value of a partial map on an occupied index fibre, and zero elsewhere. -/
def domainInducedValue {N : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N) (Y : Finset X) (s : ZMod N) : ZMod N :=
  if hs : ∃ x, x ∈ Y ∧ D.index x = s then phi hs.choose else 0

/-- A Bohr difference model forces agreement on every occupied index fibre. -/
theorem HasBohrDifferenceModel.constant_on_fibres {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] {D : MultifunctionDomain N X}
    {phi : X → ZMod N} {K : Finset (ZMod N)} {zeta : Real}
    {Y : Finset X} {psi : ZMod N → ZMod N}
    (h : HasBohrDifferenceModel D phi K zeta Y psi) (hzeta : 0 ≤ zeta)
    {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) (hindex : D.index x = D.index y) :
    phi x = phi y := by
  classical
  have hzero : (0 : ZMod N) ∈ bohr K zeta := by
    simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r _
    simpa [centeredAbs] using mul_nonneg hzeta (Nat.cast_nonneg N)
  have hpsi : psi 0 = 0 := by
    simpa using (h.2 x hx x hx (by simpa using hzero)).symm
  have hdiff := h.2 x hx y hy (by simpa [hindex] using hzero)
  rw [hindex, sub_self, hpsi] at hdiff
  exact sub_eq_zero.mp hdiff

/-- Choice of a representative does not affect the induced value. -/
theorem domainInducedValue_agrees {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] {D : MultifunctionDomain N X}
    {phi : X → ZMod N} {K : Finset (ZMod N)} {zeta : Real}
    {Y : Finset X} {psi : ZMod N → ZMod N}
    (h : HasBohrDifferenceModel D phi K zeta Y psi) (hzeta : 0 ≤ zeta)
    (x : X) (hx : x ∈ Y) : domainInducedValue D phi Y (D.index x) = phi x := by
  classical
  let hs : ∃ y, y ∈ Y ∧ D.index y = D.index x := ⟨x, hx, rfl⟩
  unfold domainInducedValue
  rw [dif_pos hs]
  exact h.constant_on_fibres hzeta hs.choose_spec.1 hx hs.choose_spec.2

/-- Two elements of a progression differ by an integer multiple of its
step with coefficient bounded by any upper bound for its length. -/
theorem ModAP.sub_mem_symmetricMultiples {N m : Nat} (I : ModAP N)
    (hI : I.length ≤ m) {x y : ZMod N} (hx : x ∈ I.carrier) (hy : y ∈ I.carrier) :
    x - y ∈ section10SymmetricMultiples I.step m := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.mem_image.mpr
  refine ⟨(i.val : Int) - j.val, Finset.mem_Icc.mpr ?_, ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    constructor <;> omega
  · push_cast
    ring

/-- The induced partial map is affine on every progression short enough
for Corollary 10.14, restricted to its occupied indices. -/
theorem domainInducedValue_linearOn {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (K : Finset (ZMod N)) (zeta : Real)
    (Y : Finset X) (psi : ZMod N → ZMod N)
    (hprime : N.Prime) (hmodel : HasBohrDifferenceModel D phi K zeta Y psi)
    (hzeta : 0 ≤ zeta) (m : Nat) (hm : 0 < m) (I : ModAP N)
    (hd : I.step ∈ bohr K (zeta / m)) (hI : I.length ≤ m) :
    LinearOn (I.carrier ∩ Y.image D.index) (domainInducedValue D phi Y) := by
  classical
  obtain ⟨c, hc⟩ := corollary_10_14_holds N X D phi K zeta Y psi hprime hmodel m hm I.step hd
  by_cases hne : (I.carrier ∩ Y.image D.index).Nonempty
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨Cy, hCy, hCyIndex⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
    refine ⟨c, domainInducedValue D phi Y y - c * y, ?_⟩
    intro x hx
    obtain ⟨Cx, hCx, hCxIndex⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    have hdiff := hc Cx hCx Cy hCy (by
      rw [hCxIndex, hCyIndex]
      exact I.sub_mem_symmetricMultiples hI (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1)
    have hxval : domainInducedValue D phi Y x = phi Cx := by
      rw [← hCxIndex]; exact domainInducedValue_agrees hmodel hzeta Cx hCx
    have hyval : domainInducedValue D phi Y y = phi Cy := by
      rw [← hCyIndex]; exact domainInducedValue_agrees hmodel hzeta Cy hCy
    rw [hCxIndex, hCyIndex] at hdiff
    rw [hxval, hyval]
    linear_combination hdiff
  · refine ⟨0, 0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- Construct the selection formerly supplied as a standing Section 16
hypothesis from the actual family of Bohr models. -/
theorem section16_inducedSelection_exists {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (K : Point N k → Finset (ZMod N)) (zeta : Real)
    (psi : Point N k → ZMod N → ZMod N) (hprime : N.Prime) (hzeta : 0 ≤ zeta)
    (hmodel : ∀ h, h ∈ H → HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
      (section16InducedCubeMap B h phi) (K h) zeta (Y h) (psi h)) :
    ∃ phiPrime : Point N k → ZMod N → ZMod N,
      Section16InducedSelection B phi H Y K zeta phiPrime := by
  classical
  let phiPrime (h : Point N k) := domainInducedValue (section16CubeMultifunctionDomain B h)
    (section16InducedCubeMap B h phi) (Y h)
  refine ⟨phiPrime, ?_, ?_⟩
  · intro h hh C hC
    exact domainInducedValue_agrees (hmodel h hh) hzeta C hC
  · intro h hh m hm d hd I hstep hI
    have hlin := domainInducedValue_linearOn (section16CubeMultifunctionDomain B h)
      (section16InducedCubeMap B h phi) (K h) zeta (Y h) (psi h) hprime
      (hmodel h hh) hzeta m hm I (by simpa [hstep] using hd) hI
    have hdomain : (I.carrier.filter fun x => (h, x) ∈ section16InducedDomain B H Y) =
        I.carrier ∩ (Y h).image (section16CubeMultifunctionDomain B h).index := by
      ext x
      simp [section16InducedDomain, hh, section16CubeMultifunctionDomain]
    rw [hdomain]
    exact hlin

/-- Lemma 16.5 together with the induced-value and progression-linearity
input subsequently used in Lemmas 16.6 and 16.7. -/
theorem section16_models_and_induced_selection {N k : Nat} [NeZero N]
    (hprime : N.Prime) (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hB : Section16StructuredPair theta gamma B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi phiPrime : Point N k → ZMod N → ZMod N,
          section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
            ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
          (∀ h ∈ H,
            (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
              (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
              (section16Zeta theta gamma k) (Y h) (psi h)) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
            (section16Zeta theta gamma k) phiPrime := by
  classical
  obtain ⟨H, hmass, Y, psi, hmodel⟩ := lemma_16_5_holds N k theta gamma B phi ht ht1 hg hg1 hB
  obtain ⟨phiPrime, hselection⟩ := section16_inducedSelection_exists B phi H Y _ _ psi hprime
    (by unfold section16Zeta; positivity) (fun h hh => (hmodel h hh).2)
  exact ⟨H, Y, psi, phiPrime, hmass, hmodel, hselection⟩

end LeanProofs.GowersSzemeredi
