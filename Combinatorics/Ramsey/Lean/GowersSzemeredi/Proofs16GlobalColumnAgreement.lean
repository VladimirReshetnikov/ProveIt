import GowersSzemeredi.Proofs16ZeroColumnsBihomomorphism
import GowersSzemeredi.Proofs16WitnessAgreementSlice
import GowersSzemeredi.Proofs16ColumnSliceAgreement

/-! Dense agreement with the original map after one common vertical shift.
No witness or agreement oracle is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnAgreementSliceDensity (alpha : Real) : Real :=
  columnWitnessDensity (columnEightDensity alpha)/
    (refinementCells (globalColumnZeroRadius alpha/2) : Real)^
      (globalColumnModelRank alpha+columnSpectrumCap (columnEightDensity alpha))

def globalColumnAgreementDensity (alpha : Real) : Real :=
  globalColumnZeroDensity alpha*(globalColumnAgreementSliceDensity alpha)^2

theorem globalColumnAgreementSliceDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnAgreementSliceDensity alpha := by
  have hc := columnWitnessDensity_pos (columnEightDensity_pos ha)
  have hs : 0 < globalColumnZeroRadius alpha/2 := div_pos (globalColumnZeroRadius_pos ha ha1) (by norm_num)
  have hQ : 0 < refinementCells (globalColumnZeroRadius alpha/2) := Nat.ceil_pos.mpr (by positivity)
  have hQR : (0 : Real) < refinementCells (globalColumnZeroRadius alpha/2) := by exact_mod_cast hQ
  unfold globalColumnAgreementSliceDensity
  positivity

theorem globalColumnAgreementDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnAgreementDensity alpha := by
  exact mul_pos (globalColumnZeroDensity_pos ha ha1)
    (sq_pos_of_pos (globalColumnAgreementSliceDensity_pos ha ha1))

/-- An explicitly dense agreement set inside a bounded-rank column Bohr
domain, with a Freiman bihomomorphism agreeing with the shifted original map. -/
theorem global_column_shifted_agreement {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnZeroModulusBound alpha ≤ N) :
    ∃ (V : Finset (ZMod N)) (S : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (t : ZMod N) (G : Finset (ZMod N × ZMod N)),
      (∀ x ∈ V, (S x).card ≤ globalColumnModelRank alpha+columnSpectrumCap (columnEightDensity alpha)) ∧
      G ⊆ columnBohrDomain V S (globalColumnZeroRadius alpha/2) ∧
      globalColumnAgreementDensity alpha*(N : Real)^2 ≤ G.card ∧
      IsEBihomomorphism (columnBohrDomain V S (globalColumnZeroRadius alpha))
        (fun p => L p.1 p.2+phi (p.1,t)) {0} ∧
      ∀ p ∈ G, (p.1,p.2+t) ∈ A ∧ L p.1 p.2+phi (p.1,t) = phi (p.1,p.2+t) := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,hLfull,hW,hPX,_,hP,hST,hzero,hbih,_⟩ :=
    global_column_core_bihomomorphism A phi ha ha1 hA hphi hN
  let s := globalColumnZeroRadius alpha/2
  let Q := refinementCells s
  let S := fun x => Gamma ∪ T x
  let B := fun x => Finset.univ.filter (fun y => (x,y) ∈ A)
  have hs : 0 < s := div_pos (globalColumnZeroRadius_pos ha ha1) (by norm_num)
  have hQpos : 0 < Q := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  have hQ : 1 ≤ s*Q := by
    have hc : 1/s ≤ (Q : Real) := Nat.le_ceil _
    simpa only [mul_comm] using (div_le_iff₀ hs).mp hc
  have hsle : s ≤ 1/(4*Real.pi) :=
    (by dsimp [s]; linarith [globalColumnZeroRadius_pos ha ha1] : s ≤ globalColumnZeroRadius alpha).trans
      ((globalColumnZeroRadius_le ha ha1).trans (globalColumnIdentityRadius_le ha ha1))
  have hex : ∀ x ∈ P, ∃ D ⊆ B x,
      globalColumnAgreementSliceDensity alpha*N ≤ (D.card : Real) ∧
      ∀ a ∈ D, ∀ b ∈ D, a-b ∈ bohr (S x) s ∧ L x (a-b) = phi (x,a)-phi (x,b) := by
    intro x hx
    apply witness_agreement_slice_density (B x) (T x) (S x) (W x)
      (fun y => phi (x,y)) (L x) (by positivity) hQ (hST x hx) _ (hLfull x (hPX hx))
      (hzero x hx) _ (hW x (hPX hx))
    · intro y hy
      have hyT : y ∈ bohr (T x) s := by
        exact (Finset.mem_inter.mp (by simpa only [S,bohr_union] using hy)).2
      exact bohr_mono_radius _ hsle hyT
    · intro w hw
      obtain ⟨hmem,hwB,hval⟩ := hsys x (hPX hx) w hw
      refine ⟨?_,hwB,hval⟩
      intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem i⟩
  let D (x : ZMod N) := if hx : x ∈ P then Classical.choose (hex x hx) else ∅
  have hD (x : ZMod N) (hx : x ∈ P) :
      D x ⊆ B x ∧ globalColumnAgreementSliceDensity alpha*N ≤ ((D x).card : Real) ∧
      ∀ a ∈ D x, ∀ b ∈ D x, a-b ∈ bohr (S x) s ∧ L x (a-b) = phi (x,a)-phi (x,b) := by
    simpa only [D,dif_pos hx] using Classical.choose_spec (hex x hx)
  obtain ⟨t,V,G,hVP,_,hG,hcard,hbih',hagree⟩ := column_slices_shifted_agreement A phi P S L D
    (globalColumnZeroDensity_pos ha ha1).le (globalColumnAgreementSliceDensity_pos ha ha1).le
    hP (fun x hx => (hD x hx).2.1)
    (fun x hx a haD => (Finset.mem_filter.mp ((hD x hx).1 haD)).2)
    (fun x hx => (hD x hx).2.2) hphi hbih
  exact ⟨V,S,L,t,G,fun x hx => hST x (hVP hx),hG,hcard,hbih',hagree⟩

end LeanProofs.GowersSzemeredi
