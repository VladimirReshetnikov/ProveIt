import DiophantineConsistency.SplitCertificate59
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Positive affine source change for the H2082 equation

Literal source SHA256 e4f50dbede42c421defa2d7d36268413351dd1e023763c584ea34f3b9a827957.
Parent SHA256 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.
Only the elementary source equations and beta positivity are used. There
is no native compiler calibration or Pell-classification assumption.
-/

namespace DiophantineConsistency.GapSource66

set_option maxRecDepth 16000
set_option maxHeartbeats 600000

variable {R : Type*} [CommRing R]

def q (ports : Fin 4 → R) (x : Fin 31 → R) : R := ports 0*x 0+1

/-- Restore exactly the old P and N coordinates. The transport coordinate is retained. -/
def toOld (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 31 → R := fun i =>
  if i=18 then x 18+x 12+x 13 else if i=16 then x 16+q ports x else x i

/-- The explicit affine inverse; its positivity is proved on old source zeros below. -/
def fromOld (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 31 → R := fun i =>
  if i=18 then x 18-x 12-x 13 else if i=16 then x 16-q ports x else x i

theorem fromOld_toOld (ports : Fin 4 → R) (x : Fin 31 → R) :
    fromOld ports (toOld ports x)=x := by
  funext i
  by_cases h18 : i=18
  · subst i
    change (x 18+x 12+x 13)-x 12-x 13=x 18
    ring
  · by_cases h16 : i=16
    · subst i
      change (x 16+(ports 0*x 0+1))-(ports 0*x 0+1)=x 16
      ring
    · simp only [fromOld,toOld,h18,h16,if_false]

theorem toOld_fromOld (ports : Fin 4 → R) (x : Fin 31 → R) :
    toOld ports (fromOld ports x)=x := by
  funext i
  by_cases h18 : i=18
  · subst i
    change (x 18-x 12-x 13)+x 12+x 13=x 18
    ring
  · by_cases h16 : i=16
    · subst i
      change (x 16-(ports 0*x 0+1))+(ports 0*x 0+1)=x 16
      ring
    · simp only [fromOld,toOld,h18,h16,if_false]

-- BEGIN GENERATED GAP SOURCE
/-- Literal source66 rows, independently transcribed from its85-record source. -/
def rows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  ![(x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)),
    ((-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0 * x 24)),
    (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)),
    (x 20 + (-1) * (x 17) + (-1) * (x 9) + (-1) * (x 9 * x 16) + ((-(ports 0))) * (x 0 * x 9)),
    ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21),
    (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17),
    (x 18 + (-1) * (x 17 * x 19) + x 12 * x 17),
    ((-1) + (-1) * (x 18 ^ 2) + (-1) * (x 13 * x 18) + (-1) * (x 12 * x 18) + x 11 ^ 2),
    (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)),
    ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)),
    (x 23 + (-1) * (x 19 ^ 2)),
    ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2),
    ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)),
    ((-1) * (x 26) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2))) * (x 0) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0 * ports 3))) * (x 0 ^ 2)),
    ((ports 1) + x 21 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + ((-(ports 0))) * (x 0 * x 3)),
    (x 25 + (-1) * (x 4 ^ 2)),
    (x 26 + x 19 + (-1) * (x 4 * x 7)),
    (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)),
    (x 28 + (-1) * (x 6 * x 23)),
    (x 29 + (-1) * (x 28 ^ 2)),
    (x 30 + x 29 + (-1) * (x 25 * x 30)),
    ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)]

private theorem row_identity_0 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 0=SplitCertificate59.transformedRows ports (toOld ports x) 0 := by
  change (x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)) = (x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2))
  ring

private theorem row_identity_1 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 1=SplitCertificate59.transformedRows ports (toOld ports x) 1 := by
  change ((-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0 * x 24)) = ((-1) + (-1) * (x 24) + (x 16+(ports 0*x 0+1)) + ((-(ports 0))) * (x 0) + ((-(ports 0))) * (x 0 * x 24))
  ring

private theorem row_identity_2 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 2=SplitCertificate59.transformedRows ports (toOld ports x) 2 := by
  change (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)) = (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10))
  ring

private theorem row_identity_3 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 3=SplitCertificate59.transformedRows ports (toOld ports x) 3 := by
  change (x 20 + (-1) * (x 17) + (-1) * (x 9) + (-1) * (x 9 * x 16) + ((-(ports 0))) * (x 0 * x 9)) = (x 20 + (-1) * (x 17) + (-1) * (x 9 * (x 16+(ports 0*x 0+1))))
  ring

private theorem row_identity_4 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 4=SplitCertificate59.transformedRows ports (toOld ports x) 4 := by
  change ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21) = ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21)
  ring

private theorem row_identity_5 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 5=SplitCertificate59.transformedRows ports (toOld ports x) 5 := by
  change (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17) = (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17)
  ring

private theorem row_identity_6 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 6=SplitCertificate59.transformedRows ports (toOld ports x) 6 := by
  change (x 18 + (-1) * (x 17 * x 19) + x 12 * x 17) = ((x 18+x 12+x 13) + (-1) * (x 17 * x 19) + (-1) * (x 13) + (-1) * (x 12) + x 12 * x 17)
  ring

private theorem row_identity_7 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 7=SplitCertificate59.transformedRows ports (toOld ports x) 7 := by
  change ((-1) + (-1) * (x 18 ^ 2) + (-1) * (x 13 * x 18) + (-1) * (x 12 * x 18) + x 11 ^ 2) = ((-1) + (-1) * ((x 18+x 12+x 13) ^ 2) + x 13 * (x 18+x 12+x 13) + x 12 * (x 18+x 12+x 13) + x 11 ^ 2)
  ring

private theorem row_identity_8 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 8=SplitCertificate59.transformedRows ports (toOld ports x) 8 := by
  change (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)) = (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20))
  ring

private theorem row_identity_9 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 9=SplitCertificate59.transformedRows ports (toOld ports x) 9 := by
  change ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)) = ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2))
  ring

private theorem row_identity_10 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 10=SplitCertificate59.transformedRows ports (toOld ports x) 10 := by
  change (x 23 + (-1) * (x 19 ^ 2)) = (x 23 + (-1) * (x 19 ^ 2))
  ring

private theorem row_identity_11 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 11=SplitCertificate59.transformedRows ports (toOld ports x) 11 := by
  change ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2) = ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2)
  ring

private theorem row_identity_12 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 12=SplitCertificate59.transformedRows ports (toOld ports x) 12 := by
  change ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)) = ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17))
  ring

private theorem row_identity_13 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 13=SplitCertificate59.transformedRows ports (toOld ports x) 13 := by
  change ((-1) * (x 26) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2))) * (x 0) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0 * ports 3))) * (x 0 ^ 2)) = ((-1) * (x 26) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1) + (-1) * (x 1 * x 24) + x 1 * (x 16+(ports 0*x 0+1)) + ((-(ports 3)) + (-(ports 2)) + ports 0) * (x 0) + ((-(ports 0))) * (x 0 * (x 16+(ports 0*x 0+1))) + ((-(ports 0))) * (x 0 * x 1) + ((-(ports 0 * ports 3)) + ports 0 ^ 2) * (x 0 ^ 2))
  ring

private theorem row_identity_14 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 14=SplitCertificate59.transformedRows ports (toOld ports x) 14 := by
  change ((ports 1) + x 21 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + ((-(ports 0))) * (x 0 * x 3)) = ((ports 1) + x 21 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + ((-(ports 0))) * (x 0 * x 3))
  ring

private theorem row_identity_15 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 15=SplitCertificate59.transformedRows ports (toOld ports x) 15 := by
  change (x 25 + (-1) * (x 4 ^ 2)) = (x 25 + (-1) * (x 4 ^ 2))
  ring

private theorem row_identity_16 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 16=SplitCertificate59.transformedRows ports (toOld ports x) 16 := by
  change (x 26 + x 19 + (-1) * (x 4 * x 7)) = (x 26 + x 19 + (-1) * (x 4 * x 7))
  ring

private theorem row_identity_17 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 17=SplitCertificate59.transformedRows ports (toOld ports x) 17 := by
  change (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)) = (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2))
  ring

private theorem row_identity_18 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 18=SplitCertificate59.transformedRows ports (toOld ports x) 18 := by
  change (x 28 + (-1) * (x 6 * x 23)) = (x 28 + (-1) * (x 6 * x 23))
  ring

private theorem row_identity_19 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 19=SplitCertificate59.transformedRows ports (toOld ports x) 19 := by
  change (x 29 + (-1) * (x 28 ^ 2)) = (x 29 + (-1) * (x 28 ^ 2))
  ring

private theorem row_identity_20 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 20=SplitCertificate59.transformedRows ports (toOld ports x) 20 := by
  change (x 30 + x 29 + (-1) * (x 25 * x 30)) = (x 30 + x 29 + (-1) * (x 25 * x 30))
  ring

private theorem row_identity_21 (ports : Fin 4 → R) (x : Fin 31 → R) :
    rows ports x 21=SplitCertificate59.transformedRows ports (toOld ports x) 21 := by
  change ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2) = ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)
  ring

theorem row_identity (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    rows ports x k=SplitCertificate59.transformedRows ports (toOld ports x) k := by
  fin_cases k
  · exact row_identity_0 ports x
  · exact row_identity_1 ports x
  · exact row_identity_2 ports x
  · exact row_identity_3 ports x
  · exact row_identity_4 ports x
  · exact row_identity_5 ports x
  · exact row_identity_6 ports x
  · exact row_identity_7 ports x
  · exact row_identity_8 ports x
  · exact row_identity_9 ports x
  · exact row_identity_10 ports x
  · exact row_identity_11 ports x
  · exact row_identity_12 ports x
  · exact row_identity_13 ports x
  · exact row_identity_14 ports x
  · exact row_identity_15 ports x
  · exact row_identity_16 ports x
  · exact row_identity_17 ports x
  · exact row_identity_18 ports x
  · exact row_identity_19 ports x
  · exact row_identity_20 ports x
  · exact row_identity_21 ports x
-- END GENERATED GAP SOURCE

theorem zero_iff_toOld (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, rows ports x k=0) ↔
      ∀ k, SplitCertificate59.sourceRows ports (toOld ports x) k=0 := by
  constructor
  · intro h
    apply (SplitCertificate59.transformed_zero_iff ports (toOld ports x)).mp
    intro k
    rw [← row_identity]
    exact h k
  · intro h
    have ht := (SplitCertificate59.transformed_zero_iff ports (toOld ports x)).mpr h
    intro k
    rw [row_identity]
    exact ht k

theorem zero_iff_fromOld (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, rows ports (fromOld ports x) k=0) ↔
      ∀ k, SplitCertificate59.sourceRows ports x k=0 := by
  rw [zero_iff_toOld,toOld_fromOld]

def Positive (x : Fin 31 → ℤ) : Prop := ∀ i, 0<x i

theorem toOld_positive (ports : Fin 4 → ℤ) (hβ : 0<ports 0) (x : Fin 31 → ℤ)
    (hx : Positive x) : Positive (toOld ports x) := by
  have hq : 0<q ports x := by unfold q; have := hx 0; positivity
  intro i
  by_cases h18 : i=18
  · subst i
    change 0<x 18+x 12+x 13
    exact add_pos (add_pos (hx 18) (hx 12)) (hx 13)
  · by_cases h16 : i=16
    · subst i
      change 0<x 16+q ports x
      exact add_pos (hx 16) hq
    · simpa only [toOld,h18,h16,if_false] using hx i

/-- The two strict gaps follow before any Pell argument or native interpretation. -/
theorem old_positive_gaps (ports : Fin 4 → ℤ) (hβ : 0<ports 0)
    (x : Fin 31 → ℤ) (hx : Positive x)
    (hs : ∀ k, SplitCertificate59.sourceRows ports x k=0) :
    0<x 18-x 12-x 13 ∧ x 16=(q ports x)^3 ∧ 0<x 16-q ports x := by
  have h0 := hs 0
  have h1 := hs 1
  have h3 := hs 3
  have h5 := hs 5
  have h6 := hs 6
  change x 24+((-2)*ports 0)*x 0+(-(ports 0^2))*(x 0^2)=0 at h0
  change (-1)+(-1)*x 24+x 16+(-ports 0)*x 0+(-ports 0)*(x 0*x 24)=0 at h1
  change x 20+(-1)*x 17+(-1)*(x 9*x 16)=0 at h3
  change x 19+(-1)*(x 13*x 20)+x 13*x 17+(-1)*x 12+
    (-1)*(x 12*x 20)+x 12*x 17=0 at h5
  change x 18+(-1)*(x 17*x 19)+(-1)*x 13+(-1)*x 12+x 12*x 17=0 at h6
  have hY : x 20-x 17=x 9*x 16 := by linear_combination h3
  have hc : x 19-x 12=(x 12+x 13)*(x 20-x 17) := by linear_combination h5
  have hP : x 18-x 12-x 13=x 17*(x 19-x 12) := by linear_combination h6
  have hcpos : 0<x 19-x 12 := by rw [hc,hY]; exact mul_pos (add_pos (hx 12) (hx 13)) (mul_pos (hx 9) (hx 16))
  have hPpos : 0<x 18-x 12-x 13 := by rw [hP]; exact mul_pos (hx 17) hcpos
  have hL : x 24=(q ports x)^2-1 := by unfold q; linear_combination h0
  have hN : x 16=q ports x*(x 24+1) := by unfold q; linear_combination h1
  have hNcube : x 16=(q ports x)^3 := by rw [hN,hL]; ring
  have hq : 1<q ports x := by
    have hp := mul_pos hβ (hx 0)
    unfold q
    linarith
  have hqsq : 0<(q ports x)^2-1 := by nlinarith
  refine ⟨hPpos,hNcube,?_⟩
  have he : x 16-q ports x=q ports x*((q ports x)^2-1) := by rw [hNcube]; ring
  rw [he]
  exact mul_pos (by omega) hqsq

theorem fromOld_positive (ports : Fin 4 → ℤ) (hβ : 0<ports 0) (x : Fin 31 → ℤ)
    (hx : Positive x) (hs : ∀ k, SplitCertificate59.sourceRows ports x k=0) :
    Positive (fromOld ports x) := by
  obtain ⟨hP,_,hN⟩ := old_positive_gaps ports hβ x hx hs
  intro i
  unfold fromOld
  split_ifs <;> first | exact hP | exact hN | exact hx i

/-- A literal affine equivalence of the complete positive common zero sets. -/
def positiveZeroEquiv (ports : Fin 4 → ℤ) (hβ : 0<ports 0) :
    {x : Fin 31 → ℤ // Positive x ∧ ∀ k, rows ports x k=0} ≃
      {x : Fin 31 → ℤ // Positive x ∧ ∀ k, SplitCertificate59.sourceRows ports x k=0} where
  toFun x := ⟨toOld ports x, toOld_positive ports hβ x x.property.1,
    (zero_iff_toOld ports x).mp x.property.2⟩
  invFun x := ⟨fromOld ports x, fromOld_positive ports hβ x x.property.1 x.property.2,
    (zero_iff_fromOld ports x).mpr x.property.2⟩
  left_inv x := Subtype.ext (fromOld_toOld ports x)
  right_inv x := Subtype.ext (toOld_fromOld ports x)

theorem exists_positive_zero_iff (ports : Fin 4 → ℤ) (hβ : 0<ports 0) :
    (∃ x : Fin 31 → ℤ, Positive x ∧ ∀ k, rows ports x k=0) ↔
      ∃ x : Fin 31 → ℤ, Positive x ∧ ∀ k, SplitCertificate59.sourceRows ports x k=0 := by
  constructor
  · rintro ⟨x,hx,hs⟩
    exact ⟨toOld ports x,toOld_positive ports hβ x hx,(zero_iff_toOld ports x).mp hs⟩
  · rintro ⟨x,hx,hs⟩
    exact ⟨fromOld ports x,fromOld_positive ports hβ x hx hs,(zero_iff_fromOld ports x).mpr hs⟩

theorem positive_nat_iff (P : (Fin 31 → ℤ) → Prop) :
    (∃ x : Fin 31 → ℕ, (∀ i,0<x i) ∧ P (fun i => (x i:ℤ))) ↔
      ∃ x : Fin 31 → ℤ, Positive x ∧ P x := by
  constructor
  · rintro ⟨x,hx,hP⟩
    refine ⟨fun i => (x i:ℤ),?_,hP⟩
    intro i
    change (0:ℤ)<(x i:ℤ)
    exact_mod_cast hx i
  · rintro ⟨x,hx,hP⟩
    have hcast : (fun i => ((x i).toNat:ℤ))=x := by
      funext i
      exact Int.toNat_of_nonneg (hx i).le
    refine ⟨fun i => (x i).toNat,?_,?_⟩
    · intro i
      change 0<(x i).toNat
      have hp : (0:ℤ)<((x i).toNat:ℤ) := by
        rw [Int.toNat_of_nonneg (hx i).le]
        exact hx i
      exact_mod_cast hp
    · rw [hcast]
      exact hP

theorem exists_positive_nat_zero_iff (ports : Fin 4 → ℤ) (hβ : 0<ports 0) :
    (∃ x : Fin 31 → ℕ, (∀ i,0<x i) ∧ ∀ k, rows ports (fun i => (x i:ℤ)) k=0) ↔
      ∃ x : Fin 31 → ℕ, (∀ i,0<x i) ∧ ∀ k,
        SplitCertificate59.sourceRows ports (fun i => (x i:ℤ)) k=0 := by
  exact (positive_nat_iff (fun x => ∀ k,rows ports x k=0)).trans
    ((exists_positive_zero_iff ports hβ).trans
      (positive_nat_iff (fun x => ∀ k,SplitCertificate59.sourceRows ports x k=0)).symm)

end DiophantineConsistency.GapSource66
