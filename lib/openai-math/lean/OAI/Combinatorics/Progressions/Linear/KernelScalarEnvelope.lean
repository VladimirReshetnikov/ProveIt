import OAI.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget

namespace OAI

section

namespace Erdos3

def kernelInverseEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D + D^2 + D*(D*(D+1)) + D*(D*D+D*(D^2+D+p+2))

def kernelGeometryEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  p+D+D+D*(D+1)+kernelInverseEnvelope D p

def kernelOutputEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D^2+(D+1)*kernelGeometryEnvelope D p+(D+D+(D+1)*p)+
    D*(kernelGeometryEnvelope D p+1)+
    (4*kernelGeometryEnvelope D p+D+D+D*D+2)+1

theorem kernelInverseEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelInverseEnvelope D p := by
  unfold kernelInverseEnvelope
  positivity

theorem kernelGeometryEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseEnvelope_nonneg hD hp
  unfold kernelGeometryEnvelope
  positivity

theorem kernelOutputEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelOutputEnvelope D p := by
  have hg := kernelGeometryEnvelope_nonneg hD hp
  unfold kernelOutputEnvelope
  positivity

theorem kernelInverseLog_le_envelope {q n j d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelInverseLog q n j d p ≤ kernelInverseEnvelope D p := by
  have hj' : ((j-1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le j 1)).trans hj
  unfold kernelInverseLog kernelInverseEnvelope
  gcongr

theorem kernelGeometryLog_le_envelope {q n j k d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelGeometryLog q n j k d p ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseLog_le_envelope hD hp hq hn hj hd
  unfold kernelGeometryLog kernelGeometryEnvelope
  gcongr

theorem kernelRowOutputLog_le_envelope {q n j k u d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hu : (u : ℝ) ≤ D)
    (hd : (d : ℝ) ≤ D) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    kernelRowOutputLog q n j k u d p ≤ kernelOutputEnvelope D p := by
  have hG := kernelGeometryLog_le_envelope hD hp hq hn hj hk hd
  have hG0 := (kernelGeometryLog_bounds q n j k d hp).1
  have hGe := kernelGeometryEnvelope_nonneg hD hp
  dsimp only [kernelRowOutputLog, kernelOutputEnvelope, affineProfileLogBound, jetOutputRadiusLog]
  gcongr

end Erdos3

end

end OAI
