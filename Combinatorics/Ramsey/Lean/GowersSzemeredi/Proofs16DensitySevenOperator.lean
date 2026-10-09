import GowersSzemeredi.Proofs16GlobalSevenOperatorTheorem

/-! The global seven-operator theorem with parameters depending only on the
initial density. The auxiliary extraction error is fixed explicitly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def densitySevenParameters (alpha : Real) : CompletionParameters :=
  globalSevenParameters alpha ((alpha / (2 - alpha))^4 / 2)

def densitySevenModulusBound (alpha : Real) : Nat :=
  globalSevenModulusBound alpha ((alpha / (2 - alpha))^4 / 2)

/-- The global progression and all bounds depend only on the input density. -/
theorem density_seven_operator_proper_progression {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : densitySevenModulusBound alpha ≤ N) :
    let p := densitySevenParameters alpha
    ∃ (k : Nat) (F : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N)
      (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N),
      k ≤ p.mapCap ∧ F.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      P.rank ≤ p.spectrumCap + 1 ∧ P.Proper ∧ 0 ∈ P.carrier ∧
      (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧
      0 < p.targetRadius ∧ 0 < p.targetDensity ∧ p.targetDensity * N ≤ P.carrier.card ∧
      (∀ j, FreimanHom 2 P.carrier (L j) ∧ L j 0 = 0) ∧
      ∀ y ∈ P.carrier, ∀ x ∈ bohr (F ∪ Finset.univ.image (fun j => L j y)) p.targetRadius,
        (x, y) ∈ horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  have hbeta : 0 < alpha / (2 - alpha) := div_pos ha (by linarith)
  exact global_seven_operator_proper_progression A ha ha1 (by positivity)
    (by have h := pow_pos hbeta 4; linarith) hA hN

/-- The uniform row radius is strictly positive independently of the modulus. -/
theorem densitySevenParameters_targetRadius_pos (alpha : Real) :
    0 < (densitySevenParameters alpha).targetRadius := by
  apply CompletionParameters.targetRadius_pos
  dsimp [densitySevenParameters, globalSevenParameters]
  positivity

end LeanProofs.GowersSzemeredi
