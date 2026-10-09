import GowersSzemeredi.Proofs16UniformCompletionState

/-! Uniform numerical parameters for the final three directional operations.
Every bound is determined before choosing the finite ambient group. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

structure CompletionParameters where
  fixedCap : Nat
  domainCap : Nat
  mapCap : Nat
  domainRadius : Real
  rowRadius : Real
  density : Real

namespace CompletionParameters

def frequencyCap (p : CompletionParameters) : Nat := p.fixedCap + p.mapCap * p.mapCap + 2 * p.mapCap
def initialStateCap (p : CompletionParameters) : Nat := max p.domainCap p.fixedCap
def domainCells (p : CompletionParameters) : Nat := ⌈4 / p.domainRadius⌉₊
def fixedCells (p : CompletionParameters) : Nat := ⌈(2 : Real)^p.mapCap / p.rowRadius⌉₊
def modulusBound (p : CompletionParameters) : Nat :=
  uniformCompletionModulusBound p.density p.domainCells p.fixedCells p.frequencyCap p.mapCap p.initialStateCap
def stateBound (p : CompletionParameters) : Nat :=
  uniformCompletionStateBound p.density p.domainCells p.fixedCells p.frequencyCap p.mapCap p.initialStateCap
def spectrumCap (p : CompletionParameters) : Nat :=
  ⌈16 / (p.density / (p.domainCells : Real)^p.stateBound)^2⌉₊
def targetRadius (p : CompletionParameters) : Real := p.rowRadius / (2 : Real)^p.mapCap / 4 / 2
def targetDensity (p : CompletionParameters) : Real :=
  Real.exp (-(((p.spectrumCap : Real) + 1) * Real.log (1 + Real.pi) +
    10 * ((p.spectrumCap : Real) + 1)^2))

theorem domainCells_pos (p : CompletionParameters) (h : 0 < p.domainRadius) : 0 < p.domainCells := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem fixedCells_pos (p : CompletionParameters) (h : 0 < p.rowRadius) : 0 < p.fixedCells := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem domainCells_bound (p : CompletionParameters) (h : 0 < p.domainRadius) :
    4 ≤ p.domainRadius * p.domainCells := by
  have hb : 4 / p.domainRadius ≤ (p.domainCells : Real) := Nat.le_ceil _
  have := (div_le_iff₀ h).mp hb
  nlinarith only [this]

theorem fixedCells_bound (p : CompletionParameters) (h : 0 < p.rowRadius) :
    (2 : Real)^p.mapCap ≤ p.rowRadius * p.fixedCells := by
  have hb : (2 : Real)^p.mapCap / p.rowRadius ≤ (p.fixedCells : Real) := Nat.le_ceil _
  have := (div_le_iff₀ h).mp hb
  nlinarith only [this]

theorem targetRadius_pos (p : CompletionParameters) (h : 0 < p.rowRadius) : 0 < p.targetRadius := by
  unfold targetRadius
  positivity

theorem targetDensity_pos (p : CompletionParameters) : 0 < p.targetDensity := Real.exp_pos _

end CompletionParameters
end LeanProofs.GowersSzemeredi
