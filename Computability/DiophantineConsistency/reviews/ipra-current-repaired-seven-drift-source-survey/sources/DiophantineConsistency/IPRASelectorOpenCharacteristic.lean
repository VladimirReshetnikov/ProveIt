import DiophantineConsistency.IPRASelectorStability
import DiophantineConsistency.IPRABoundedSelector
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASelectorOpenCharacteristic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRANativeFormula IPRANativeTheory IPRANativeOpenDecidable IPRANativeFormulaRew IPRASelectorStability
open PRAFiniteFunctionCodes PRALanguage IPRATheoryHilbertBridge
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def openCharacteristic {φ : Semipropositionᵢ language 1} (χ : Semiproposition language 1)
    (hopen : χ.Open) (t : Term language ℕ)
    (hf : extended nativeTheory ⊢! Rewriting.free φ 🡒 Rewriting.free (native χ))
    (hs : extended nativeTheory ⊢! Rewriting.free (native χ) 🡒 Rewriting.shift ((native χ)/[t]))
    (hb : extended nativeTheory ⊢! ((native χ)/[t]) 🡒 φ/[t]) :
    extended nativeTheory ⊢! ∼∼(∃⁰ φ) 🡒 ∃⁰ φ := by
  have ho : (χ/[t]).Open := by simpa using hopen
  have hstab := openStable (χ/[t]) ho
  have hrewrite : (native χ)/[t] = native (χ/[t]) := by
    simp only [← native_rew]
  exact stableExistsOfCharacteristic φ (native χ) t hf hs (by simpa only [hrewrite] using hstab) hb
end DiophantineConsistency.IPRASelectorOpenCharacteristic
