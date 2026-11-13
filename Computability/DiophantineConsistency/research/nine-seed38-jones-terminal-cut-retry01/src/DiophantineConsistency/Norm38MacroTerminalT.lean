import DiophantineConsistency.Norm38MacroKcValue
import DiophantineConsistency.Norm38MacroPath18to41
import DiophantineConsistency.Norm38MacroPrefixInputsB
import DiophantineConsistency.Norm38MacroDependentOutput

/-! Candidate exact terminal cuts with earlier nodes kept as symbolic values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroTerminalCut
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding
  Norm38MacroPath18to41 Norm38MacroDependent08

def terminalT {R : Type*} [CommRing R] (bd cd kc v0 v1 t : R) : R :=
  bd * t + cd - kc * (cd + v0 * v1)

def terminalOutput {R : Type*} [CommRing R] (t kc a0 a1 v0 : R) : R :=
  (t ^ (2 : Nat) + kc ^ (2 : Nat) * a0 - kc ^ (2 : Nat) * v0 ^ (2 : Nat) * a1) ^ (2 : Nat) -
    ((4 : Int) : R) * t ^ (2 : Nat) * kc ^ (2 : Nat) * a0

theorem lookup41_43 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 41) :
    d43.values a i.castSucc.castSucc = d41.values a i := by
  have path : PrefixPath d41 d43 (fun i => i.castSucc.castSucc) := by
    change PrefixPath d41 (Dag.snoc (Dag.snoc d41 _) _) _
    exact PrefixPath.step (PrefixPath.step (PrefixPath.base d41) _) _
  exact lookup path a i

theorem lookup41_44 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 41) :
    d44.values a i.castSucc.castSucc.castSucc = d41.values a i := by
  have path : PrefixPath d41 d44 (fun i => i.castSucc.castSucc.castSucc) := by
    change PrefixPath d41 (Dag.snoc (Dag.snoc (Dag.snoc d41 _) _) _) _
    exact PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d41) _) _) _
  exact lookup path a i

theorem d41_t_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 17).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨8, by decide⟩ := by
  exact (lookup18_41 a (Fin.last 17)).trans (Norm38MacroPrefixGroup04.prefix_t a)

theorem d44_T_cut {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d44.values a (Fin.last 43) = terminalT (d41.values a ⟨39, by decide⟩)
      (d41.values a ⟨40, by decide⟩) (d43.values a (Fin.last 42))
      (d41.values a ⟨37, by decide⟩) (d41.values a ⟨38, by decide⟩) (a ⟨8, by decide⟩) := by
  rw [prefix_T]
  have h39 : d43.values a ⟨39, by decide⟩ = d41.values a ⟨39, by decide⟩ := by
    have hi : ((⟨39, by decide⟩ : Fin 41).castSucc.castSucc) = (⟨39, by decide⟩ : Fin 43) := by decide
    simpa only [hi] using lookup41_43 a ⟨39, by decide⟩
  have h17 : d43.values a ⟨17, by decide⟩ = d41.values a ⟨17, by decide⟩ := by
    have hi : ((⟨17, by decide⟩ : Fin 41).castSucc.castSucc) = (⟨17, by decide⟩ : Fin 43) := by decide
    simpa only [hi] using lookup41_43 a ⟨17, by decide⟩
  have h40 : d43.values a ⟨40, by decide⟩ = d41.values a ⟨40, by decide⟩ := by
    have hi : ((⟨40, by decide⟩ : Fin 41).castSucc.castSucc) = (⟨40, by decide⟩ : Fin 43) := by decide
    simpa only [hi] using lookup41_43 a ⟨40, by decide⟩
  have h37 : d43.values a ⟨37, by decide⟩ = d41.values a ⟨37, by decide⟩ := by
    have hi : ((⟨37, by decide⟩ : Fin 41).castSucc.castSucc) = (⟨37, by decide⟩ : Fin 43) := by decide
    simpa only [hi] using lookup41_43 a ⟨37, by decide⟩
  have h38 : d43.values a ⟨38, by decide⟩ = d41.values a ⟨38, by decide⟩ := by
    have hi : ((⟨38, by decide⟩ : Fin 41).castSucc.castSucc) = (⟨38, by decide⟩ : Fin 43) := by decide
    simpa only [hi] using lookup41_43 a ⟨38, by decide⟩
  have hit : (⟨17, by decide⟩ : Fin 41) = ((Fin.last 17).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hik : (⟨42, by decide⟩ : Fin 43) = Fin.last 42 := by decide
  rw [h39, h17, h40, h37, h38, hit, d41_t_value, hik]
  rfl

#print axioms lookup41_43
#print axioms lookup41_44
#print axioms d41_t_value
#print axioms d44_T_cut
end DiophantineConsistency.Norm38MacroTerminalCut
