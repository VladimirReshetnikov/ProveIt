import DiophantineConsistency.Norm38MacroV1Value
import DiophantineConsistency.Norm38MacroCheckpoint27to34
import DiophantineConsistency.Norm38MacroCheckpoint34to41

/-! Candidate shared last-prefix lookups and symbolic C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointBdCd
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding Norm38MacroPrefixGroup01
  Norm38MacroCheckpointC Norm38MacroCheckpoint27to34 Norm38MacroCheckpoint34to41

theorem lookup39_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 39) :
    d41.values a i.castSucc.castSucc = d39.values a i := by
  have path : PrefixPath d39 d41 (fun i => i.castSucc.castSucc) := by
    change PrefixPath d39 (Dag.snoc (Dag.snoc d39 _) _) _
    exact PrefixPath.step (PrefixPath.step (PrefixPath.base d39) _) _
  exact lookup path a i

theorem lookup40_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 40) :
    d41.values a i.castSucc = d40.values a i := by
  have path : PrefixPath d40 d41 (fun i => i.castSucc) := by
    change PrefixPath d40 (Dag.snoc d40 _) _
    exact PrefixPath.step (PrefixPath.base d40) _
  exact lookup path a i

theorem d41_C_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩ := by
  calc
    d41.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a (Fin.last 26) := lookup27_34 a (Fin.last 26)
    _ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩ := d27_C_value a

#print axioms lookup39_41
#print axioms lookup40_41
#print axioms d41_C_value
end DiophantineConsistency.Norm38MacroCheckpointBdCd
