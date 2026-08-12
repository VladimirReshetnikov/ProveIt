import PolynomialFormulas.LazardInvariantModularProductBridgeCore
import PolynomialFormulas.LazardInvariantModularOrbitCount
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesRepresentativeBridge
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

/-! Executable index equivalence for the 132 degree-seven cyclic orbits. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

open LazardInvariantModularCounterexample
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularProductBridge

set_option autoImplicit false

noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem cyclicOrbitRepresentatives_seven_length :
    (orbitRepresentatives 7).length = 132 := by
  simpa [invariantOrbitCount] using cyclicSix_degreeSeven_orbit_count

private theorem eraseDups_nodup_semantic {α : Type*}
    [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        rw [List.mem_eraseDups] at ha
        simp at ha
      · exact eraseDups_nodup_semantic
          (as.filter fun b => !b == a)
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ as)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem cyclicOrbitRepresentatives_seven_nodup :
    (orbitRepresentatives 7).Nodup := by
  rw [orbitRepresentatives]
  exact eraseDups_nodup_semantic _

/-! The literal coordinate table has already been checked, in the separately
compiled representative bridge, to be exactly the executable orbit list.  We
build the index equivalence from that literal list.  Consequently its forward
map is definitionally the literal coordinate lookup; clients do not have to
normalize the 132-row bridge again merely to learn the value at one index. -/

private theorem degreeSevenRepresentativeList_length :
    degreeSevenRepresentativeList.length = 132 := by
  rfl

private theorem degreeSevenRepresentativeList_nodup :
    degreeSevenRepresentativeList.Nodup := by
  rw [degreeSevenRepresentativeList_eq_orbitRepresentatives]
  exact cyclicOrbitRepresentatives_seven_nodup

private noncomputable def degreeSevenLiteralIndexEquivOrbitRepresentative :
    Fin 132 ≃ OrbitRepresentative 7 :=
  (finCongr degreeSevenRepresentativeList_length.symm).trans
    ((List.Nodup.getEquiv degreeSevenRepresentativeList
      degreeSevenRepresentativeList_nodup).trans
        (Equiv.setCongr (Set.ext fun _ => by
          rw [degreeSevenRepresentativeList_eq_orbitRepresentatives]
          exact List.mem_toFinset.symm)))

private theorem degreeSevenRepresentative_mem_orbitRepresentatives
    (i : Fin 132) :
    degreeSevenRepresentative i ∈ (orbitRepresentatives 7).toFinset := by
  rw [← degreeSevenRepresentativeList_eq_orbitRepresentatives,
    List.mem_toFinset]
  let j : Fin degreeSevenRepresentativeList.length :=
    ⟨i.1, by simpa [degreeSevenRepresentativeList_length] using i.isLt⟩
  change degreeSevenRepresentativeList.getD j.1 (fun _ => 0) ∈
    degreeSevenRepresentativeList
  rw [List.getD_eq_get degreeSevenRepresentativeList (fun _ => 0) j]
  exact List.get_mem _ _

private def degreeSevenLiteralOrbitRepresentative (i : Fin 132) :
    OrbitRepresentative 7 :=
  ⟨degreeSevenRepresentative i,
    degreeSevenRepresentative_mem_orbitRepresentatives i⟩

private theorem degreeSevenLiteralOrbitRepresentative_eq_equiv_apply
    (i : Fin 132) :
    degreeSevenLiteralOrbitRepresentative i =
      degreeSevenLiteralIndexEquivOrbitRepresentative i := by
  apply Subtype.ext
  let j : Fin degreeSevenRepresentativeList.length :=
    finCongr degreeSevenRepresentativeList_length.symm i
  change degreeSevenRepresentativeList.getD j.1 (fun _ => 0) =
    degreeSevenRepresentativeList.get j
  exact List.getD_eq_get degreeSevenRepresentativeList (fun _ => 0) j

/-- The literal coordinate indices enumerate the canonical degree-seven
cyclic-orbit representatives.  Its forward map deliberately exposes the
literal lookup, while bijectivity is transported from `List.Nodup.getEquiv`. -/
noncomputable def degreeSevenIndexEquivOrbitRepresentative :
    Fin 132 ≃ OrbitRepresentative 7 :=
  Equiv.ofBijective degreeSevenLiteralOrbitRepresentative (by
    have hfun :
        degreeSevenLiteralOrbitRepresentative =
          (degreeSevenLiteralIndexEquivOrbitRepresentative :
            Fin 132 → OrbitRepresentative 7) := by
      funext i
      exact degreeSevenLiteralOrbitRepresentative_eq_equiv_apply i
    rw [hfun]
    exact degreeSevenLiteralIndexEquivOrbitRepresentative.bijective)

end


end LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants
