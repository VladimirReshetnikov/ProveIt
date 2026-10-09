import GowersSzemeredi.Proofs16BalancedIncidenceSelection

/-! A higher arrangement prescribes two anchor values at each of four
shifts. A global assignment realizes it exactly when these restrictions
hold; reconstruction retains all eleven original parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementShifts {N : Nat} (p : HigherArrangementParameter N) : Fin 4 → ZMod N :=
  ![p.1.1,p.1.2 0,p.1.2 1,p.1.1+p.1.2 0-p.1.2 1]
def higherArrangementAnchorValues {N : Nat} (p : HigherArrangementParameter N) : Fin 4 → ZMod N × ZMod N :=
  ![(p.2,p.1.2 5),(p.1.2 2,p.1.2 6),(p.1.2 3,p.1.2 7),(p.1.2 4,p.1.2 8)]
def RealizesHigherArrangement {N : Nat} (g : ZMod N → ZMod N × ZMod N)
    (p : HigherArrangementParameter N) : Prop :=
  ∀ j, g (higherArrangementShifts p j) = higherArrangementAnchorValues p j

theorem higherArrangementShifts_additive {N : Nat} (p : HigherArrangementParameter N) :
    higherArrangementShifts p 0+higherArrangementShifts p 1 =
      higherArrangementShifts p 2+higherArrangementShifts p 3 := by
  dsimp [higherArrangementShifts]
  ring

theorem RealizesHigherArrangement.reconstruct {N : Nat}
    (g : ZMod N → ZMod N × ZMod N) (p : HigherArrangementParameter N)
    (h : RealizesHigherArrangement g p) :
    shiftAnchorArrangement (fun a => (g a).1) (fun a => (g a).2) (higherArrangementShifts p) = p := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  dsimp [higherArrangementShifts,higherArrangementAnchorValues] at h0 h1 h2 h3
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      fin_cases j <;> dsimp [shiftAnchorArrangement,higherArrangementShifts]
      all_goals first | rfl | exact congrArg Prod.fst h1 | exact congrArg Prod.fst h2 |
        exact congrArg Prod.fst h3 | exact congrArg Prod.snd h0 | exact congrArg Prod.snd h1 |
        exact congrArg Prod.snd h2 | exact congrArg Prod.snd h3
  · exact congrArg Prod.fst h0

theorem higherArrangementShifts_injOn_realizations {N : Nat}
    (g : ZMod N → ZMod N × ZMod N) (H : Finset (HigherArrangementParameter N)) :
    Set.InjOn higherArrangementShifts (↑(H.filter (RealizesHigherArrangement g)) : Set (HigherArrangementParameter N)) := by
  intro p hp q hq he
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  calc p = shiftAnchorArrangement (fun a => (g a).1) (fun a => (g a).2) (higherArrangementShifts p) :=
         (RealizesHigherArrangement.reconstruct g p hp').symm
    _ = shiftAnchorArrangement (fun a => (g a).1) (fun a => (g a).2) (higherArrangementShifts q) := by rw [he]
    _ = q := RealizesHigherArrangement.reconstruct g q hq'

theorem higher_anchor_restriction_balance {N : Nat} [NeZero N]
    (p : HigherArrangementParameter N) (hp : Function.Injective (higherArrangementShifts p)) :
    ((Finset.univ.filter fun g : ZMod N → ZMod N × ZMod N => RealizesHigherArrangement g p).card)*N^8 =
      Fintype.card (ZMod N → ZMod N × ZMod N) := by
  have h := coordinate_restriction_fiber_balance (higherArrangementShifts p) hp (higherArrangementAnchorValues p)
  simp only [Fintype.card_prod,ZMod.card,Fintype.card_fin,← pow_two,← pow_mul] at h
  simp only [Nat.reduceMul] at h
  convert h using 1
  congr 2
  ext g
  simp [RealizesHigherArrangement]

end LeanProofs.GowersSzemeredi
