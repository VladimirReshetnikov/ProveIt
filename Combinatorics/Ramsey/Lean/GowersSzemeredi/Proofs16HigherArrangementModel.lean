import GowersSzemeredi.Proofs16OffsetFreimanRetention

/-! Eleven free parameters encode the sixteen endpoints in the higher
arrangement: four matched shifts, with the fourth shift determined by
a1+a2=a3+a4. The first unshifted endpoint is separated for extraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev HigherArrangementIndex (N : Nat) := ZMod N × (Fin 9 → ZMod N)
abbrev HigherArrangementParameter (N : Nat) := HigherArrangementIndex N × ZMod N

def higherArrangementEndpoints {N : Nat} (p : HigherArrangementParameter N) : Fin 16 → ZMod N :=
  let a := p.1.1
  let z := p.1.2
  ![p.2+a,p.2,z 2+z 0,z 2,z 3+z 1,z 3,z 4+(a+z 0-z 1),z 4,
    z 5+a,z 5,z 6+z 0,z 6,z 7+z 1,z 7,z 8+(a+z 0-z 1),z 8]

def HigherArrangementEquation {N : Nat} (f : Fin 16 → ZMod N → ZMod N)
    (p : HigherArrangementParameter N) : Prop :=
  let e := higherArrangementEndpoints p
  (f 0 (e 0)-f 1 (e 1))+(f 2 (e 2)-f 3 (e 3))+
    (f 4 (e 4)-f 5 (e 5))+(f 6 (e 6)-f 7 (e 7)) =
  (f 8 (e 8)-f 9 (e 9))+(f 10 (e 10)-f 11 (e 11))+
    (f 12 (e 12)-f 13 (e 13))+(f 14 (e 14)-f 15 (e 15))

def higherArrangementResidual {N : Nat} (f : Fin 16 → ZMod N → ZMod N)
    (i : HigherArrangementIndex N) : ZMod N :=
  let a := i.1
  let z := i.2
  ((f 8 (z 5+a)-f 9 (z 5))+(f 10 (z 6+z 0)-f 11 (z 6))+
    (f 12 (z 7+z 1)-f 13 (z 7))+(f 14 (z 8+(a+z 0-z 1))-f 15 (z 8))) -
  ((f 2 (z 2+z 0)-f 3 (z 2))+(f 4 (z 3+z 1)-f 5 (z 3))+
    (f 6 (z 4+(a+z 0-z 1))-f 7 (z 4)))

theorem higherArrangementEquation_offset {N : Nat} (f : Fin 16 → ZMod N → ZMod N)
    (p : HigherArrangementParameter N) (h : HigherArrangementEquation f p) :
    f 0 (p.2+p.1.1)-f 1 p.2 = higherArrangementResidual f p.1 := by
  dsimp [HigherArrangementEquation,higherArrangementEndpoints] at h
  dsimp [higherArrangementResidual]
  linear_combination h

theorem higherArrangement_offset_fibre_card {N : Nat} [NeZero N] (a : ZMod N) :
    ((Finset.univ : Finset (HigherArrangementIndex N)).filter fun i => i.1 = a).card = N^9 := by
  have heq : ((Finset.univ : Finset (HigherArrangementIndex N)).filter fun i => i.1 = a) =
      {a} ×ˢ (Finset.univ : Finset (Fin 9 → ZMod N)) := by
    ext ⟨b,z⟩
    simp [eq_comm]
  rw [heq]
  simp only [Finset.card_product,Finset.card_singleton,one_mul,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,ZMod.card]

/-- The representation has exactly eleven free coordinates, as required
by the higher-arrangement density normalization. -/
theorem higherArrangement_parameter_card {N : Nat} [NeZero N] :
    Fintype.card (HigherArrangementParameter N) = N^11 := by
  simp only [HigherArrangementParameter,HigherArrangementIndex,Fintype.card_prod,Fintype.card_fun,
    Fintype.card_fin,ZMod.card]
  ring

end LeanProofs.GowersSzemeredi
