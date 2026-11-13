import DiophantineConsistency.Compact44.FixedGraphAnchoredMatch
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFieldCastBridge
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ

theorem lookup_row (f : Quad → ℕ) (lookup : V → V)
    (hlookup : ∀ m : ℕ, lookup (m:V)=((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))):V))
    (i : Fin 943) : lookup (i.val:V)=((f (Compact943Data.row i)):V) := by
  rw [hlookup]
  have hi : i.val<Compact943Data.rows.length := by simpa only [Compact943Data.rows_length] using i.isLt
  simp only [List.getElem?_toArray, getElem?_pos Compact943Data.rows i.val hi, Option.getD_some]
  rfl
theorem lookup_matches (lookup : (Quad → ℕ) → V → V)
    (hlookup : ∀ f : Quad → ℕ, f (0,0,0,0)=0 → ∀ m : ℕ,
      lookup f (m:V)=((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))):V))
    (b : V → V) (N s : V) (hN : 0<N)
    (hfields : ∀ h<N, ∃ i j l : Fin 943, b h=(i.val:V) ∧ b (ArithmeticCyclicWord.cyc N h s)=(j.val:V) ∧
      b (ArithmeticCyclicWord.cyc N h 1)=(l.val:V) ∧
      (Compact943Data.row i).2.2.2=(Compact943Data.row j).2.1 ∧
      (Compact943Data.row i).2.2.1=(Compact943Data.row l).1) :
    (∀ h<N, ∀ g<N, (g+1)%N=h → lookup (fun t => t.2.2.1) (b h)=lookup (fun t => t.1) (b g)) ∧
    (∀ h<N, ∀ g<N, (g+s)%N=h → lookup (fun t => t.2.2.2) (b h)=lookup (fun t => t.2.1) (b g)) := by
  constructor
  · intro h hh g hg he
    have hprev : ArithmeticCyclicWord.cyc N h 1=g := by rw [←he]; exact BlockOrbit.forward_back N g 1 hN hg
    obtain ⟨i,j,l,hi,hj,hl,hv,heq⟩ := hfields h hh
    rw [hprev] at hl
    rw [hi,hl,lookup_row _ _ (hlookup _ rfl) i,lookup_row _ _ (hlookup _ rfl) l,heq]
  · intro h hh g hg he
    have hprev : ArithmeticCyclicWord.cyc N h s=g := by rw [←he]; exact BlockOrbit.forward_back N g s hN hg
    obtain ⟨i,j,l,hi,hj,hl,hv,heq⟩ := hfields h hh
    rw [hprev] at hj
    rw [hi,hj,lookup_row _ _ (hlookup _ rfl) i,lookup_row _ _ (hlookup _ rfl) j,hv]
#print axioms CompactFieldCastBridge.lookup_row
#print axioms CompactFieldCastBridge.lookup_matches
end CompactFieldCastBridge
