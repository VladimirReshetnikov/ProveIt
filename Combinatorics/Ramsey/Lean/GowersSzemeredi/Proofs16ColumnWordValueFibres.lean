import GowersSzemeredi.Proofs16ColumnWords

/-! Words with one fixed alternating value occupy one codimension-one fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnWordValueFibre {N k : Nat} [NeZero N] (c : ZMod N) : Finset (ColumnWord N (k+1)) :=
  Finset.univ.filter (fun w => columnWordValue w = c)

theorem columnWordValueFibre_card_le {N k : Nat} [NeZero N] (c : ZMod N) :
    (columnWordValueFibre (k := k) c).card ≤ N^(3*k+2) := by
  have h := Finset.card_le_card_of_injOn
    (s := columnWordValueFibre (k := k) c)
    (t := (Finset.univ : Finset ((ZMod N × ZMod N) × ColumnWord N k)))
    (fun w => (w.1.2,w.2)) (by simp) (by
      intro p hp q hq he
      have hm : p.1.2 = q.1.2 := congrArg Prod.fst he
      have ht : p.2 = q.2 := congrArg (fun v : (ZMod N × ZMod N) × ColumnWord N k => v.2) he
      have ep := (Finset.mem_filter.mp hp).2
      have eq := (Finset.mem_filter.mp hq).2
      have hf : p.1.1 = q.1.1 := by
        change p.1.1-p.1.2.1+p.1.2.2-columnWordValue p.2 = c at ep
        change q.1.1-q.1.2.1+q.1.2.2-columnWordValue q.2 = c at eq
        rw [hm,ht] at ep
        linear_combination ep-eq
      exact Prod.ext (Prod.ext hf hm) ht)
  simpa [columnWord_card,pow_add,pow_two,mul_assoc,mul_comm,mul_left_comm] using h

end LeanProofs.GowersSzemeredi
