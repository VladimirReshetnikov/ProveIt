import PA194SourceListPreimage
import PA194SourceLK
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA194Logic PA194Logic.Relational

def refutesAllList (xs : List (Proposition language))
    (p : Semiproposition language 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hlz : lo < z)
    (hz : ∀ q,q ∈ xs → lo+1+depth q ≤ z)
    (d : Refutes ((xs : SourceSequent).map Semiformula.shift + ⦃p.free⦄) (shiftedLabels f lo) (lo+1) z) :
    Refutes ((xs : SourceSequent) + ⦃Semiformula.all p⦄) f lo z := by
  intro C h
  let K := negativeContext xs Fin.elim0 f (lo+1) z
  have hs : ∀ q,q ∈ (xs : SourceSequent).map Semiformula.shift →
      Context K (wn (code q (shiftedLabels f lo) (lo+1) z)) := by
    intro q hq
    let pre := findPreimage xs Semiformula.shift q (by simpa using hq)
    have hc : Context K (wn (code pre.val f (lo+1) z)) :=
      .assumption (List.mem_map.mpr ⟨pre.val,pre.property.1,rfl⟩)
    rw [← pre.property.2]
    simpa only [code,toNamed_shift] using hc
  let body := d.positive hs
  have hb : Context K (relationalCode z
      (toNamed p (Fin.cases lo Fin.elim0) f (lo+1))) := by
    simpa only [code,toNamed_free] using body
  let hg := generalizeNegativeContext xs Fin.elim0 f (lo+1) lo z hlo
    (by omega) (fun i => Fin.elim0 i) (fun i => Nat.ne_of_lt (hf i)) (by omega) hb
  have hu : Context C (code (.all p) f lo z) := hg.cut
    (negativeContextSupply xs f (lo+1) z (fun q hq => by
      let hr := reallocation q Fin.elim0 f lo (lo+1) z hlo (by omega)
        (fun i => Fin.elim0 i) (fun i => by simpa using hf i)
        (by have hh := hz q hq; omega)
      exact Context.mp (h q (Multiset.mem_add.mpr (Or.inl (by simpa using hq)))) (.closed (Bi.neg hr).1)))
  exact Context.mp hu (h (.all p) (by simp))
#print axioms refutesAllList
end PA194Logic.Relational.Source
