import PA195LocalQuotient
import M6.Native

/-! The exact unfolded PA195 parent satisfies the reusable four register-box
lemmas of the imported M6 runtime. This is an arbitrary-register, standard-Nat
semantic theorem, not a source-program simulation or an internal PRA proof. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195RuntimeEngine
open PA195LocalQuotient M6.Zip M6.Runtime M6.Native M6.Reference230

def machine (q : Nat) (bit : Bool) : Option (Bool × Bool × Nat) :=
  (lookup parent q bit).map fun r => (r.write, r.right, r.target)

theorem exact_engine_rows :
    boxRows.all (fun r => machine r.1 r.2 == tm230 r.1 r.2) = true := by decide +kernel

theorem engine_agrees : AgreeRows machine tm230 boxRows := by
  intro r hr
  have h := (List.all_eq_true.mp exact_engine_rows) r hr
  exact beq_iff_eq.mp h

theorem append_one : IncTail1 machine := by
  change machine 198 false = some (true, false, 40)
  decide +kernel

theorem box_lemmas : BoxLemmas machine := boxLemmas engine_agrees append_one

/-- A checked symbolic execution on the actual unfolded table gives an
exact, positive physical run for every gap and valid register file. The
symbolic execution equality remains an explicit hypothesis. -/
theorem symbolic_segment (br : Branch) (tgt : SConf → Bool)
    (n fuel : Nat) (vs : List Nat) (hv : Valid br vs) (s s' : SConf)
    (h : exec machine br tgt fuel s false = some s') :
    tgt s' = true ∧ Reach machine (conc n vs s) (conc n vs s') ∧
      Reach1 machine (conc n vs s) (conc n vs s') := by
  obtain ⟨ht, hr, hp⟩ := exec_sound box_lemmas n hv fuel s false s' h
  exact ⟨ht, hr, hp rfl⟩

#print axioms symbolic_segment
#print axioms exact_engine_rows
#print axioms append_one
#print axioms box_lemmas
end PA195RuntimeEngine
