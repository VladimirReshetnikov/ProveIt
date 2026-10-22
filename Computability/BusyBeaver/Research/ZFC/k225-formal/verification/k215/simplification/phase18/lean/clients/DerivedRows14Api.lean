import BusyBeaver.ZFC.TarskiLeibniz

namespace DerivedRows14Api
open SetTheory.BusyBeaver.ZFC
open Tarski (NF Rows)
open Tarski.NF

variable {T : NF → Prop}

/-- Propositional discharge requires no quantifier or equality rows. -/
theorem deduction (hC : Kalmar.Classical NF.imp NF.bot T) {a b c : NF}
    (d : Kalmar.Der NF.imp T [b, a] c) : T (imp a (imp b c)) :=
  Tarski.ded2 hC d

/-- Both shared induction steps retain their explicit vacuity premises. -/
theorem vacuity (hC : Kalmar.Classical NF.imp NF.bot T) [Rows T]
    (i j : Nat) (a b : NF) (ha : T (imp a (all i a))) (hb : T (imp b (all i b))) :
    T (imp (imp a b) (all i (imp a b))) ∧ T (imp (all j a) (all i (all j a))) :=
  ⟨Tarski.vac_imp hC ha hb, Tarski.vac_all hC ha⟩

/-- Reverse atomic transport explicitly receives symmetry, even for an arbitrary atom. -/
theorem atomic_rewrite (hC : Kalmar.Classical NF.imp NF.bot T)
    (hs : ∀ x y, T (imp (NF.eq x y) (NF.eq y x))) (P : Nat → Nat → NF)
    (hL : ∀ u v j, T (imp (NF.eq u v) (imp (P u j) (P v j))))
    (hR : ∀ u v i, T (imp (NF.eq u v) (imp (P i u) (P i v)))) (x y i j : Nat) :
    T (imp (NF.eq x y) (imp (P i j) (P (Tarski.rv x y i) (Tarski.rv x y j)))) ∧
    T (imp (NF.eq x y) (imp (P (Tarski.rv x y i) (Tarski.rv x y j)) (P i j))) :=
  ⟨Tarski.atom_subst hC P hL hR x y i j, Tarski.atom_subst_rev hC hs P hL hR x y i j⟩

#print axioms deduction
#print axioms vacuity
#print axioms atomic_rewrite
end DerivedRows14Api
