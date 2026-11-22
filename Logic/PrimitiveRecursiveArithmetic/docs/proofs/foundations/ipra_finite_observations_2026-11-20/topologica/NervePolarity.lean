import ConciseIPRA.PR

/-! The incidence-polarity unit in object iPRA, for arbitrary arithmetic
    predicates A and R. The left-to-right assertion says that x lies in every
    cover member containing A whenever x belongs to A. The second unit follows
    from this one by transposing the incidence relation. -/

namespace NervePolarity

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

private abbrev memAt {k : Nat} (A : Fm PTm 1) (x : PTm k) := A.subst (fun _ => x)
private abbrev incAt {k : Nat} (R : Fm PTm 2) (x i : PTm k) := R.subst (Fin.cases x (fun _ => i))

private theorem subst_mem {j k : Nat} (A : Fm PTm 1) (x : PTm j) (s : Fin j → PTm k) :
    (memAt A x).subst s = memAt A (Syn.subst s x) := by
  simp only [memAt, Fm.subst_subst]

private theorem subst_inc {j k : Nat} (R : Fm PTm 2) (x y : PTm j) (s : Fin j → PTm k) :
    (incAt R x y).subst s = incAt R (Syn.subst s x) (Syn.subst s y) := by
  simp only [incAt, Fm.subst_subst]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- ∀ x i, (A(x) ∧ ∀z (A(z) → R(z,i))) → R(x,i). -/
def unitFormula (A : Fm PTm 1) (R : Fm PTm 2) : Fm PTm 0 :=
  Fm.all (Fm.all ((memAt A (var 1) ⋏
    Fm.all (memAt A (var 0) ⟶ incAt R (var 0) (var 1))) ⟶
    incAt R (var 1) (var 0)))

theorem prove_unit (A : Fm PTm 1) (R : Fm PTm 2) :
    [] ⊢[PRAAx] unitFormula A R := by
  refine .allI (.allI (.impI ?_))
  have hyp : (memAt A (var (1 : Fin 2)) ⋏ Fm.all (memAt A (var 0) ⟶ incAt R (var 0) (var 1))) ::
      [] ⊢[PRAAx] (memAt A (var 1) ⋏ Fm.all (memAt A (var 0) ⟶ incAt R (var 0) (var 1))) :=
    Prf.hyp0
  have hi := Prf.allE (var (1 : Fin 2)) (Prf.andE₂ hyp)
  simp only [Fm.subst_imp, subst_mem, subst_inc, Syn.subst_var, Syn.inst_zero] at hi
  exact .impE hi (.andE₁ hyp)

end NervePolarity
