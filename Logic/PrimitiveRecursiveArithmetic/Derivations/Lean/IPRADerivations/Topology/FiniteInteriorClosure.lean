import IPRADerivations.Foundations.IntersectionEnumeration
import IPRADerivations.Algebra.AdjugateInverse

/-!
# Interior and closure on a finite specialization preorder

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, Theorems
`thm:finite-intcl` (F03: "`Int A = {x : (∀y)(x ≼ y ⇒ y ∈ A)}`, `Cl A = {x : (∃y)(x ≼ y ∧ y ∈ A)}`. The first is
the greatest open subset of `A`, and the second is the least closed superset of `A`") and `thm:finite-laws`
(F04: monotonicity, `Int(A ∩ B) = Int A ∩ Int B`, `Cl(A ∪ B) = Cl A ∪ Cl B`, `Int(A^c) = (Cl A)^c`).

A finite space is `Fin k` with a preorder `rel` (finite data); a subset is a family `A : Fin k → Fm PTm n` of
arbitrary iPRA formulas (open: upward closed, closed: downward closed, both as derived implications).
`Int A x` is the finite conjunction of `A y` over the successors `y` of `x`, `Cl A x` the finite disjunction.
(F01, the topology of upward-closed sets, and F06, continuity as monotonicity, are
`Topology/FinitePreorder` for arbitrary first-order relations.)

* `int_sub`, `int_open`, `int_greatest`: `Int A ⊆ A`, `Int A` is open, every open `U ⊆ A` lies in `Int A`;
* `sub_cl`, `cl_closed`, `cl_least`: `A ⊆ Cl A`, `Cl A` is closed, every closed `D ⊇ A` contains `Cl A`;
* `int_mono`, `cl_mono`;
* `int_inter`, `cl_union`: `Int(A ∧ B) ↔ Int A ∧ Int B`, `Cl(A ∨ B) ↔ Cl A ∨ Cl B`;
* `int_neg`: `Int(¬A) ↔ ¬Cl A`, intuitionistically and without decidability of `A`.
-/

namespace LeanProofs.IPRA.Topology.FiniteInteriorClosure

open_ipra
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Algebra.AdjugateInverse (conjFin_elim)

variable {n k : ℕ} {Γ : List (Fm PTm n)}
variable (rel : Fin k → Fin k → Prop) [DecidableRel rel]

/-- `⊤`. -/
abbrev truth : Fm PTm n := ConciseIPRA.PTm.zero ≐ ConciseIPRA.PTm.zero

/-- `Int A x = ⋀_{x ≼ y} A y`. -/
def Int (A : Fin k → Fm PTm n) (x : Fin k) : Fm PTm n := conjFin fun y => if rel x y then A y else truth

/-- `Cl A x = ⋁_{x ≼ y} A y`. -/
def Cl (A : Fin k → Fm PTm n) (x : Fin k) : Fm PTm n := disjFin fun y => if rel x y then A y else Fm.bot

/-- `U` is open (upward closed). -/
def IsOpen (G : List (Fm PTm n)) (U : Fin k → Fm PTm n) : Prop := ∀ x y, rel x y → Prf PRAAx G (U x ⟶ U y)

/-- `D` is closed (downward closed). -/
def IsClosed (G : List (Fm PTm n)) (D : Fin k → Fm PTm n) : Prop := ∀ x y, rel x y → Prf PRAAx G (D y ⟶ D x)

variable {rel}

theorem int_at {A : Fin k → Fm PTm n} {x y : Fin k} (h : Γ ⊢[PRAAx] Int rel A x) (hxy : rel x y) :
    Γ ⊢[PRAAx] A y := by
  have := conjFin_elim h y
  simpa [hxy] using this

theorem int_intro {A : Fin k → Fm PTm n} {x : Fin k} (h : ∀ y, rel x y → (Γ ⊢[PRAAx] A y)) :
    Γ ⊢[PRAAx] Int rel A x :=
  conjFin_intro fun y => by
    by_cases hxy : rel x y
    · simpa [hxy] using h y hxy
    · simpa [hxy] using (Prf.eqRefl (Γ := Γ) (ConciseIPRA.PTm.zero : PTm n))

theorem cl_intro {A : Fin k → Fm PTm n} {x y : Fin k} (hxy : rel x y) (h : Γ ⊢[PRAAx] A y) :
    Γ ⊢[PRAAx] Cl rel A x :=
  disjFin_intro y (by simpa [hxy] using h)

theorem cl_imp {A : Fin k → Fm PTm n} {x : Fin k} {χ : Fm PTm n}
    (h : ∀ y, rel x y → (Γ ⊢[PRAAx] A y ⟶ χ)) : Γ ⊢[PRAAx] Cl rel A x ⟶ χ :=
  disjFin_imp fun y => by
    by_cases hxy : rel x y
    · simpa [hxy] using h y hxy
    · simpa [hxy] using (Prf.impI (Prf.botE χ Prf.hyp0) : Γ ⊢[PRAAx] Fm.bot ⟶ χ)

variable (hrefl : ∀ x, rel x x) (htrans : ∀ x y z, rel x y → rel y z → rel x z)
include hrefl htrans

/-- `Int A ⊆ A`. -/
theorem int_sub (A : Fin k → Fm PTm n) (x : Fin k) : Γ ⊢[PRAAx] Int rel A x ⟶ A x :=
  .impI (int_at Prf.hyp0 (hrefl x))

/-- `Int A` is open. -/
theorem int_open (A : Fin k → Fm PTm n) : IsOpen rel Γ (Int rel A) := fun x z hxz =>
  .impI (int_intro fun y hzy => int_at Prf.hyp0 (htrans x z y hxz hzy))

/-- Every open `U ⊆ A` lies in `Int A`. -/
theorem int_greatest {U A : Fin k → Fm PTm n} (hU : IsOpen rel Γ U) (hUA : ∀ x, Γ ⊢[PRAAx] U x ⟶ A x)
    (x : Fin k) : Γ ⊢[PRAAx] U x ⟶ Int rel A x :=
  .impI (int_intro fun y hxy => .impE (hUA y).wk (.impE (hU x y hxy).wk Prf.hyp0))

/-- `A ⊆ Cl A`. -/
theorem sub_cl (A : Fin k → Fm PTm n) (x : Fin k) : Γ ⊢[PRAAx] A x ⟶ Cl rel A x :=
  .impI (cl_intro (hrefl x) Prf.hyp0)

/-- `Cl A` is closed. -/
theorem cl_closed (A : Fin k → Fm PTm n) : IsClosed rel Γ (Cl rel A) := fun z x hzx =>
  cl_imp fun y hxy => .impI (cl_intro (htrans z x y hzx hxy) Prf.hyp0)

/-- Every closed `D ⊇ A` contains `Cl A`. -/
theorem cl_least {A D : Fin k → Fm PTm n} (hD : IsClosed rel Γ D) (hAD : ∀ x, Γ ⊢[PRAAx] A x ⟶ D x)
    (x : Fin k) : Γ ⊢[PRAAx] Cl rel A x ⟶ D x :=
  cl_imp fun y hxy => Prf.impTrans (hAD y) (hD x y hxy)

omit hrefl htrans in
/-- Monotonicity of `Int`. -/
theorem int_mono {A B : Fin k → Fm PTm n} (h : ∀ x, Γ ⊢[PRAAx] A x ⟶ B x) (x : Fin k) :
    Γ ⊢[PRAAx] Int rel A x ⟶ Int rel B x :=
  .impI (int_intro fun y hxy => .impE (h y).wk (int_at Prf.hyp0 hxy))

omit hrefl htrans in
/-- Monotonicity of `Cl`. -/
theorem cl_mono {A B : Fin k → Fm PTm n} (h : ∀ x, Γ ⊢[PRAAx] A x ⟶ B x) (x : Fin k) :
    Γ ⊢[PRAAx] Cl rel A x ⟶ Cl rel B x :=
  cl_imp fun y hxy => .impI (cl_intro hxy (.impE (h y).wk Prf.hyp0))

omit hrefl htrans in
/-- `Int(A ∧ B) ↔ Int A ∧ Int B`. -/
theorem int_inter (A B : Fin k → Fm PTm n) (x : Fin k) :
    (Γ ⊢[PRAAx] Int rel (fun y => A y ⋏ B y) x ⟶ (Int rel A x ⋏ Int rel B x)) ∧
    (Γ ⊢[PRAAx] (Int rel A x ⋏ Int rel B x) ⟶ Int rel (fun y => A y ⋏ B y) x) :=
  ⟨.impI (.andI (int_intro fun y hxy => (int_at Prf.hyp0 hxy).andE₁)
      (int_intro fun y hxy => (int_at Prf.hyp0 hxy).andE₂)),
   .impI (int_intro fun y hxy => .andI (int_at Prf.hyp0.andE₁ hxy) (int_at Prf.hyp0.andE₂ hxy))⟩

omit hrefl htrans in
/-- `Cl(A ∨ B) ↔ Cl A ∨ Cl B`. -/
theorem cl_union (A B : Fin k → Fm PTm n) (x : Fin k) :
    (Γ ⊢[PRAAx] Cl rel (fun y => A y ⋎ B y) x ⟶ (Cl rel A x ⋎ Cl rel B x)) ∧
    (Γ ⊢[PRAAx] (Cl rel A x ⋎ Cl rel B x) ⟶ Cl rel (fun y => A y ⋎ B y) x) :=
  ⟨cl_imp fun y hxy => .impI (.orE Prf.hyp0 (.orI₁ (cl_intro hxy Prf.hyp0)) (.orI₂ (cl_intro hxy Prf.hyp0))),
   .impI (.orE Prf.hyp0 (.impE (cl_imp fun y hxy => .impI (cl_intro hxy (.orI₁ Prf.hyp0))) Prf.hyp0)
      (.impE (cl_imp fun y hxy => .impI (cl_intro hxy (.orI₂ Prf.hyp0))) Prf.hyp0))⟩

omit hrefl htrans in
/-- `Int(¬A) ↔ ¬Cl A`. -/
theorem int_neg (A : Fin k → Fm PTm n) (x : Fin k) :
    (Γ ⊢[PRAAx] Int rel (fun y => neg (A y)) x ⟶ neg (Cl rel A x)) ∧
    (Γ ⊢[PRAAx] neg (Cl rel A x) ⟶ Int rel (fun y => neg (A y)) x) :=
  ⟨.impI (.impI (by
      have hI : (Cl rel A x :: Int rel (fun y => neg (A y)) x :: Γ) ⊢[PRAAx] Int rel (fun y => neg (A y)) x :=
        Prf.hyp1
      exact .impE (cl_imp fun y hxy => .impI (.impE (int_at hI hxy).wk Prf.hyp0)) Prf.hyp0)),
   .impI (int_intro fun y hxy => .impI (.impE Prf.hyp1 (cl_intro hxy Prf.hyp0)))⟩

end LeanProofs.IPRA.Topology.FiniteInteriorClosure
