import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.SumPalindrome

/-!
# One finite cube for all parameters (`riemann_ipra_prime_criteria_2026-11-20`, Theorem `thm:cubef`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-object.tex`, Theorem `thm:cubef`:
"Let `A = ∀x [e(x) = 0]`, allowing an arbitrary iPRA term and additional free parameters in `e`. The following
are equivalent by derivations of object iPRA: `A`, `∀N B_e(N) = 0`, `∀N B_e(N + g(N)) = 0` … In addition,
object iPRA proves the witness-preserving equivalence `(∃x e(x) ≠ 0) ↔ (∃N B_e(N) ≠ 0)`."

Here the excess is a body `e(x, y)` with its parameters packed into `y` (any number of parameters by pairing,
and any number of coordinates by pairing the `x`), and the scan `B_e(N)` is the bounded existential bit
`BoundedReflection.exB e N y` — `1` exactly when some sample `x < N` is nonzero, its least failure being the
primitive-recursive witness `wit e N y`.

* `cube_clean`: `∀x e(x) = 0 ↔ ∀N B_e(N) = 0`;
* `cube_shift`: `∀x e(x) = 0 ↔ ∀N B_e(N + g(N)) = 0` for every term `g` (in `N` and the parameters);
* `cube_witness`: `(∃x e(x) ≠ 0) ↔ (∃N B_e(N) ≠ 0)`, the reverse direction producing the witness `wit`.

All arithmetic inductions are the quantifier-free ones inside `BoundedReflection`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.CubeScan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_none ex_intro one_ne_zero)
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (e : PTm 2)

/-- `A = ∀x e(x, y) = 0`. -/
abbrev Clean (y : PTm n) : Fm PTm n := Fm.all (inst2 e (var 0) (Syn.shift y) ≐ zero)

/-- `B_e(N) = 0` for every horizon `N`. -/
abbrev ScanClean (y : PTm n) : Fm PTm n := Fm.all (exB e (var 0) (Syn.shift y) ≐ zero)

/-- `B_e(N + g(N)) = 0` for every `N`. -/
abbrev ScanCleanG (g : PTm (n + 1)) (y : PTm n) : Fm PTm n := Fm.all (exB e (var 0 + g) (Syn.shift y) ≐ zero)

theorem inst2_subst {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (inst2 e a b) = inst2 e (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem clean_shift (y : PTm n) : Fm.shift (Clean e y) = Clean e (Syn.shift y) := by
  simp only [Clean, Fm.shift, Fm.subst_all, Fm.subst_eq, inst2_subst, Syn.subst_var, Syn.up_zero,
    subst_up_shift_pal, ConciseIPRA.PTm.subst_zero] <;> rfl

theorem exneg_shift (y : PTm n) : Fm.shift (Fm.ex (neg (inst2 e (var 0) (Syn.shift y) ≐ zero))) =
    Fm.ex (neg (inst2 e (var 0) (Syn.shift (Syn.shift y)) ≐ zero)) := by
  simp only [Fm.shift, Fm.subst_ex, subst_neg, Fm.subst_eq, inst2_subst, Syn.subst_var, Syn.up_zero,
    subst_up_shift_pal, ConciseIPRA.PTm.subst_zero] <;> rfl

theorem exscan_shift (y : PTm n) : Fm.shift (Fm.ex (neg (exB e (var 0) (Syn.shift y) ≐ zero))) =
    Fm.ex (neg (exB e (var 0) (Syn.shift (Syn.shift y)) ≐ zero)) := by
  simp only [Fm.shift, Fm.subst_ex, subst_neg, Fm.subst_eq, subst_ap2, PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, subst_up_shift_pal] <;> rfl

/-- A clean excess gives a clean scan at every horizon. -/
theorem scan_of_clean {y N : PTm n} (h : Γ ⊢[PRAAx] Clean e y) : Γ ⊢[PRAAx] exB e N y ≐ zero := by
  refine .orE (ex_cases e N y) Prf.hyp0 ?_
  have w := ex_elim e (Prf.hyp0 : ((exB e N y ≐ one) :: Γ) ⊢[PRAAx] exB e N y ≐ one)
  have a : ((exB e N y ≐ one) :: Γ) ⊢[PRAAx] inst2 e (wit e N y) y ≐ zero := by
    simpa using Prf.allE (wit e N y) h.wk
  exact .botE _ (.impE (Prf.andE₂ w) a)

/-- A clean scan at a horizon above `x` gives `e(x) = 0`. -/
theorem clean_of_scan {y x M : PTm n} (h : Γ ⊢[PRAAx] exB e M y ≐ zero) (hx : Γ ⊢[PRAAx] lt x M) :
    Γ ⊢[PRAAx] inst2 e x y ≐ zero :=
  ex_none e h hx

theorem cube_clean (y : PTm n) : Γ ⊢[PRAAx] Fm.iff (Clean e y) (ScanClean e y) := by
  refine .andI (.impI (.allI ?_)) (.impI (.allI ?_))
  · have h := (Prf.hyp0 : (Clean e y :: Γ) ⊢[PRAAx] Clean e y).shift
    rw [clean_shift] at h
    exact scan_of_clean e h
  · have h0 := Prf.allE (succ (var 0)) (Prf.hyp0 : (ScanClean e y :: Γ) ⊢[PRAAx] ScanClean e y).shift
    simp only [Fm.subst_eq, subst_ap2, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
      Syn.subst_var, Syn.up_zero, Syn.inst_zero, subst_up_shift_pal, Syn.subst_inst_shift] at h0
    exact clean_of_scan e h0 (le_refl _)

theorem cube_shift (g : PTm (n + 1)) (y : PTm n) : Γ ⊢[PRAAx] Fm.iff (Clean e y) (ScanCleanG e g y) := by
  refine .andI (.impI (.allI ?_)) (.impI (.allI ?_))
  · have h := (Prf.hyp0 : (Clean e y :: Γ) ⊢[PRAAx] Clean e y).shift
    rw [clean_shift] at h
    exact scan_of_clean e h
  · have h0 := Prf.allE (succ (var 0)) (Prf.hyp0 : (ScanCleanG e g y :: Γ) ⊢[PRAAx] ScanCleanG e g y).shift
    simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, Syn.inst_zero, subst_up_shift_pal,
      Syn.subst_inst_shift] at h0
    exact clean_of_scan e h0 (le_add_right _ _)

/-- The witness-preserving equivalence; the reverse direction exhibits `wit e N y`. -/
theorem cube_witness (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (Fm.ex (neg (inst2 e (var 0) (Syn.shift y) ≐ zero)))
      (Fm.ex (neg (exB e (var 0) (Syn.shift y) ≐ zero))) := by
  refine .andI (.impI ?_) (.impI ?_)
  · refine .exE Prf.hyp0 ?_
    rw [exscan_shift]
    refine .exI (succ (var 0)) ?_
    simp only [subst_neg, Fm.subst_eq, subst_ap2, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    refine .impI ?_
    have h1 : ((exB e (succ (var 0)) (Syn.shift y) ≐ zero) :: neg (inst2 e (var 0) (Syn.shift y) ≐ zero) ::
        (Fm.ex (neg (inst2 e (var 0) (Syn.shift y) ≐ zero)) :: Γ).map Fm.shift) ⊢[PRAAx]
        neg (inst2 e (var 0) (Syn.shift y) ≐ zero) := Prf.hyp1
    exact .impE h1 (clean_of_scan e Prf.hyp0 (le_refl _))
  · refine .exE Prf.hyp0 ?_
    rw [exneg_shift]
    refine .exI (wit e (var 0) (Syn.shift y)) ?_
    simp only [subst_neg, Fm.subst_eq, inst2_subst, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero]
    have h1 : (neg (exB e (var 0) (Syn.shift y) ≐ zero) ::
        (Fm.ex (neg (exB e (var 0) (Syn.shift y) ≐ zero)) :: Γ).map Fm.shift) ⊢[PRAAx]
        neg (exB e (var 0) (Syn.shift y) ≐ zero) := Prf.hyp0
    exact .orE (ex_cases e (var 0) (Syn.shift y)) (.botE _ (.impE h1.wk Prf.hyp0)) (Prf.andE₂ (ex_elim e Prf.hyp0))

/-! ## The multiplicative certificate (`new-uniform.tex`, "A multiplicative certificate with an object derivation")

"Use the actual nonnegative excess `e_i` to form `V(0) = 1` and `V(m+1) = V(m)(1 + e_m)`. Then the hypothesis has
the equivalent form `∀m V(m) = 1`." -/

/-- `V(m) = Π_{i<m} (1 + e_i)`. -/
abbrev Vc (m y : PTm n) : PTm n := ap2 (prodF (succ e)) m y

theorem v_succ (m y : PTm n) : Γ ⊢[PRAAx] Vc e (succ m) y ≐ Vc e m y * succ (inst2 e m y) := by
  have h := prod_succ (Γ := Γ) (succ e) m y
  simpa [inst2] using h

theorem v_clean {y : PTm n} (h : Γ ⊢[PRAAx] Clean e y) : Γ ⊢[PRAAx] Fm.all (Vc e (var 0) (Syn.shift y) ≐ one) := by
  ipra_qfind (trivial) [subst_ap2]
  · exact prod_zero _ _
  · have ih : ((Vc e (var 0) (Syn.shift y) ≐ one) :: Γ.map Fm.shift) ⊢[PRAAx] Vc e (var 0) (Syn.shift y) ≐ one :=
      Prf.hyp0
    have hz : ((Vc e (var 0) (Syn.shift y) ≐ one) :: Γ.map Fm.shift) ⊢[PRAAx] inst2 e (var 0) (Syn.shift y) ≐ zero :=
      h.allOpen.wk
    exact (v_succ e (var 0) (Syn.shift y)).eqTrans ((congrMul ih (congrSucc hz)).eqTrans (one_mul _))

/-- `∀x e(x) = 0 ↔ ∀m V(m) = 1`. -/
theorem product_certificate (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (Clean e y) (Fm.all (Vc e (var 0) (Syn.shift y) ≐ one)) := by
  refine .andI (.impI (v_clean e Prf.hyp0)) (.impI (.allI ?_))
  have hall : (Fm.all (Vc e (var 0) (Syn.shift y) ≐ one) :: Γ) ⊢[PRAAx] Fm.all (Vc e (var 0) (Syn.shift y) ≐ one) :=
    Prf.hyp0
  have h0 := natEq hall.allOpen
  have h1' := Prf.allE (succ (var 0)) hall.shift
  simp only [Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.up_zero, Syn.inst_zero, subst_up_shift_pal, Syn.subst_inst_shift] at h1'
  have h1'' : ((Fm.all (Vc e (var 0) (Syn.shift y) ≐ one) :: Γ).map Fm.shift) ⊢[PRAAx]
      Vc e (succ (var 0)) (Syn.shift y) ≐ one := h1'
  have h1 := natEq h1''
  have s := natEq (v_succ (Γ := (Fm.all (Vc e (var 0) (Syn.shift y) ≐ one) :: Γ).map Fm.shift) e (var 0) (Syn.shift y))
  ipra_lc h1 - s - (𝔞 (inst2 e (var 0) (Syn.shift y)) + 1) * h0

end LeanProofs.IPRA.AnalyticNumberTheory.CubeScan
