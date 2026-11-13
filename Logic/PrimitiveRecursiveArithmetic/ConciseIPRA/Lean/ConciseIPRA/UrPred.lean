import ConciseIPRA.UrRetract
import ConciseIPRA.TeqCompare

/-!
# The predecessor from uniqueness of iteration

`kern:sec:urpred`: the clocks `N` (parity) and `M` (residue mod 3), the ramp
`G(n) = I(n, 0; u. g(u))` with the update `g(u) = S(u + N(M(u)))`, the factor map
`χ(u) = sel(N(u), G(u), u)`, the comparator and the saturating predecessor, in
`T_UR`.  The update `g` differs from the ramp of `T_eq` away from the orbit of `0`, so
that `M(g(u)) = Z(M(u))` holds at every `u` and the ramp invariant `M(G(n)) = N(n)` is
one instance of uniqueness, with no induction hypothesis (`kern:lem:ramp`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- The update of the ramp, `S(u + N(M(u)))`. -/
def Tm.ug (a : Tm n) : Tm n := Tm.succ (Tm.add a (Tm.par (Tm.mod3 a)))

/-- The ramp `I(n, 0; u. g(u))`. -/
def Tm.uG (a : Tm n) : Tm n := Tm.iter a Tm.zero (Tm.ug (Syn.var 0))

/-- The factor map `χ(u) = sel(N(u), G(u), u)`. -/
def Tm.uhop (a : Tm n) : Tm n := Tm.sel (Tm.par a) (Tm.uG a) a

/-- The iterated factor map. -/
def Tm.uhops (y a : Tm n) : Tm n := Tm.iter y a (Tm.uhop (Syn.var 0))

/-- The comparator `λ(x, y) = N(I(y, 2^x; u. χ(u)))`, the indicator of `x ≤ y`. -/
def Tm.ucmp (x y : Tm n) : Tm n := Tm.par (Tm.uhops y (Tm.pow2 x))

/-- One saturating step. -/
def Tm.ubump (k u : Tm n) : Tm n := Tm.sel (Tm.ucmp (Tm.succ (Tm.succ u)) k) u (Tm.succ u)

/-- The saturating counter. -/
def Tm.usat (t k : Tm n) : Tm n := Tm.iter t Tm.zero (Tm.ubump (Syn.shift k) (Syn.var 0))

/-- The predecessor of `T_UR`. -/
def Tm.upred (a : Tm n) : Tm n := Tm.usat a a

lift_op₁ ug uG uhop
lift_op₂ uhops ucmp ubump usat
lift_op₁ upred

ulift_op₁ zf par cyc mod3 pow2 ug uG uhop upred
ulift_op₂ uhops ucmp ubump usat

@[simp] theorem UExt.map_add {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)} (e : UExt Γ Γ')
    (x y : U Γ) : e.map (x + y) = e.map x + e.map y :=
  UExt.map_op₂ e (fun _ => Tm.add) Tm.subst_add x y

namespace U

variable {Γ : List (Fm Tm n)}

/-! ### The two clocks -/

theorem zf_eq (x : U Γ) : zf x = sel x 1 0 := by
  induction x using U.ind with | _ a => rfl

@[simp] theorem zf_zero : zf (0 : U Γ) = 1 := by rw [zf_eq, sel_zero]

@[simp] theorem zf_succ (x : U Γ) : zf (succ x) = 0 := by rw [zf_eq, sel_succ]

@[simp] theorem zf_one : zf (1 : U Γ) = 0 := zf_succ 0

@[simp] theorem par_zero : par (0 : U Γ) = 0 := sound (Tur.iterZero _ _)

@[simp] theorem par_succ (x : U Γ) : par (succ x) = zf (par x) := by
  induction x using U.ind with | _ a => exact sound (Tur.iterSucc a Tm.zero (Tm.zf (var 0)))

@[simp] theorem par_one : par (1 : U Γ) = 1 := by
  show par (succ 0) = 1
  rw [par_succ, par_zero, zf_zero]

@[simp] theorem zf_zf_par (x : U Γ) : zf (zf (par x)) = par x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.zf (Tm.zf (Tm.par (var 0)))) (Tm.par (var 0)) (Tm.zf (var 0)) a

theorem par_cases (x : U Γ) {p q : U Γ}
    (h0 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : UExt Γ Γ'), par (e.map x) = 0 → e.map p = e.map q)
    (h1 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : UExt Γ Γ'), par (e.map x) = 1 → e.map p = e.map q) :
    p = q := by
  refine U.cases (par x) (fun e he => h0 e (by rwa [UExt.map_par] at he)) (fun e z he => h1 e ?_)
  rw [UExt.map_par] at he
  have h := zf_zf_par (e.map x)
  rw [he, zf_succ, zf_zero] at h
  rw [he, ← h]

theorem par_double (x : U Γ) : par (x + x) = 0 := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.par (Tm.add (var 0) (var 0))) Tm.zero (Tm.zf (Tm.zf (var 0))) a

theorem par_triple (x : U Γ) : par (x + x + x) = par x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.par (Tm.add (Tm.add (var 0) (var 0)) (var 0))) (Tm.par (var 0))
    (Tm.zf (var 0)) a

theorem cyc_eq (x : U Γ) : cyc x = zf x + (par x + par x) := by
  induction x using U.ind with | _ a => rfl

@[simp] theorem cyc_zero : cyc (0 : U Γ) = 1 := by simp [cyc_eq]

@[simp] theorem cyc_one : cyc (1 : U Γ) = succ 1 := by simp [cyc_eq]

@[simp] theorem cyc_succ_one : cyc (succ (1 : U Γ)) = 0 := by simp [cyc_eq]

@[simp] theorem mod3_zero : mod3 (0 : U Γ) = 0 := sound (Tur.iterZero _ _)

@[simp] theorem mod3_succ (x : U Γ) : mod3 (succ x) = cyc (mod3 x) := by
  induction x using U.ind with | _ a => exact sound (Tur.iterSucc a Tm.zero (Tm.cyc (var 0)))

/-- The residue takes the values `0`, `1` and `2`, split over all extensions. -/
theorem mod3_cases (x : U Γ) {p q : U Γ}
    (h0 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : UExt Γ Γ'), mod3 (e.map x) = 0 → e.map p = e.map q)
    (h1 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : UExt Γ Γ'), mod3 (e.map x) = 1 → e.map p = e.map q)
    (h2 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : UExt Γ Γ'),
      mod3 (e.map x) = succ 1 → e.map p = e.map q) : p = q := by
  refine U.cases x (fun e he => h0 e (by rw [he, mod3_zero])) (fun e z he => ?_)
  have key : ∀ {k : ℕ} {Γ'' : List (Fm Tm k)} (e' : UExt _ Γ''),
      mod3 ((e.comp e').map x) = cyc (e'.map (mod3 z)) := fun e' => by
    rw [UExt.map_comp, he, UExt.map_succ, mod3_succ, UExt.map_mod3]
  refine U.cases (mod3 z) (fun e' he' => ?_) (fun e' w he' => ?_)
  · rw [← UExt.map_comp, ← UExt.map_comp]
    exact h1 (e.comp e') (by rw [key, he', cyc_zero])
  · refine par_cases (succ w) (fun e'' h => ?_) (fun e'' h => ?_)
    · rw [← UExt.map_comp, ← UExt.map_comp, ← UExt.map_comp, ← UExt.map_comp]
      refine h0 (e.comp (e'.comp e'')) ?_
      rw [key, UExt.map_comp, he', cyc_eq, h, UExt.map_succ, zf_succ]
      simp
    · rw [← UExt.map_comp, ← UExt.map_comp, ← UExt.map_comp, ← UExt.map_comp]
      refine h2 (e.comp (e'.comp e'')) ?_
      rw [key, UExt.map_comp, he', cyc_eq, h, UExt.map_succ, zf_succ]
      rw [zero_add, add_one_eq]

@[simp] theorem par_par (x : U Γ) : par (par x) = par x := by
  refine par_cases x (fun e h => ?_) (fun e h => ?_) <;> simp [h]

@[simp] theorem par_add_zf (x : U Γ) : par x + zf (par x) = 1 := by
  refine par_cases x (fun e h => ?_) (fun e h => ?_) <;> simp [h]

@[simp] theorem cyc3_mod3 (x : U Γ) : cyc (cyc (cyc (mod3 x))) = mod3 x := by
  refine mod3_cases x (fun e h => ?_) (fun e h => ?_) (fun e h => ?_) <;> simp [h]

@[simp] theorem add_par_add_zf (y x : U Γ) : y + par x + zf (par x) = succ y := by
  rw [add_assoc, par_add_zf, add_one_eq]

theorem mod3_triple (x : U Γ) : mod3 (x + x + x) = 0 := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.mod3 (Tm.add (Tm.add (var 0) (var 0)) (var 0))) Tm.zero (var 0) a

/-! ### The ramp -/

theorem ug_eq (x : U Γ) : ug x = succ (x + par (mod3 x)) := by
  induction x using U.ind with | _ a => rfl

@[simp] theorem uG_zero : uG (0 : U Γ) = 0 := sound (Tur.iterZero _ _)

theorem uG_succ_ug (x : U Γ) : uG (succ x) = ug (uG x) := by
  induction x using U.ind with | _ a => exact sound (Tur.iterSucc a Tm.zero (Tm.ug (var 0)))

/-- `kern:lem:ramp` (i): the update advances the residue by the zero test, everywhere. -/
@[simp] theorem mod3_ug (x : U Γ) : mod3 (ug x) = zf (mod3 x) := by
  refine mod3_cases x (fun e h => ?_) (fun e h => ?_) (fun e h => ?_) <;> simp [ug_eq, h]

/-- `kern:lem:ramp` (ii): the ramp invariant, by one instance of uniqueness. -/
@[simp] theorem mod3_uG (x : U Γ) : mod3 (uG x) = par x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.mod3 (Tm.uG (var 0))) (Tm.par (var 0)) (Tm.zf (var 0)) a
    (by simp) (by simp [uG_succ_ug])

/-- `kern:lem:ramp` (iii). -/
@[simp] theorem uG_succ (x : U Γ) : uG (succ x) = succ (uG x + par x) := by
  rw [uG_succ_ug, ug_eq, mod3_uG, par_par]

theorem uG_succ_succ (x : U Γ) : uG (succ (succ x)) = succ (succ (succ (uG x))) := by
  simp

theorem uG_three (x : U Γ) :
    uG (succ (succ (succ x))) = succ (succ (succ (succ (uG x + par x)))) := by
  rw [uG_succ, uG_succ_succ, par_succ, par_succ, zf_zf_par]
  simp only [succ_add]

theorem uG_double (x : U Γ) : uG (x + x) = x + x + x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.uG (Tm.add (var 0) (var 0))) (Tm.add (Tm.add (var 0) (var 0)) (var 0))
    (Tm.succ (Tm.succ (Tm.succ (var 0)))) a

theorem mod3_triple_par (x y : U Γ) : mod3 (y + y + y + par x) = par x := by
  refine par_cases x (fun e h => ?_) (fun e h => ?_) <;>
    simp only [UExt.map_mod3, UExt.map_add, UExt.map_par, h, add_zero, mod3_triple, add_one_eq,
      mod3_succ, cyc_zero]

/-- `kern:lem:ramp` (iv). -/
theorem uG_triple (x : U Γ) : uG (x + x + x) = uG x + uG x + uG x + par x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.uG (Tm.add (Tm.add (var 0) (var 0)) (var 0)))
    (Tm.add (Tm.add (Tm.add (Tm.uG (var 0)) (Tm.uG (var 0))) (Tm.uG (var 0))) (Tm.par (var 0)))
    (Tm.succ (Tm.succ (Tm.succ (Tm.succ (Tm.add (var 0) (Tm.mod3 (var 0))))))) a
    (by simp) (by simp [-uG_succ, uG_three, par_triple])
    (by
      simp [mod3_triple_par]
      refine par_cases (mk _ (var 0)) (fun e h => ?_) (fun e h => ?_) <;>
        simp only [UExt.map_add, UExt.map_uG, UExt.map_par, UExt.map_zf, h, UExt.map_one,
          zf_zero, zf_one, ← add_one_eq] <;> abel)

/-! ### The factor map and the comparator -/

theorem uhop_eq (x : U Γ) : uhop x = sel (par x) (uG x) x := by
  induction x using U.ind with | _ a => rfl

theorem uhop_double (x : U Γ) : uhop (x + x) = x + x + x := by
  rw [uhop_eq, par_double, sel_zero, uG_double]

@[simp] theorem uhop_one : uhop (1 : U Γ) = 1 := by rw [uhop_eq, par_one, sel_one]

theorem uhop_triple (x : U Γ) : uhop (x + x + x) = uhop x + uhop x + uhop x := by
  simp only [uhop_eq, par_triple, uG_triple]
  refine par_cases x (fun e h => ?_) (fun e h => ?_) <;>
    simp only [UExt.map_sel, UExt.map_add, UExt.map_uG, UExt.map_par, h, sel_zero, sel_one,
      add_zero]

@[simp] theorem uhops_zero (x : U Γ) : uhops 0 x = x := by
  induction x using U.ind with | _ a => exact sound (Tur.iterZero a _)

@[simp] theorem uhops_succ (y x : U Γ) : uhops (succ y) x = uhop (uhops y x) := by
  induction y, x using U.ind₂ with | _ b a
  have h := Tur.iterSucc (Γ := Γ) b a (Tm.uhop (var 0))
  simp only [Tm.subst_uhop, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

@[simp] theorem uhops_one_left (x : U Γ) : uhops 1 x = uhop x := by
  rw [one_eq, uhops_succ, uhops_zero]

/-- Rotation, from `kern:lem:uradd`. -/
theorem uhops_succ' (y x : U Γ) : uhops (succ y) x = uhops y (uhop x) := by
  induction y, x using U.ind₂ with | _ b a
  simpa using cu (Γ := Γ) (Tm.uhops (Tm.succ (var 0)) (shift a)) (Tm.uhops (var 0) (Tm.uhop (shift a)))
    (Tm.uhop (var 0)) b

theorem uhops_triple (y x : U Γ) : uhops y (x + x + x) = uhops y x + uhops y x + uhops y x := by
  induction y, x using U.ind₂ with | _ b a
  simpa using cu (Γ := Γ) (Tm.uhops (var 0) (Tm.add (Tm.add (shift a) (shift a)) (shift a)))
    (Tm.add (Tm.add (Tm.uhops (var 0) (shift a)) (Tm.uhops (var 0) (shift a)))
      (Tm.uhops (var 0) (shift a))) (Tm.uhop (var 0)) b (by simp) (by simp)
    (by simp [uhop_triple])

@[simp] theorem uhops_one (y : U Γ) : uhops y 1 = 1 := by
  induction y using U.ind with | _ b
  simpa using cu (Γ := Γ) (Tm.uhops (var 0) Tm.one) Tm.one (Tm.uhop (var 0)) b

@[simp] theorem pow2_zero : pow2 (0 : U Γ) = 1 := sound (Tur.iterZero _ _)

@[simp] theorem pow2_succ (x : U Γ) : pow2 (succ x) = pow2 x + pow2 x := by
  induction x using U.ind with | _ a => exact sound (Tur.iterSucc a Tm.one (Tm.add (var 0) (var 0)))

theorem ucmp_eq (x y : U Γ) : ucmp x y = par (uhops y (pow2 x)) := by
  induction x, y using U.ind₂ with | _ a b => rfl

/-- `kern:lem:comparator` (iii). -/
@[simp] theorem ucmp_zero (y : U Γ) : ucmp 0 y = 1 := by
  rw [ucmp_eq, pow2_zero, uhops_one, par_one]

@[simp] theorem ucmp_succ_zero (x : U Γ) : ucmp (succ x) 0 = 0 := by
  rw [ucmp_eq, pow2_succ, uhops_zero, par_double]

@[simp] theorem ucmp_succ_succ (x y : U Γ) : ucmp (succ x) (succ y) = ucmp x y := by
  rw [ucmp_eq, ucmp_eq, pow2_succ, uhops_succ', uhop_double, uhops_triple, par_triple]

@[simp] theorem ucmp_one_succ (y : U Γ) : ucmp 1 (succ y) = 1 :=
  (ucmp_succ_succ 0 y).trans (ucmp_zero y)

@[simp] theorem ucmp_one_zero : ucmp (1 : U Γ) 0 = 0 := ucmp_succ_zero 0

@[simp] theorem ucmp_succ_one (x : U Γ) : ucmp (succ x) 1 = ucmp x 0 := ucmp_succ_succ x 0

/-! ### The predecessor -/

theorem sel_succ_succ (c x y : U Γ) : sel c (succ x) (succ y) = succ (sel c x y) := by
  refine U.cases c (fun e he => ?_) (fun e z he => ?_) <;> simp [he]

theorem ubump_eq (k u : U Γ) : ubump k u = sel (ucmp (succ (succ u)) k) u (succ u) := by
  induction k, u using U.ind₂ with | _ a b => rfl

@[simp] theorem ubump_succ_succ (k u : U Γ) : ubump (succ k) (succ u) = succ (ubump k u) := by
  rw [ubump_eq, ucmp_succ_succ, sel_succ_succ, ← ubump_eq]

@[simp] theorem usat_zero (k : U Γ) : usat 0 k = 0 := by
  induction k using U.ind with | _ a => exact sound (Tur.iterZero _ _)

@[simp] theorem usat_succ (t k : U Γ) : usat (succ t) k = ubump k (usat t k) := by
  induction t, k using U.ind₂ with | _ a b
  have h := Tur.iterSucc (Γ := Γ) a Tm.zero (Tm.ubump (shift b) (var 0))
  simp only [Tm.subst_ubump, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact sound h

/-- Conjugacy of the saturating counters at consecutive caps. -/
@[simp] theorem ubump_usat_succ (t k : U Γ) :
    ubump (succ (succ k)) (usat t (succ (succ k))) = succ (usat t (succ k)) := by
  induction t, k using U.ind₂ with | _ a b
  simpa using cu (Γ := Γ)
    (Tm.ubump (Tm.succ (Tm.succ (shift b))) (Tm.usat (var 0) (Tm.succ (Tm.succ (shift b)))))
    (Tm.succ (Tm.usat (var 0) (Tm.succ (shift b))))
    (Tm.ubump (Tm.succ (Tm.succ (shift b))) (var 0)) a
    (by simp [ubump_eq]) (by simp [Syn.subst_up_shift]; rfl) (by simp [Syn.subst_up_shift]; rfl)

theorem upred_eq (x : U Γ) : upred x = usat x x := by
  induction x using U.ind with | _ a => rfl

@[simp] theorem upred_zero : upred (0 : U Γ) = 0 := by rw [upred_eq, usat_zero]

/-- **The predecessor from uniqueness** (`kern:thm:urpred`). -/
@[simp] theorem upred_succ (x : U Γ) : upred (succ x) = x := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.upred (Tm.succ (var 0))) (var 0) (Tm.succ (var 0)) a
    (by simp [upred_eq]; rw [one_eq, usat_succ, usat_zero, ubump_eq, ucmp_succ_succ,
      ucmp_succ_zero, sel_zero]) (by simp [upred_eq])

theorem succ_inj {x y : U Γ} (h : succ x = succ y) : x = y := by
  have h' := congrArg upred h
  rwa [upred_succ, upred_succ] at h'

@[simp] theorem succ_inj_iff {x y : U Γ} : succ x = succ y ↔ x = y :=
  ⟨succ_inj, fun h => by rw [h]⟩

end U

end LeanProofs.ConciseIPRA
