import ConciseIPRA.UrPred

/-!
# Truncated subtraction, diagonal descent and three Boolean identities

`kern:sec:urmonus` in `T_UR`: `d(a, b) = I(b, a; u. P(u))` (`kern:lem:monus`),
diagonal descent for two and three arguments (`kern:lem:dd`) and the Boolean
identities of `kern:lem:bool`.  The hypotheses of diagonal descent are stated
over every context, since its proof splits each argument by coverage.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- Truncated subtraction `d(a, b) = I(b, a; u. P(u))`. -/
def Tm.ud (a b : Tm n) : Tm n := Tm.iter b a (Tm.upred (Syn.var 0))

/-- The sign `sg(a) = sel(a, 0, 1)`. -/
def Tm.usg (a : Tm n) : Tm n := Tm.sel a Tm.zero Tm.one

/-- `or(p, q) = sel(p, q, 1)`. -/
def Tm.uor (p q : Tm n) : Tm n := Tm.sel p q Tm.one

/-- `xor(p, q) = sel(p, q, Z(q))`. -/
def Tm.uxor (p q : Tm n) : Tm n := Tm.sel p q (Tm.zf q)

lift_op₁ usg
lift_op₂ ud uor uxor

ulift_op₁ usg
ulift_op₂ ud uor uxor

namespace U

variable {Γ : List (Fm Tm n)}

theorem mk_op₂ (Q : ∀ k, Tm k → Tm k → Tm k) (hQ : Sub₂ Q) (a b : Tm n) :
    mk Γ (Q n a b) = op₂ Q hQ (mk Γ a) (mk Γ b) := rfl

theorem mk_op₃ (Q : ∀ k, Tm k → Tm k → Tm k → Tm k) (hQ : Sub₃ Q) (a b c : Tm n) :
    mk Γ (Q n a b c) = op₃ Q hQ (mk Γ a) (mk Γ b) (mk Γ c) := rfl

/-! ### Truncated subtraction -/

@[simp] theorem ud_zero (x : U Γ) : ud x 0 = x := by
  induction x using U.ind with | _ a => exact sound (Tur.iterZero a _)

@[simp] theorem ud_succ (x y : U Γ) : ud x (succ y) = upred (ud x y) := by
  induction x, y using U.ind₂ with | _ a b
  have h := Tur.iterSucc (Γ := Γ) b a (Tm.upred (var 0))
  simp only [Tm.subst_upred, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

@[simp] theorem ud_one (x : U Γ) : ud x 1 = upred x := by rw [one_eq, ud_succ, ud_zero]

@[simp high] theorem ud_succ_succ (x y : U Γ) : ud (succ x) (succ y) = ud x y := by
  induction x, y using U.ind₂ with | _ a b
  simpa using cu (Γ := Γ) (Tm.ud (Tm.succ (shift a)) (Tm.succ (var 0))) (Tm.ud (shift a) (var 0))
    (Tm.upred (var 0)) b

@[simp high] theorem ud_one_succ (y : U Γ) : ud 1 (succ y) = ud 0 y := ud_succ_succ 0 y

@[simp] theorem ud_self (x : U Γ) : ud x x = 0 := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.ud (var 0) (var 0)) Tm.zero (var 0) a

@[simp] theorem ud_zero_left (x : U Γ) : ud 0 x = 0 := by
  induction x using U.ind with | _ a
  simpa using cu (Γ := Γ) (Tm.ud Tm.zero (var 0)) Tm.zero (Tm.upred (var 0)) a

theorem upred_ud_succ (x y : U Γ) : upred (ud (succ x) y) = ud x y := by
  refine U.cases y (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

@[simp] theorem ud_add_cancel (x y : U Γ) : ud (x + y) y = x := by
  induction x, y using U.ind₂ with | _ a b
  simpa using cu (Γ := Γ) (Tm.ud (Tm.add (shift a) (var 0)) (var 0)) (shift a) (var 0) b

theorem add_right_cancel {x y z : U Γ} (h : x + z = y + z) : x = y := by
  have k := congrArg (fun w => ud w z) h
  simpa using k

/-! ### Diagonal descent -/

theorem upred_cases (Q : ∀ k, Tm k → Tm k → Tm k) (hQ : Sub₂ Q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y : U Γ'), op₂ Q hQ (succ x) (succ y) = op₂ Q hQ x y)
    (hx : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (y : U Γ'), op₂ Q hQ 0 y = 0)
    (hy : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x : U Γ'), op₂ Q hQ x 0 = 0) (x y : U Γ) :
    op₂ Q hQ (upred x) (upred y) = op₂ Q hQ x y := by
  refine U.cases x (fun e h => ?_) (fun e z h => ?_)
  · simp only [UExt.map_op₂, UExt.map_upred, h, upred_zero, hx]
  · refine U.cases (e.map y) (fun e' h' => ?_) (fun e' w h' => ?_)
    · simp only [UExt.map_op₂, UExt.map_upred, h', upred_zero, hy]
    · simp only [UExt.map_op₂, UExt.map_upred, h', h, UExt.map_succ, upred_succ, hS]

/-- **Diagonal descent** (`kern:lem:dd`), two arguments. -/
theorem dd₂ (Q : ∀ k, Tm k → Tm k → Tm k) (hQ : Sub₂ Q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y : U Γ'), op₂ Q hQ (succ x) (succ y) = op₂ Q hQ x y)
    (hx : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (y : U Γ'), op₂ Q hQ 0 y = 0)
    (hy : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x : U Γ'), op₂ Q hQ x 0 = 0) (x y : U Γ) :
    op₂ Q hQ x y = 0 := by
  induction x, y using U.ind₂ with | _ a b
  have k := cu (Γ := Γ) (Q (n + 1) (Tm.ud (shift a) (var 0)) (Tm.ud (shift b) (var 0)))
    (Q (n + 1) (shift a) (shift b)) (var 0) a
    (by simp [hQ, mk_op₂ Q hQ])
    (by
      simp only [hQ, Tm.subst_ud, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
        mk_op₂ Q hQ, mk_ud, mk_succ, ud_succ]
      rw [upred_cases Q hQ hS hx hy]
      simp [mk_op₂ Q hQ])
    (by simp [hQ, mk_op₂ Q hQ])
  simp only [hQ, Tm.subst_ud, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    mk_op₂ Q hQ, mk_ud, ud_self, hx] at k
  exact k.symm

theorem upred_cases₃ (Q : ∀ k, Tm k → Tm k → Tm k → Tm k) (hQ : Sub₃ Q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y z : U Γ'),
      op₃ Q hQ (succ x) (succ y) (succ z) = op₃ Q hQ x y z)
    (hx : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (y z : U Γ'), op₃ Q hQ 0 y z = 0)
    (hy : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x z : U Γ'), op₃ Q hQ x 0 z = 0)
    (hz : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y : U Γ'), op₃ Q hQ x y 0 = 0) (x y z : U Γ) :
    op₃ Q hQ (upred x) (upred y) (upred z) = op₃ Q hQ x y z := by
  refine U.cases x (fun e h => ?_) (fun e x' h => ?_)
  · simp only [UExt.map_op₃, UExt.map_upred, h, upred_zero, hx]
  refine U.cases (e.map y) (fun e' h' => ?_) (fun e' y' h' => ?_)
  · simp only [UExt.map_op₃, UExt.map_upred, h', upred_zero, hy]
  refine U.cases (e'.map (e.map z)) (fun e'' h'' => ?_) (fun e'' z' h'' => ?_)
  · simp only [UExt.map_op₃, UExt.map_upred, h'', upred_zero, hz]
  · simp only [UExt.map_op₃, UExt.map_upred, h'', h', h, UExt.map_succ, upred_succ, hS]

/-- **Diagonal descent** (`kern:lem:dd`), three arguments. -/
theorem dd₃ (Q : ∀ k, Tm k → Tm k → Tm k → Tm k) (hQ : Sub₃ Q)
    (hS : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y z : U Γ'),
      op₃ Q hQ (succ x) (succ y) (succ z) = op₃ Q hQ x y z)
    (hx : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (y z : U Γ'), op₃ Q hQ 0 y z = 0)
    (hy : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x z : U Γ'), op₃ Q hQ x 0 z = 0)
    (hz : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (x y : U Γ'), op₃ Q hQ x y 0 = 0) (x y z : U Γ) :
    op₃ Q hQ x y z = 0 := by
  induction x, y, z using U.ind₃ with | _ a b c
  have k := cu (Γ := Γ)
    (Q (n + 1) (Tm.ud (shift a) (var 0)) (Tm.ud (shift b) (var 0)) (Tm.ud (shift c) (var 0)))
    (Q (n + 1) (shift a) (shift b) (shift c)) (var 0) a
    (by simp [hQ, mk_op₃ Q hQ])
    (by
      simp only [hQ, Tm.subst_ud, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
        mk_op₃ Q hQ, mk_ud, mk_succ, ud_succ]
      rw [upred_cases₃ Q hQ hS hx hy hz]
      simp [mk_op₃ Q hQ])
    (by simp [hQ, mk_op₃ Q hQ])
  simp only [hQ, Tm.subst_ud, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    mk_op₃ Q hQ, mk_ud, ud_self, hx] at k
  exact k.symm

/-! ### Booleans -/

/-- A successor equal to zero identifies all classes. -/
theorem absurd_succ {x : U Γ} (h : succ x = 0) (y z : U Γ) : y = z := by
  have h' := congrArg zf h
  rw [zf_succ, zf_zero] at h'
  exact U.absurd h' y z

theorem usg_eq (x : U Γ) : usg x = sel x 0 1 := by induction x using U.ind with | _ a => rfl

theorem uor_eq (p q : U Γ) : uor p q = sel p q 1 := by
  induction p, q using U.ind₂ with | _ a b => rfl

theorem uxor_eq (p q : U Γ) : uxor p q = sel p q (zf q) := by
  induction p, q using U.ind₂ with | _ a b => rfl

@[simp] theorem usg_zero : usg (0 : U Γ) = 0 := by rw [usg_eq, sel_zero]

@[simp] theorem usg_succ (x : U Γ) : usg (succ x) = 1 := by rw [usg_eq, sel_succ]

@[simp] theorem usg_one : usg (1 : U Γ) = 1 := usg_succ 0

@[simp] theorem uor_zero (q : U Γ) : uor 0 q = q := by rw [uor_eq, sel_zero]

@[simp] theorem uor_succ (p q : U Γ) : uor (succ p) q = 1 := by rw [uor_eq, sel_succ]

@[simp] theorem uor_one (q : U Γ) : uor 1 q = 1 := uor_succ 0 q

@[simp] theorem uxor_zero (q : U Γ) : uxor 0 q = q := by rw [uxor_eq, sel_zero]

@[simp] theorem uxor_succ (p q : U Γ) : uxor (succ p) q = zf q := by rw [uxor_eq, sel_succ]

@[simp] theorem uxor_one (q : U Γ) : uxor 1 q = zf q := uxor_succ 0 q

@[simp] theorem uxor_self (q : U Γ) : uxor q q = 0 := by
  refine U.cases q (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

/-- Two values fixed by the double zero test whose `xor` is `0` are equal. -/
theorem eq_of_uxor {p q : U Γ} (hp : zf (zf p) = p) (hq : zf (zf q) = q) (h : uxor p q = 0) :
    p = q := by
  refine U.cases p (fun e he => ?_) (fun e z he => ?_)
  · have k := congrArg e.map h
    simp only [UExt.map_uxor, he, uxor_zero, UExt.map_zero] at k
    rw [he, k]
  · have k := congrArg e.map h
    have kp := congrArg e.map hp
    have kq := congrArg e.map hq
    simp only [UExt.map_uxor, he, uxor_succ, UExt.map_zero, UExt.map_zf, zf_succ, zf_zero] at k kp kq
    rw [k, zf_zero] at kq
    rw [he, ← kp, kq]

@[simp] theorem zf_zf_zf (x : U Γ) : zf (zf (zf x)) = zf x := by
  refine U.cases x (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

@[simp] theorem zf_zf_usg (x : U Γ) : zf (zf (usg x)) = usg x := by
  refine U.cases x (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

@[simp] theorem zf_zf_uor (p q : U Γ) (hq : zf (zf q) = q) : zf (zf (uor p q)) = uor p q := by
  refine U.cases p (fun e h => ?_) (fun e z h => ?_)
  · have k := congrArg e.map hq
    simp only [UExt.map_zf] at k
    simp [h, k]
  · simp [h]

/-! ### Three Boolean identities -/

/-- `kern:lem:bool` (iii). -/
theorem uor_usg (x y : U Γ) : uor (usg x) (usg y) = usg (x + y) := by
  refine U.cases x (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

end U

/-- The `xor` of the two sides of `kern:lem:bool` (i). -/
def Tm.bq₁ (x y : Tm n) : Tm n := Tm.uxor (Tm.zf (Tm.ud (Tm.succ x) y)) (Tm.usg (Tm.ud y x))

/-- The `xor` of the two sides of `kern:lem:bool` (ii). -/
def Tm.bq₂ (x a b : Tm n) : Tm n :=
  Tm.uxor (Tm.zf (Tm.ud (Tm.ud x a) (Tm.ud b a))) (Tm.uor (Tm.zf (Tm.ud x a)) (Tm.zf (Tm.ud x b)))

@[simp] theorem Tm.subst_bq₁ (σ : Fin n → Tm m) (x y : Tm n) :
    Syn.subst σ (Tm.bq₁ x y) = Tm.bq₁ (Syn.subst σ x) (Syn.subst σ y) := by simp [Tm.bq₁]

@[simp] theorem Tm.subst_bq₂ (σ : Fin n → Tm m) (x a b : Tm n) :
    Syn.subst σ (Tm.bq₂ x a b) = Tm.bq₂ (Syn.subst σ x) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.bq₂]

namespace U

variable {Γ : List (Fm Tm n)}

theorem bq₁_eq (x y : U Γ) :
    op₂ (fun _ => Tm.bq₁) Tm.subst_bq₁ x y = uxor (zf (ud (succ x) y)) (usg (ud y x)) := by
  induction x, y using U.ind₂ with | _ a b => rfl

theorem bq₂_eq (x a b : U Γ) :
    op₃ (fun _ => Tm.bq₂) Tm.subst_bq₂ x a b
      = uxor (zf (ud (ud x a) (ud b a))) (uor (zf (ud x a)) (zf (ud x b))) := by
  induction x, a, b using U.ind₃ with | _ x a b => rfl

/-- `kern:lem:bool` (i). -/
theorem zf_ud_succ (x y : U Γ) : zf (ud (succ x) y) = usg (ud y x) := by
  refine eq_of_uxor (zf_zf_zf _) (zf_zf_usg _) ?_
  rw [← bq₁_eq]
  refine dd₂ _ _ (fun x y => by rw [bq₁_eq, bq₁_eq]; simp) (fun y => ?_)
    (fun x => by rw [bq₁_eq]; simp) x y
  rw [bq₁_eq]
  refine U.cases y (fun e h => ?_) (fun e z h => ?_) <;> simp [h]

/-- `kern:lem:bool` (ii). -/
theorem zf_ud_ud (x a b : U Γ) :
    zf (ud (ud x a) (ud b a)) = uor (zf (ud x a)) (zf (ud x b)) := by
  refine eq_of_uxor (zf_zf_zf _) (zf_zf_uor _ _ (zf_zf_zf _)) ?_
  rw [← bq₂_eq]
  refine dd₃ _ _ (fun x a b => by rw [bq₂_eq, bq₂_eq]; simp) (fun a b => by rw [bq₂_eq]; simp)
    (fun x b => ?_) (fun x a => ?_) x a b
  · rw [bq₂_eq]
    refine U.cases x (fun e h => ?_) (fun e z h => ?_) <;> simp [h]
  · rw [bq₂_eq]
    refine U.cases (ud x a) (fun e h => ?_) (fun e z h => ?_)
    · refine U.cases (e.map x) (fun e' h' => ?_) (fun e' w h' => ?_) <;>
        simp [h]
    · refine U.cases (e.map x) (fun e' h' => ?_) (fun e' w h' => ?_)
      · refine absurd_succ (x := e'.map z) ?_ _ _
        have k := congrArg e'.map h
        simp only [UExt.map_ud, h', ud_zero_left, UExt.map_succ] at k
        exact k.symm
      · simp [h, h']

end U

end LeanProofs.ConciseIPRA
