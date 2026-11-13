import ConciseIPRA.UrMonus

/-!
# Reflection of equality and uniqueness of iteration in place of induction

`kern:sec:uracc`, `kern:sec:urreflect` and `kern:thm:ur` in `T_UR`: the accumulator
`φ(n, a, b)` (`kern:lem:acc`), commutativity of the maximum `a + d(b, a) = b + d(a, b)`
(`kern:lem:max`), the reflection `Δ(a, b) = sg(d(a, b) + d(b, a))` of equality
(`kern:lem:urreflect`), equation induction by zero induction on `Δ(s(n), r(n))`, and

  `tur_iff_teq : Γ ⊢[TurAx] φ ↔ Γ ⊢[TeqAx] φ`:

`T_UR` and `T_eq` derive the same sequents, so `T_UR` inherits the bi-interpretation
of `T_eq` with `iPRA`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- `μ(x, a) = d(x, d(x, a))`. -/
def Tm.umu (x a : Tm n) : Tm n := Tm.ud x (Tm.ud x a)

/-- `m(a, b) = a + d(b, a)`. -/
def Tm.umx (a b : Tm n) : Tm n := Tm.add a (Tm.ud b a)

/-- The reflection of equality `Δ(a, b) = sg(d(a, b) + d(b, a))`. -/
def Tm.udelta (a b : Tm n) : Tm n := Tm.usg (Tm.add (Tm.ud a b) (Tm.ud b a))

lift_op₂ umu umx udelta
ulift_op₂ umu umx udelta

/-- The accumulator `φ(x, a, b) = μ(x, a) + μ(d(x, a), d(b, a))` as a term. -/
def Tm.uphi (x a b : Tm n) : Tm n := Tm.add (Tm.umu x a) (Tm.umu (Tm.ud x a) (Tm.ud b a))

@[simp] theorem Tm.subst_uphi (σ : Fin n → Tm m) (x a b : Tm n) :
    Syn.subst σ (Tm.uphi x a b) = Tm.uphi (Syn.subst σ x) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [Tm.uphi]

namespace U

variable {Γ : List (Fm Tm n)} {Γ' : List (Fm Tm m)}

theorem umu_eq (x a : U Γ) : umu x a = ud x (ud x a) := by
  induction x, a using U.ind₂ with | _ a b => rfl

theorem umx_eq (a b : U Γ) : umx a b = a + ud b a := by
  induction a, b using U.ind₂ with | _ a b => rfl

theorem udelta_eq (a b : U Γ) : udelta a b = usg (ud a b + ud b a) := by
  induction a, b using U.ind₂ with | _ a b => rfl

/-! ### The accumulator -/

/-- `kern:lem:acc` (i). -/
theorem umu_succ (x a : U Γ) : umu (succ x) a = umu x a + zf (ud (succ x) a) := by
  have k₀ := (upred_ud_succ x a).symm
  refine U.cases (ud (succ x) a) (fun e h => ?_) (fun e r h => ?_)
  · have h' := h
    simp only [UExt.map_ud, UExt.map_succ] at h'
    have k := congrArg e.map k₀
    simp only [UExt.map_ud, UExt.map_upred, UExt.map_succ, h', upred_zero] at k
    simp [umu_eq, h', k]
  · have h' := h
    simp only [UExt.map_ud, UExt.map_succ] at h'
    have k := congrArg e.map k₀
    simp only [UExt.map_ud, UExt.map_upred, UExt.map_succ, h', upred_succ] at k
    simp [umu_eq, h', k]

/-- The accumulator `φ(x, a, b) = μ(x, a) + μ(d(x, a), d(b, a))`. -/
def uphi (x a b : U Γ) : U Γ := umu x a + umu (ud x a) (ud b a)

@[simp] theorem mk_uphi (x a b : Tm n) :
    mk Γ (Tm.uphi x a b) = uphi (mk Γ x) (mk Γ a) (mk Γ b) := rfl

theorem map_uphi (e : UExt Γ Γ') (x a b : U Γ) :
    e.map (uphi x a b) = uphi (e.map x) (e.map a) (e.map b) := by
  simp [uphi]

@[simp] theorem uphi_zero (a b : U Γ) : uphi 0 a b = 0 := by simp [uphi, umu_eq]

theorem uphi_succ_zf (x a b : U Γ) :
    uphi (succ x) a b = uphi x a b + zf (ud (ud (succ x) a) (ud b a)) := by
  have k₀ := (upred_ud_succ x a).symm
  refine U.cases (ud (succ x) a) (fun e h => ?_) (fun e r h => ?_)
  · have h' := h
    simp only [UExt.map_ud, UExt.map_succ] at h'
    have k := congrArg e.map k₀
    simp only [UExt.map_ud, UExt.map_upred, UExt.map_succ, h', upred_zero] at k
    simp [uphi, h', k, umu_eq]
  · have h' := h
    simp only [UExt.map_ud, UExt.map_succ] at h'
    have k := congrArg e.map k₀
    simp only [UExt.map_ud, UExt.map_upred, UExt.map_succ, h', upred_succ] at k
    simp only [uphi, UExt.map_add, UExt.map_umu, UExt.map_ud, UExt.map_succ, UExt.map_zf, h', k,
      umu_succ, zf_succ, add_zero]
    abel

/-- `kern:lem:acc` (ii). -/
theorem uphi_succ (x a b : U Γ) :
    uphi (succ x) a b = uphi x a b + usg (ud a x + ud b x) := by
  rw [uphi_succ_zf, zf_ud_ud, zf_ud_succ, zf_ud_succ, uor_usg]

/-- `kern:lem:acc` (iii). -/
theorem umx_rec (a b : U Γ) : umx a b = umx (upred a) (upred b) + usg (a + b) := by
  refine U.cases a (fun e h => ?_) (fun e a' h => ?_)
  · refine U.cases (e.map b) (fun e' h' => ?_) (fun e' b' h' => ?_) <;>
      simp [umx_eq, h, h']
  · refine U.cases (e.map b) (fun e' h' => ?_) (fun e' b' h' => ?_) <;>
      simp [umx_eq, h, h', upred_ud_succ]

/-- **Commutativity of the maximum** (`kern:lem:max`). -/
theorem umx_step (A B Φ : U Γ) : umx (upred A) (upred B) + (Φ + usg (A + B)) = umx A B + Φ := by
  rw [umx_rec A B]; abel

theorem umx_step' (A B Φ : U Γ) : umx (upred B) (upred A) + (Φ + usg (A + B)) = umx B A + Φ := by
  rw [umx_rec B A, add_comm B A]; abel

@[simp] theorem umx_zero_right (x : U Γ) : umx x 0 = x := by simp [umx_eq]

@[simp] theorem umx_zero_left (x : U Γ) : umx 0 x = x := by simp [umx_eq]

/-- **Commutativity of the maximum** (`kern:lem:max`): `F(n) = m(d(a, n), d(b, n)) + φ(n, a, b)`
and `F'(n) = m(d(b, n), d(a, n)) + φ(n, a, b)` are constant, and agree at `n = b`. -/
theorem umx_comm (a b : U Γ) : umx a b = umx b a := by
  induction a, b using U.ind₂ with | _ a b
  have hF := cu (Γ := Γ)
    (Tm.add (Tm.umx (Tm.ud (shift a) (var 0)) (Tm.ud (shift b) (var 0))) (Tm.uphi (var 0) (shift a) (shift b)))
    (shift (Tm.umx a b)) (var 0) b (by simp) (by simp [uphi_succ, umx_step]) (by simp)
  have hF' := cu (Γ := Γ)
    (Tm.add (Tm.umx (Tm.ud (shift b) (var 0)) (Tm.ud (shift a) (var 0))) (Tm.uphi (var 0) (shift a) (shift b)))
    (shift (Tm.umx b a)) (var 0) b (by simp) (by simp [uphi_succ, umx_step']) (by simp)
  simp at hF hF'
  rw [← hF, ← hF']

theorem eq_zero_of_usg {u : U Γ} (h : usg u = 0) : u = 0 := by
  refine U.cases u (fun e he => by rw [he, UExt.map_zero]) (fun e z he => ?_)
  have k := congrArg e.map h
  rw [UExt.map_usg, he, usg_succ, UExt.map_zero] at k
  exact U.absurd k.symm _ _

theorem eq_zero_of_add {u v : U Γ} (h : u + v = 0) : u = 0 := by
  refine U.cases u (fun e he => by rw [he, UExt.map_zero]) (fun e z he => ?_)
  have k := congrArg e.map h
  rw [UExt.map_add, he, succ_add, UExt.map_zero] at k
  exact absurd_succ k _ _

/-- **Reflection of equality** (`kern:lem:urreflect`). -/
theorem eq_of_udelta {a b : U Γ} (h : udelta a b = 0) : a = b := by
  rw [udelta_eq] at h
  have h₁ := eq_zero_of_usg h
  have hab := eq_zero_of_add h₁
  have hba := eq_zero_of_add ((add_comm _ _).trans h₁)
  have k := umx_comm a b
  rw [umx_eq, umx_eq, hab, hba, add_zero, add_zero] at k
  exact k

@[simp] theorem udelta_self (a : U Γ) : udelta a a = 0 := by simp [udelta_eq]

theorem act_mk (ε : UExt Γ Γ') (e : Tm (n + 1)) (X : Tm m) :
    act ε e (mk Γ' X) = mk Γ' (Syn.subst (Fin.cases X ε.σ) e) := by
  show mk Γ' (Syn.subst (inst X) (Syn.subst (up ε.σ) e)) = _
  rw [Syn.subst_subst]
  congr 2; funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem act_udelta (ε : UExt Γ Γ') (s t : Tm (n + 1)) (x : U Γ') :
    act ε (Tm.udelta s t) x = udelta (act ε s x) (act ε t x) := by
  induction x using U.ind with | _ X
  simp [act, app_mk]

theorem act_wkb (ε : UExt (Γ.map Fm.shift) Γ') (q : Tm (n + 1)) :
    act ε (Tm.wkb q) = act ((UExt.shift Γ).comp ε) q := by
  funext x
  simp only [act, Tm.wkb]
  rw [Syn.subst_subst, up_comp]
  rfl

end U

open U in
/-- **Equation induction in `T_UR`**: zero induction (`kern:lem:zi`) on
`Δ(s(n), t(n))`, with the reflection of equality (`kern:thm:ur`). -/
theorem Tur.eqInd {Γ : List (Fm Tm n)} (s t : Tm (n + 1))
    (h0 : Γ ⊢[TurAx] (s ≐ t).subst (inst Tm.zero))
    (hS : (s ≐ t) :: Γ.map Fm.shift ⊢[TurAx] (s ≐ t).subst (repl (Tm.succ (var 0)))) :
    Γ ⊢[TurAx] Fm.all (s ≐ t) := by
  have key : ∀ {m : ℕ} {Γ' : List (Fm Tm m)} (ε : UExt Γ Γ') (x : U Γ'),
      act ε (Tm.udelta s t) x = 0 → act ε (Tm.udelta s t) (succ x) = 0 := by
    intro m Γ' ε x
    induction x using U.ind with | _ X
    intro hx
    rw [act_udelta] at hx
    have e := eq_of_udelta hx
    rw [act_mk, act_mk] at e
    have d := hS.substWeaken (Fin.cases X ε.σ)
      (Δ := ((s ≐ t).subst (Fin.cases X ε.σ)) :: Γ') (by
        intro φ hφ
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hφ
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact List.mem_cons_self
        · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hψ
          refine List.mem_cons_of_mem _ ?_
          rw [Fm.subst_shift]
          exact ε.sub χ hχ)
    have d' := d.trans (Δ := Γ') (fun ψ hψ => by
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact U.exact e
      · exact .hyp hψ)
    rw [Fm.subst_subst] at d'
    have e' : mk Γ' (Syn.subst (Fin.cases (Tm.succ X) ε.σ) s)
        = mk Γ' (Syn.subst (Fin.cases (Tm.succ X) ε.σ) t) := by
      have hσ : (fun i => Syn.subst (Fin.cases X ε.σ) (repl (Tm.succ (var 0)) i))
          = Fin.cases (Tm.succ X) ε.σ := by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [hσ] at d'
      exact sound d'
    rw [← mk_succ, act_udelta, act_mk, act_mk, e', udelta_self]
  have z := U.zi (Γ := Γ.map Fm.shift) (Tm.wkb (Tm.udelta s t))
    (by
      rw [← act_shift, ← UExt.map_zero (UExt.shift Γ), ← map_app_eq_act]
      show (UExt.shift Γ).map (mk Γ (Syn.subst (inst Tm.zero) (Tm.udelta s t))) = 0
      simp only [Tm.subst_udelta, mk_udelta]
      rw [sound h0, udelta_self, UExt.map_zero])
    (fun ε x hx => by rw [act_wkb] at hx ⊢; exact key _ x hx) (mk _ (var 0))
  rw [← act_shift, act_udelta] at z
  have k := eq_of_udelta z
  rw [act_mk, act_mk] at k
  have hv : (Fin.cases (var 0) (UExt.shift Γ).σ : Fin (n + 1) → Tm (n + 1)) = var := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hv, Syn.subst_id, Syn.subst_id] at k
  exact .allI (U.exact k)

/-- A derivation from one axiom set is a derivation from another that derives its
axioms. -/
theorem Prf.transferAx {Ax₁ Ax₂ : Theory Tm}
    (hA : ∀ {k : ℕ} {φ : Fm Tm k}, Ax₁ k φ → (([] : List (Fm Tm k)) ⊢[Ax₂] φ))
    {Γ : List (Fm Tm n)} {φ : Fm Tm n} (h : Γ ⊢[Ax₁] φ) : Γ ⊢[Ax₂] φ := by
  induction h with
  | hyp h => exact .hyp h
  | ax h σ => exact Prf.ofNil ((hA h).subst σ)
  | botE φ _ ih => exact .botE φ ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | allI _ ih => exact .allI ih
  | allE t _ ih => exact .allE t ih
  | exI t _ ih => exact .exI t ih
  | exE _ _ ih₁ ih₂ => exact .exE ih₁ ih₂
  | eqRefl t => exact .eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ => exact .eqSubst φ σ σ' ih₁ ih₂

/-- The induction axiom of `T_eq` in `T_UR`. -/
theorem tur_ind (s t : Tm (n + 1)) :
    ([] : List (Fm Tm n)) ⊢[TurAx] ((s ≐ t).subst (inst Tm.zero) ⟶
      Fm.all ((s ≐ t) ⟶ (s ≐ t).subst (repl (Tm.succ (var 0)))) ⟶ Fm.all (s ≐ t)) := by
  refine .impI (.impI (Tur.eqInd s t Prf.hyp1 ?_))
  have hm : (Fm.all ((s ≐ t) ⟶ (s ≐ t).subst (repl (Tm.succ (var 0))))).shift ∈
      (s ≐ t) :: List.map Fm.shift
        [Fm.all ((s ≐ t) ⟶ (s ≐ t).subst (repl (Tm.succ (var 0)))), (s ≐ t).subst (inst Tm.zero)] :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self)
  have h := Prf.allE (Ax := TurAx) (var 0) (Prf.hyp hm)
  rw [Fm.subst_up_succ_inst] at h
  exact .impE h Prf.hyp0

/-- Uniqueness of iteration in `T_eq` (`kern:prop:uniq`), as the axiom of `T_UR`. -/
theorem teq_ur (f h : Tm (n + 1)) :
    ([] : List (Fm Tm n)) ⊢[TeqAx]
      (Fm.all (Syn.subst (repl (Tm.succ (var 0))) f ≐ Syn.subst (inst f) (Tm.wkb h)) ⟶
        Fm.all (f ≐ Tm.iter (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f)) (Tm.wkb h))) := by
  refine .impI (Teq.eqInd f (Tm.iter (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f)) (Tm.wkb h))
    ?_ ?_)
  · simpa using Prf.eqSymm (Teq.iterZero (Γ := [Fm.all (Syn.subst (repl (Tm.succ (var 0))) f
      ≐ Syn.subst (inst f) (Tm.wkb h))]) (Syn.subst (inst Tm.zero) f) h)
  · have hm : (Fm.all (Syn.subst (repl (Tm.succ (var 0))) f ≐ Syn.subst (inst f) (Tm.wkb h))).shift ∈
        (f ≐ Tm.iter (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f)) (Tm.wkb h))
          :: List.map Fm.shift [Fm.all (Syn.subst (repl (Tm.succ (var 0))) f
            ≐ Syn.subst (inst f) (Tm.wkb h))] :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self)
    have hp := Prf.allE (Ax := TeqAx) (var 0) (Prf.hyp hm)
    rw [Fm.subst_up_succ_inst] at hp
    have hi := Prf.eqCongr1 (Ax := TeqAx) (Γ := (f ≐ Tm.iter (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f))
        (Tm.wkb h)) :: List.map Fm.shift [Fm.all (Syn.subst (repl (Tm.succ (var 0))) f
          ≐ Syn.subst (inst f) (Tm.wkb h))]) (Tm.wkb h) Prf.hyp0
    have hs := Teq.iterSucc (Γ := (f ≐ Tm.iter (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f))
        (Tm.wkb h)) :: List.map Fm.shift [Fm.all (Syn.subst (repl (Tm.succ (var 0))) f
          ≐ Syn.subst (inst f) (Tm.wkb h))]) (var 0) (Syn.shift (Syn.subst (inst Tm.zero) f)) (Tm.wkb h)
    simp only [Fm.subst_eq, Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
      Tm.subst_up_repl_wkb] at hp hs ⊢
    exact Prf.eqTrans hp (Prf.eqTrans hi (Prf.eqSymm hs))

/-- **`T_UR` and `T_eq` derive the same sequents** (`kern:thm:ur`). -/
theorem tur_iff_teq {Γ : List (Fm Tm n)} {φ : Fm Tm n} : (Γ ⊢[TurAx] φ) ↔ (Γ ⊢[TeqAx] φ) := by
  constructor
  · refine Prf.transferAx (fun {k φ} h => ?_)
    cases h with
    | iterZero a h => exact .axm (.iterZero a h)
    | iterSucc c a h => exact .axm (.iterSucc c a h)
    | cover => exact .axm .cover
    | sep => exact .axm .sep
    | ur f h => exact teq_ur f h
  · refine Prf.transferAx (fun {k φ} h => ?_)
    cases h with
    | iterZero a h => exact .axm (.iterZero a h)
    | iterSucc c a h => exact .axm (.iterSucc c a h)
    | cover => exact .axm .cover
    | sep => exact .axm .sep
    | ind s t => exact tur_ind s t

end LeanProofs.ConciseIPRA
