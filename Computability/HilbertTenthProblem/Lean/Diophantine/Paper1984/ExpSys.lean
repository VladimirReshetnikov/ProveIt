import Diophantine.Paper1984.ExpPrim
import Diophantine.Paper1984.Normalize

/-!
# Jones–Matijasevič 1984, §2–§3: acceptance is singlefold unary exponential Diophantine

The conditions (24)–(39), with the base fixed as `Q = 2^{x+s+l+2}` "for singlefoldness", are
translated by the methods of §2 (order (3), masking (8)–(13), one-place exponentials (9)) into a
finite system of unary exponential equations. The unknowns `s, Q, I, R_j, L_i` of a solution are
uniquely determined (`sysQ_unique`, from the canonical digits of `sys_canonical`), and so are the
auxiliary unknowns of the translation. Hence `accepts_sfu`: for a well-formed program the set of
accepted inputs is singlefold unary exponential Diophantine.
-/

namespace JM1984
namespace RM

open Exp Exp.UTerm Finset

variable {r : ℕ}

/-! ### Additional closure properties -/

namespace SFUx

open Exp.SFU

theorem forall_fin {α : Type} : ∀ {n : ℕ} (S : Fin n → (α → ℕ) → Prop), (∀ i, Exp.SFU (S i)) →
    Exp.SFU (fun a => ∀ i, S i a)
  | 0, _, _ => Exp.SFU.true.congr (fun a => ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩)
  | n + 1, S, h => ((h 0).and (forall_fin (fun i => S i.succ) (fun i => h i.succ))).congr
      (fun a => ⟨fun ⟨h0, hs⟩ i => Fin.cases h0 hs i, fun h => ⟨h 0, fun i => h i.succ⟩⟩)

/-- `∃ Z, Z + t₁ = t₂ ∧ u ≼ Z`: masking against a difference. -/
theorem maskDiff {α : Type} (t₁ t₂ u : UTerm α) :
    Exp.SFU (fun a => ∃ Z, Z + t₁.eval a = t₂.eval a ∧ u.eval a ≼ Z) := by
  have h := ((Exp.SFU.eq (unk (0 : Fin 1) + lift t₁) (lift t₂)).and
    (mask (lift u) (unk (0 : Fin 1)))).exists_unique (fun a y z hy hz => by
      simp only [eval_add', eval_lift, eval_unk] at hy hz
      funext j; fin_cases j; simp only [Fin.zero_eta]; omega)
  refine h.congr (fun a => ?_)
  simp only [eval_add', eval_lift, eval_unk]
  exact ⟨fun ⟨y, hy⟩ => ⟨y 0, hy⟩, fun ⟨Z, hZ⟩ => ⟨fun _ => Z, hZ⟩⟩

/-- A finite sum of terms. -/
def tsum {α : Type} : ℕ → (ℕ → UTerm α) → UTerm α
  | 0, _ => const 0
  | n + 1, f => tsum n f + f n

theorem eval_tsum {α : Type} (n : ℕ) (f : ℕ → UTerm α) (v : α → ℕ) :
    (tsum n f).eval v = ∑ i ∈ range n, (f i).eval v := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tsum, ih, sum_range_succ]

end SFUx

/-! ### The unknowns and their terms -/

open SFUx Exp.SFU

variable (P : Program r)

/-- The number of main unknowns `s, Q, I, R_1, …, R_r, L_0, …, L_l`. -/
abbrev nU : ℕ := 3 + r + P.length

/-- Parameters `x` and the main unknowns. -/
abbrev Var : Type := Unit ⊕ Fin (nU P)

/-- Reading the input from a valuation. -/
def xOf (p : Var P → ℕ) : ℕ := p (Sum.inl ())
def sOf (p : Var P → ℕ) : ℕ := p (Sum.inr ⟨0, by unfold nU; omega⟩)
def QOf (p : Var P → ℕ) : ℕ := p (Sum.inr ⟨1, by unfold nU; omega⟩)
def IOf (p : Var P → ℕ) : ℕ := p (Sum.inr ⟨2, by unfold nU; omega⟩)
def ROf (p : Var P → ℕ) (j : Fin r) : ℕ := p (Sum.inr ⟨3 + j, by unfold nU; omega⟩)
def LOf (p : Var P → ℕ) (i : ℕ) : ℕ := if h : i < P.length then p (Sum.inr ⟨3 + r + i, by unfold nU; omega⟩) else 0

def tX : UTerm (Var P) := var (Sum.inl ())
def tS : UTerm (Var P) := var (Sum.inr ⟨0, by unfold nU; omega⟩)
def tQ : UTerm (Var P) := var (Sum.inr ⟨1, by unfold nU; omega⟩)
def tI : UTerm (Var P) := var (Sum.inr ⟨2, by unfold nU; omega⟩)
def tR (j : Fin r) : UTerm (Var P) := var (Sum.inr ⟨3 + j, by unfold nU; omega⟩)
def tL (i : ℕ) : UTerm (Var P) := if h : i < P.length then var (Sum.inr ⟨3 + r + i, by unfold nU; omega⟩) else const 0

section evals
variable {P} (p : Var P → ℕ)
@[simp] theorem eval_tX : (tX P).eval p = xOf P p := rfl
@[simp] theorem eval_tS : (tS P).eval p = sOf P p := rfl
@[simp] theorem eval_tQ : (tQ P).eval p = QOf P p := rfl
@[simp] theorem eval_tI : (tI P).eval p = IOf P p := rfl
@[simp] theorem eval_tR (j : Fin r) : (tR P j).eval p = ROf P p j := rfl
@[simp] theorem eval_tL (i : ℕ) : (tL P i).eval p = LOf P p i := by
  unfold tL LOf; split_ifs <;> rfl
end evals

/-- The encoded history term of an operand. -/
def tOp : Operand r → UTerm (Var P)
  | .reg j => tR P j
  | .zero => const 0
  | .one => tI P

@[simp] theorem eval_tOp (p : Var P → ℕ) (a : Operand r) :
    (tOp P a).eval p = a.enc (IOf P p) (ROf P p) := by
  cases a <;> rfl

/-- The exponent `x + s + l + 2` of the base. -/
def tq : UTerm (Var P) := tX P + tS P + const (P.length + 1)

/-- The translated line condition. -/
def lineE (i : ℕ) (p : Var P → ℕ) : Cmd r → Prop
  | .goto k => QOf P p * LOf P p i ≼ LOf P p k
  | .ifLt a b k => QOf P p * LOf P p i ≼ LOf P p k + LOf P p (i + 1) ∧
      ∃ Z, Z + 2 * b.enc (IOf P p) (ROf P p) =
        LOf P p k + QOf P p * IOf P p + 2 * a.enc (IOf P p) (ROf P p) ∧ QOf P p * LOf P p i ≼ Z
  | .ifLe a b k => QOf P p * LOf P p i ≼ LOf P p k + LOf P p (i + 1) ∧
      ∃ Z, Z + 2 * a.enc (IOf P p) (ROf P p) =
        LOf P p (i + 1) + QOf P p * IOf P p + 2 * b.enc (IOf P p) (ROf P p) ∧ QOf P p * LOf P p i ≼ Z
  | .arith _ => QOf P p * LOf P p i ≼ LOf P p (i + 1)
  | .stop => True

theorem lineE_sfu (i : ℕ) (c : Cmd r) : Exp.SFU (fun p => lineE P i p c) := by
  cases c with
  | goto k => exact (mask (tQ P * tL P i) (tL P k)).congr (fun p => by simp [lineE])
  | ifLt a b k =>
    exact ((mask (tQ P * tL P i) (tL P k + tL P (i + 1))).and
      (maskDiff (const 2 * tOp P b) (tL P k + tQ P * tI P + const 2 * tOp P a)
        (tQ P * tL P i))).congr (fun p => by simp [lineE])
  | ifLe a b k =>
    exact ((mask (tQ P * tL P i) (tL P k + tL P (i + 1))).and
      (maskDiff (const 2 * tOp P a) (tL P (i + 1) + tQ P * tI P + const 2 * tOp P b)
        (tQ P * tL P i))).congr (fun p => by simp [lineE])
  | arith δ => exact (mask (tQ P * tL P i) (tL P (i + 1))).congr (fun p => by simp [lineE])
  | stop => exact Exp.SFU.true.congr (fun p => by simp [lineE])

/-- The translated register equation. -/
def regE (p : Var P → ℕ) (j : Fin r) : Prop :=
  ROf P p j + ∑ i ∈ range P.length, (if delta P i j = -1 then QOf P p * LOf P p i else 0)
    = QOf P p * ROf P p j + ∑ i ∈ range P.length, (if delta P i j = 1 then QOf P p * LOf P p i else 0)
      + (if j.val = 0 then xOf P p else 0)

theorem regE_sfu (j : Fin r) : Exp.SFU (fun p => regE P p j) := by
  refine (Exp.SFU.eq (tR P j + tsum P.length (fun i => if delta P i j = -1 then tQ P * tL P i else const 0))
    (tQ P * tR P j + tsum P.length (fun i => if delta P i j = 1 then tQ P * tL P i else const 0) +
      (if j.val = 0 then tX P else const 0))).congr (fun p => ?_)
  simp only [regE, eval_add', eval_mul', eval_tsum, eval_tR, eval_tQ]
  have h1 : ∀ c : ℤ, ∑ i ∈ range P.length, (if delta P i j = c then tQ P * tL P i else const 0).eval p =
      ∑ i ∈ range P.length, (if delta P i j = c then QOf P p * LOf P p i else 0) :=
    fun c => sum_congr rfl (fun i _ => by split_ifs <;> simp)
  have h2 : (if j.val = 0 then tX P else const 0).eval p = if j.val = 0 then xOf P p else 0 := by
    split_ifs <;> simp
  rw [h1, h1, h2]

/-- The translated system (24)–(39) with the base fixed. -/
def ExpCond (p : Var P → ℕ) : Prop :=
  2 * (xOf P p + sOf P p) < QOf P p ∧ P.length < QOf P p ∧
  QOf P p = 2 ^ (xOf P p + sOf P p + (P.length + 1)) ∧
  1 + QOf P p * IOf P p = IOf P p + 2 ^ ((xOf P p + sOf P p + (P.length + 1)) * (sOf P p + 1)) ∧
  (∀ j : Fin r, ∃ Z, Z + IOf P p = 2 ^ (xOf P p + sOf P p + P.length) * IOf P p ∧ ROf P p j ≼ Z) ∧
  IOf P p = ∑ i ∈ range P.length, LOf P p i ∧
  (∀ i : Fin P.length, LOf P p i ≼ IOf P p) ∧
  1 ≼ LOf P p 0 ∧
  LOf P p (P.length - 1) = 2 ^ ((xOf P p + sOf P p + (P.length + 1)) * sOf P p) ∧
  (∀ i : Fin P.length, ∀ c, P[i.val]? = some c → lineE P i p c) ∧
  (∀ j : Fin r, regE P p j)

theorem expCond_sfu : Exp.SFU (ExpCond P) := by
  have hlines : Exp.SFU (fun p => ∀ i : Fin P.length, ∀ c, P[i.val]? = some c → lineE P i p c) := by
    refine (forall_fin (fun i p => lineE P i p (P[i.val]'i.isLt)) (fun i => lineE_sfu P i _)).congr
      (fun p => ⟨fun h i c hc => ?_, fun h i => h i _ (List.getElem?_eq_getElem i.isLt)⟩)
    rw [List.getElem?_eq_getElem i.isLt, Option.some.injEq] at hc
    rw [← hc]; exact h i
  refine ((lt (const 2 * (tX P + tS P)) (tQ P)).and ((lt (const P.length) (tQ P)).and
    ((Exp.SFU.eq (tQ P) (pow2 (tq P))).and
    ((Exp.SFU.eq (const 1 + tQ P * tI P) (tI P + pow2 (tq P * (tS P + const 1)))).and
    ((forall_fin (fun j p => ∃ Z, Z + IOf P p = 2 ^ (xOf P p + sOf P p + P.length) * IOf P p ∧
        ROf P p j ≼ Z) (fun j => (maskDiff (tI P) (pow2 (tX P + tS P + const P.length) * tI P)
          (tR P j)).congr (fun p => by simp))).and
    ((Exp.SFU.eq (tI P) (tsum P.length (tL P))).and
    ((forall_fin (n := P.length) (fun i p => LOf P p i ≼ IOf P p) (fun i => (mask (tL P i) (tI P)).congr
        (fun p => by simp))).and
    ((mask (const 1) (tL P 0)).and
    ((Exp.SFU.eq (tL P (P.length - 1)) (pow2 (tq P * tS P))).and
    (hlines.and (forall_fin (fun j p => regE P p j) (fun j => regE_sfu P j)))))))))))).congr
    (fun p => ?_)
  simp only [ExpCond, tq, eval_add', eval_mul', eval_pow2, eval_const, eval_tX, eval_tS, eval_tQ,
    eval_tI, eval_tL, eval_tsum]

/-! ### The translation is faithful -/

section faithful

variable {P}

theorem sys_congr_L (hP : WF P) {x s Q I : ℕ} {R : Fin r → ℕ} {L L' : ℕ → ℕ}
    (hL : ∀ i < P.length, L i = L' i) (H : Sys P x s Q I R L) : Sys P x s Q I R L' := by
  have hlen := hP.pos
  have hlast : ∀ i c, P[i]? = some c → c ≠ Cmd.stop → i + 1 < P.length := by
    intro i c hc hne
    have hi := (List.getElem?_eq_some_iff.1 hc).1
    by_contra h
    have : i = P.length - 1 := by omega
    subst this
    rw [hP.last_stop] at hc
    exact hne (Option.some.inj hc).symm
  refine ⟨H.c24, H.c25, H.c26, H.c27, H.c29, ?_, fun i hi => ?_, ?_, ?_, fun i c hc => ?_,
    fun j => ?_⟩
  · rw [H.c30]; exact sum_congr rfl (fun i hi => hL i (mem_range.1 hi))
  · rw [← hL i hi]; exact H.c31 i hi
  · rw [← hL 0 hlen]; exact H.c32
  · rw [← hL _ (by omega)]; exact H.c33
  · have h := H.lines i c hc
    have hi := (List.getElem?_eq_some_iff.1 hc).1
    cases c with
    | goto k =>
      have hk := hP.goto_lt _ _ hc
      simp only [lineCond] at h ⊢; rwa [← hL i hi, ← hL k hk]
    | ifLt a b k =>
      have hk := (hP.ifLt_ok _ _ _ _ hc).1
      have hi1 := hlast _ _ hc (by simp)
      simp only [lineCond] at h ⊢; rwa [← hL i hi, ← hL k hk, ← hL (i + 1) hi1]
    | ifLe a b k =>
      have hk := (hP.ifLe_ok _ _ _ _ hc).1
      have hi1 := hlast _ _ hc (by simp)
      simp only [lineCond] at h ⊢; rwa [← hL i hi, ← hL k hk, ← hL (i + 1) hi1]
    | arith δ =>
      have hi1 := hlast _ _ hc (by simp)
      simp only [lineCond] at h ⊢; rwa [← hL i hi, ← hL (i + 1) hi1]
    | stop => trivial
  · have h := H.regs j
    have hs : ∀ c : ℤ, ∑ i ∈ range P.length, (if delta P i j = c then Q * L i else 0) =
        ∑ i ∈ range P.length, (if delta P i j = c then Q * L' i else 0) :=
      fun c => sum_congr rfl (fun i hi => by rw [hL i (mem_range.1 hi)])
    unfold regEq at h ⊢
    rwa [hs, hs] at h

/-- The operand bound needed to remove truncated subtraction. -/
theorem two_enc_le {Q I : ℕ} {R : Fin r → ℕ} (hQ : 2 ≤ Q) (hR : ∀ j, R j ≼ (Q / 2 - 1) * I)
    (a : Operand r) : 2 * a.enc I R ≤ Q * I := by
  cases a with
  | reg j =>
    have h := Mask.le (hR j)
    simp only [Operand.enc]
    have : 2 * (Q / 2 - 1) ≤ Q := by omega
    calc 2 * R j ≤ 2 * ((Q / 2 - 1) * I) := by omega
      _ = (2 * (Q / 2 - 1)) * I := by ring
      _ ≤ Q * I := Nat.mul_le_mul_right _ this
  | zero => simp [Operand.enc]
  | one => simp only [Operand.enc]; exact Nat.mul_le_mul_right _ hQ

theorem expCond_iff (hP : WF P) (p : Var P → ℕ) :
    ExpCond P p ↔ Sys P (xOf P p) (sOf P p) (QOf P p) (IOf P p) (ROf P p) (LOf P p) ∧
      QOf P p = 2 ^ (xOf P p + sOf P p + (P.length + 1)) := by
  have hlen := hP.pos
  constructor
  · rintro ⟨h24, h25, h26, h27, h29, h30, h31, h32, h33, hlines, hregs⟩
    set x := xOf P p
    set s := sOf P p
    set Q := QOf P p
    set I := IOf P p
    set R := ROf P p
    set L := LOf P p
    set q := x + s + (P.length + 1) with hq
    have hhalf : 2 ^ q / 2 = 2 ^ (x + s + P.length) := by
      rw [two_pow_div_two (by omega)]; rfl
    have hQ2 : 2 ≤ Q := by omega
    have hQpow : ∀ n, Q ^ n = 2 ^ (q * n) := fun n => by rw [h26, pow_mul]
    have h29' : ∀ j, R j ≼ (Q / 2 - 1) * I := by
      intro j
      obtain ⟨Z, hZ, hRZ⟩ := h29 j
      rw [h26, hhalf]
      have : Z = (2 ^ (x + s + P.length) - 1) * I := by
        have h1 : 1 ≤ 2 ^ (x + s + P.length) := Nat.one_le_two_pow
        rw [Nat.sub_one_mul]; omega
      rwa [← this]
    refine ⟨⟨h24, h25, ⟨q, h26⟩, ?_, h29', h30, fun i hi => h31 ⟨i, hi⟩, h32, ?_, ?_, hregs⟩, h26⟩
    · rw [hQpow, Nat.sub_one_mul]
      have : I ≤ Q * I := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [hQpow]; exact h33
    · intro i c hc
      have hi := (List.getElem?_eq_some_iff.1 hc).1
      have h := hlines ⟨i, hi⟩ c hc
      cases c with
      | goto k => exact h
      | arith δ => exact h
      | stop => trivial
      | ifLt a b k =>
        obtain ⟨h1, Z, hZ, hQZ⟩ := h
        have hZ' : Z + 2 * b.enc I R = L k + Q * I + 2 * a.enc I R := hZ
        refine ⟨h1, ?_⟩
        rwa [show L k + Q * I + 2 * a.enc I R - 2 * b.enc I R = Z by omega]
      | ifLe a b k =>
        obtain ⟨h1, Z, hZ, hQZ⟩ := h
        have hZ' : Z + 2 * a.enc I R = L (i + 1) + Q * I + 2 * b.enc I R := hZ
        refine ⟨h1, ?_⟩
        rwa [show L (i + 1) + Q * I + 2 * b.enc I R - 2 * a.enc I R = Z by omega]
  · rintro ⟨H, h26⟩
    set x := xOf P p
    set s := sOf P p
    set Q := QOf P p
    set I := IOf P p
    set R := ROf P p
    set L := LOf P p
    set q := x + s + (P.length + 1) with hq
    have hhalf : 2 ^ q / 2 = 2 ^ (x + s + P.length) := by
      rw [two_pow_div_two (by omega)]; rfl
    have hQ2 : 2 ≤ Q := by have := H.c25; omega
    have hQpow : ∀ n, Q ^ n = 2 ^ (q * n) := fun n => by rw [h26, pow_mul]
    have henc := two_enc_le hQ2 H.c29
    refine ⟨H.c24, H.c25, h26, ?_, fun j => ?_, H.c30, fun i => H.c31 i i.isLt, H.c32, ?_,
      fun i c hc => ?_, H.regs⟩
    · show 1 + Q * I = I + 2 ^ (q * (s + 1))
      have h := H.c27
      rw [hQpow, Nat.sub_one_mul] at h
      have : I ≤ Q * I := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · refine ⟨(2 ^ (x + s + P.length) - 1) * I, ?_, ?_⟩
      · show (2 ^ (x + s + P.length) - 1) * I + I = 2 ^ (x + s + P.length) * I
        have h1 : 1 ≤ 2 ^ (x + s + P.length) := Nat.one_le_two_pow
        rw [Nat.sub_one_mul]
        have : I ≤ 2 ^ (x + s + P.length) * I := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · have := H.c29 j
        rwa [h26, hhalf] at this
    · have := H.c33; rwa [hQpow] at this
    · have h := H.lines i c hc
      cases c with
      | goto k => exact h
      | arith δ => exact h
      | stop => trivial
      | ifLt a b k =>
        obtain ⟨h1, h2⟩ := h
        have := henc b
        refine ⟨h1, L k + Q * I + 2 * a.enc I R - 2 * b.enc I R, ?_, h2⟩
        show L k + Q * I + 2 * a.enc I R - 2 * b.enc I R + 2 * b.enc I R = L k + Q * I + 2 * a.enc I R
        omega
      | ifLe a b k =>
        obtain ⟨h1, h2⟩ := h
        have := henc a
        refine ⟨h1, L (i + 1) + Q * I + 2 * b.enc I R - 2 * a.enc I R, ?_, h2⟩
        show L (i + 1) + Q * I + 2 * b.enc I R - 2 * a.enc I R + 2 * a.enc I R =
          L (i + 1) + Q * I + 2 * b.enc I R
        omega

theorem run_none_mono {c : Config r} {t t' : ℕ} (h : run P c t = none) (ht : t ≤ t') :
    run P c t' = none := by
  induction t', ht using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [run_succ, ih]; rfl

/-- **The solutions with the fixed base are unique.** -/
theorem sysQ_unique (hP : WF P) {x s Q I s' Q' I' : ℕ} {R R' : Fin r → ℕ} {L L' : ℕ → ℕ}
    (H : Sys P x s Q I R L) (hQ : Q = 2 ^ (x + s + (P.length + 1)))
    (H' : Sys P x s' Q' I' R' L') (hQ' : Q' = 2 ^ (x + s' + (P.length + 1))) :
    s = s' ∧ Q = Q' ∧ I = I' ∧ R = R' ∧ ∀ i < P.length, L i = L' i := by
  obtain ⟨f1, i1, r1, l1, d1⟩ := sys_canonical hP H
  obtain ⟨f2, i2, r2, l2, d2⟩ := sys_canonical hP H'
  -- the halting times agree
  have hss : s = s' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := run_none_mono (P := P) (t := s + 1) (by rw [run_succ_of_eq f1]; exact step_final hP)
        (show s + 1 ≤ s' by omega)
      rw [f2] at this; cases this
    · have := run_none_mono (P := P) (t := s' + 1) (by rw [run_succ_of_eq f2]; exact step_final hP)
        (show s' + 1 ≤ s by omega)
      rw [f1] at this; cases this
  subst hss
  have hQQ : Q = Q' := by rw [hQ, hQ']
  subst hQQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  refine ⟨rfl, rfl, by rw [i1, i2], ?_, ?_⟩
  · funext j
    rw [← blocks_digit hQ0 (r1 j), ← blocks_digit hQ0 (r2 j)]
    refine blocks_congr (fun t ht => ?_)
    obtain ⟨c, hc⟩ := run_isSome_of_le f1 t (by omega)
    rw [(d1 t (by omega) c hc).1 j, (d2 t (by omega) c hc).1 j]
  · intro i hi
    rw [← blocks_digit hQ0 (l1 i hi), ← blocks_digit hQ0 (l2 i hi)]
    refine blocks_congr (fun t ht => ?_)
    obtain ⟨c, hc⟩ := run_isSome_of_le f1 t (by omega)
    rw [(d1 t (by omega) c hc).2 i hi, (d2 t (by omega) c hc).2 i hi]

end faithful

/-- The main unknowns as a vector. -/
def vecOf (s Q I : ℕ) (R : Fin r → ℕ) (L : ℕ → ℕ) : Fin (nU P) → ℕ := fun idx =>
  if h0 : idx.val = 0 then s else if h1 : idx.val = 1 then Q else if h2 : idx.val = 2 then I
  else if h : idx.val < 3 + r then R ⟨idx.val - 3, by omega⟩ else L (idx.val - 3 - r)

/-- **Acceptance by a well-formed register machine is singlefold unary exponential
Diophantine.** -/
theorem accepts_sfu (hP : WF P) : Exp.SFU (fun a : Unit → ℕ => Accepts P (a ())) := by
  have hlen := hP.pos
  refine ((expCond_sfu P).exists_unique (fun a y z hy hz => ?_)).congr (fun a => ?_)
  · obtain ⟨H1, hQ1⟩ := (expCond_iff hP _).1 hy
    obtain ⟨H2, hQ2⟩ := (expCond_iff hP _).1 hz
    obtain ⟨hs, hQ, hI, hR, hL⟩ := sysQ_unique hP H1 hQ1 H2 hQ2
    funext idx
    have hidx := idx.isLt
    unfold nU at hidx
    by_cases h0 : idx.val = 0
    · have : idx = ⟨0, by simp only [nU]; omega⟩ := Fin.ext h0
      rw [this]; exact hs
    by_cases h1 : idx.val = 1
    · have : idx = ⟨1, by simp only [nU]; omega⟩ := Fin.ext h1
      rw [this]; exact hQ
    by_cases h2 : idx.val = 2
    · have : idx = ⟨2, by simp only [nU]; omega⟩ := Fin.ext h2
      rw [this]; exact hI
    by_cases h3 : idx.val < 3 + r
    · have := congrFun hR ⟨idx.val - 3, by omega⟩
      simp only [ROf] at this
      rwa [show (⟨3 + (idx.val - 3), _⟩ : Fin (nU P)) = idx from Fin.ext (by simp; omega)] at this
    · have := hL (idx.val - 3 - r) (by omega)
      simp only [LOf, dif_pos (show idx.val - 3 - r < P.length by omega)] at this
      rwa [show (⟨3 + r + (idx.val - 3 - r), _⟩ : Fin (nU P)) = idx from Fin.ext (by simp; omega)] at this
  · constructor
    · rintro ⟨y, hy⟩
      obtain ⟨H, -⟩ := (expCond_iff hP _).1 hy
      exact accepts_of_sys hP H
    · intro hacc
      obtain ⟨s, Q, I, R, L, H, hQ⟩ := sys_of_accepts hP hacc
      refine ⟨vecOf P s Q I R L, (expCond_iff hP _).2 ⟨?_, ?_⟩⟩
      · have e1 : xOf P (join a (vecOf P s Q I R L)) = a () := rfl
        have e2 : sOf P (join a (vecOf P s Q I R L)) = s := rfl
        have e3 : QOf P (join a (vecOf P s Q I R L)) = Q := rfl
        have e4 : IOf P (join a (vecOf P s Q I R L)) = I := rfl
        have e5 : ROf P (join a (vecOf P s Q I R L)) = R := by
          funext j
          simp only [ROf, join, Sum.elim_inr, vecOf]
          rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
          congr 1; ext; simp
        rw [e1, e2, e3, e4, e5]
        refine sys_congr_L hP (fun i hi => ?_) H
        simp only [LOf, dif_pos hi, join, Sum.elim_inr, vecOf]
        rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
        congr 1; omega
      · show Q = 2 ^ (a () + s + (P.length + 1))
        rw [hQ]; congr 1

end RM
end JM1984
