import BusyBeaver.ZFC.Code254

/-! A code-dependent three-value model for the K + R(A,B)-fourth calculus,
including quantified stability and the literal gated KCode222 seed bundle.
Only the accepted cached Code254 module is imported. Native below transcribes
the six pinned KCode222 code definitions, without importing its theorem facade.
The semantic carrier is not a Tarski variable-assignment structure. -/
namespace K218KRAB
open SetTheory SetTheory.BusyBeaver.ZFC.Code254

inductive Value where
  | low | middle | top
  deriving DecidableEq
open Value

def j : Value → Value → Value
  | low, low => middle
  | low, _ => top
  | middle, _ => top
  | top, top => top
  | top, _ => middle

def r : Value → Value → Value
  | _, low => middle
  | _, middle => low
  | top, top => low
  | _, top => top

def q : Value → Value
  | top => top
  | _ => middle

def evalF : Nat → Nat → Value
  | 0, _ => top
  | _ + 1, 0 => top
  | fuel + 1, n + 1 =>
    match (n + 1) % 4 with
    | 0 => j (evalF fuel (Cantor.ofNat ((n + 1) / 4)).1)
              (evalF fuel (Cantor.ofNat ((n + 1) / 4)).2)
    | 1 => r (evalF fuel (Cantor.ofNat ((n + 1) / 4)).1)
              (evalF fuel (Cantor.ofNat ((n + 1) / 4)).2)
    | 2 => q (evalF fuel (Cantor.ofNat ((n + 1) / 4)).2)
    | _ => low

def eval (n : Nat) : Value := evalF (n + 1) n

theorem evalF_stable : ∀ (f g n : Nat), n < f → n < g → evalF f n = evalF g n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, 0, _, _ => rfl
  | f + 1, g + 1, n + 1, hf, hg => by
    have hz := ofNat_le ((n + 1) / 4)
    have hd : (n + 1) / 4 < n + 1 := Nat.div_lt_self (by omega) (by omega)
    simp only [evalF]
    split
    · rw [evalF_stable f g _ (by omega) (by omega),
          evalF_stable f g _ (by omega) (by omega)]
    · rw [evalF_stable f g _ (by omega) (by omega),
          evalF_stable f g _ (by omega) (by omega)]
    · rw [evalF_stable f g _ (by omega) (by omega)]
    · rfl

@[simp] theorem eval_zero : eval 0 = top := rfl

@[simp] theorem eval_wim (a b : Nat) : eval (wim a b) = j (eval a) (eval b) := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl,rfl⟩ := h
    have hz : wim 0 0 = 0 := by simp [wim,P,Cantor.toNat,Cantor.tri]
    rw [hz,eval_zero]
    rfl
  · have hp : 0 < P a b := by
      rcases Nat.eq_zero_or_pos (P a b) with h0 | h0
      · exact absurd (P_eq_zero h0) h
      · exact h0
    have ha := le_P_left a b
    have hb := le_P_right a b
    obtain ⟨m,hm⟩ : ∃ m, wim a b = m + 1 := ⟨wim a b - 1, by simp only [wim]; omega⟩
    have hmod : (m + 1) % 4 = 0 := by simp only [wim] at hm; omega
    have hdiv : (m + 1) / 4 = P a b := by simp only [wim] at hm; omega
    rw [eval,hm,evalF]
    simp only [hmod,hdiv,unP_P]
    rw [evalF_stable (m+1) (a+1) a (by simp only [wim] at hm; omega) (by omega),
        evalF_stable (m+1) (b+1) b (by simp only [wim] at hm; omega) (by omega)]
    rfl

@[simp] theorem eval_wel (a b : Nat) : eval (wel a b) = r (eval a) (eval b) := by
  have ha := le_P_left a b
  have hb := le_P_right a b
  obtain ⟨m,hm⟩ : ∃ m, wel a b = m + 1 := ⟨4 * P a b, rfl⟩
  have hmod : (m + 1) % 4 = 1 := by simp only [wel] at hm; omega
  have hdiv : (m + 1) / 4 = P a b := by simp only [wel] at hm; omega
  rw [eval,hm,evalF]
  simp only [hmod,hdiv,unP_P]
  rw [evalF_stable (m+1) (a+1) a (by simp only [wel] at hm; omega) (by omega),
      evalF_stable (m+1) (b+1) b (by simp only [wel] at hm; omega) (by omega)]
  rfl

@[simp] theorem eval_wal (i a : Nat) : eval (wal i a) = q (eval a) := by
  have ha := le_P_right i a
  obtain ⟨m,hm⟩ : ∃ m, wal i a = m + 1 := ⟨4 * P i a + 1, by simp only [wal]⟩
  have hmod : (m + 1) % 4 = 2 := by simp only [wal] at hm; omega
  have hdiv : (m + 1) / 4 = P i a := by simp only [wal] at hm; omega
  rw [eval,hm,evalF]
  simp only [hmod,hdiv,unP_P]
  rw [evalF_stable (m+1) (a+1) a (by simp only [wal] at hm; omega) (by omega)]
  rfl

@[simp] theorem eval_weq (a b : Nat) : eval (weq a b) = low := by
  obtain ⟨m,hm⟩ : ∃ m, weq a b = m + 1 := ⟨4 * P a b + 2, by simp only [weq]⟩
  have hmod : (m + 1) % 4 = 3 := by simp only [weq] at hm; omega
  rw [eval,hm,evalF]
  simp only [hmod]

@[simp] theorem eval_falsum : eval F = low := by
  rw [← wel_zero_zero,eval_wel,eval_zero]
  rfl

namespace Native
def growG (a b c : Nat) : Nat := wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))
def req (b k m : Nat) : Nat := wal b (wim m (wn (wal b (wim m (wn (wel b k))))))
def clos (a b k m : Nat) : Nat :=
  wal b (wim (wel b k) (wn (wal a (wim m (wn (wal a (wim (wal k (wim (wel k a) (wel k b)))
    (req b k m))))))))
def nks (a b c : Nat) : Nat := wal c (wim (clos a b c c) (wn (req b c c)))
def vrel (a b c : Nat) : Nat := wim (wel a b) (wal c (wel a b))
def bundle222 (a b c : Nat) : Nat := wn (wim (vrel a b c) (nks a b c))
end Native

def K (a b : Nat) := wim a (wim b a)
def QS (i a : Nat) := wim (wn (wn (wal i a))) (wal i a)

theorem r1_valid (a b : Nat) : eval (rho1 a b) = top := by
  simp only [rho1,wex,wn,eval_wim,eval_wal,eval_weq,eval_falsum]
  rfl
theorem r2_valid (a b c : Nat) : eval (rho2 a b c) = top := by
  simp only [rho2,eval_wim,eval_wal]
  cases eval b <;> cases eval c <;> rfl
theorem r3_valid (a b c : Nat) : eval (rho3 a b c) = top := by
  simp only [rho3,eval_wim,eval_weq,eval_wel]
  cases eval a <;> cases eval b <;> cases eval c <;> rfl
theorem r4_valid (a b c : Nat) : eval (rho4 a b c) = top := by
  simp only [rho4,eval_wim,eval_wal]
  cases eval c <;> rfl
theorem r5_valid (a b c : Nat) : eval (rho5 a b c) = top := by
  simp only [rho5,eval_wim,eval_weq,eval_wel]
  cases eval a <;> cases eval b <;> cases eval c <;> rfl
theorem r6_valid (a b : Nat) : eval (rho6 a b) = top := by
  simp only [rho6,wex,wn,eval_wim,eval_wal,eval_falsum]
  cases eval b <;> rfl
theorem g_valid (a b c : Nat) : eval (Native.growG a b c) = top := by
  simp only [Native.growG,eval_wim,eval_weq,eval_wal]
  rfl
theorem h_valid (a b c : Nat) : eval (rho8 a b c (wel a b)) = top := by
  simp only [rho8,eval_wim,eval_wel]
  cases eval a <;> cases eval b <;> cases eval c <;> rfl
theorem k_valid (a b : Nat) : eval (K a b) = top := by
  simp only [K,eval_wim]
  cases eval a <;> cases eval b <;> rfl
theorem qs_valid (i a : Nat) : eval (QS i a) = top := by
  simp only [QS,wn,eval_wim,eval_wal,eval_falsum]
  cases eval a <;> rfl

/-- Stronger ungated semantic check; the calculus below retains both gates. -/
theorem bundle_valid (a b c : Nat) : eval (Native.bundle222 a b c) = top := by
  simp only [Native.bundle222,Native.vrel,Native.nks,Native.clos,Native.req,
    wn,eval_wim,eval_wal,eval_wel,eval_falsum]
  cases eval a <;> cases eval b <;> cases eval c <;> rfl

theorem mp_valid {a b : Nat} (ha : eval a = top) (hab : eval (wim a b) = top) :
    eval b = top := by
  rw [eval_wim,ha] at hab
  cases hb : eval b <;> simp_all [j]

/-- Exact modified derivability; no unrestricted substitution or implication rule. -/
inductive Prov : Nat → Prop
  | truth : Prov 0
  | mp {a b : Nat} : Prov a → Prov (wim a b) → Prov b
  | gen (i : Nat) {a : Nat} : Prov a → Prov (wal i a)
  | r1 (a b : Nat) : Prov (rho1 a b)
  | r2 (a b c : Nat) : Prov (rho2 a b c)
  | r3 (a b c : Nat) : Prov (rho3 a b c)
  | r4 (a b c : Nat) : Prov (rho4 a b c)
  | r5 (a b c : Nat) : Prov (rho5 a b c)
  | r6 (a b : Nat) : Prov (rho6 a b)
  | g (a b c : Nat) : Prov (Native.growG a b c)
  | h (a b c : Nat) : Prov (rho8 a b c (wel a b))
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → Prov (Native.bundle222 a b c)
  | k (a b : Nat) : Prov (K a b)
  | qs (i a : Nat) : Prov (QS i a)

theorem sound {n : Nat} (h : Prov n) : eval n = top := by
  induction h with
  | truth => exact eval_zero
  | mp _ _ ih1 ih2 => exact mp_valid ih1 ih2
  | gen i _ ih => rw [eval_wal,ih]; rfl
  | r1 a b => exact r1_valid a b
  | r2 a b c => exact r2_valid a b c
  | r3 a b c => exact r3_valid a b c
  | r4 a b c => exact r4_valid a b c
  | r5 a b c => exact r5_valid a b c
  | r6 a b => exact r6_valid a b
  | g a b c => exact g_valid a b c
  | h a b c => exact h_valid a b c
  | bundle a b c _ _ => exact bundle_valid a b c
  | k a b => exact k_valid a b
  | qs i a => exact qs_valid i a

theorem no_falsum : ¬ Prov F := by
  intro h
  have hs := sound h
  rw [eval_falsum] at hs
  cases hs

theorem falsum_identity_code : wim F F = 16 := by rfl
theorem no_falsum_identity : ¬ Prov (wim F F) := by
  intro h
  have hs := sound h
  rw [eval_wim,eval_falsum] at hs
  cases hs
theorem no_code16 : ¬ Prov 16 := by
  rw [← falsum_identity_code]
  exact no_falsum_identity

#print axioms evalF_stable
#print axioms eval_wim
#print axioms eval_wel
#print axioms eval_wal
#print axioms eval_weq
#print axioms eval_falsum
#print axioms r1_valid
#print axioms r2_valid
#print axioms r3_valid
#print axioms r4_valid
#print axioms r5_valid
#print axioms r6_valid
#print axioms g_valid
#print axioms h_valid
#print axioms k_valid
#print axioms qs_valid
#print axioms bundle_valid
#print axioms mp_valid
#print axioms sound
#print axioms no_falsum
#print axioms no_code16
end K218KRAB
