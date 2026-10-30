import FirstOrder.Fol
import BusyBeaver.ZFC.TarskiFalsity

/-!
The base-4 code calculus of the calibrated ZFC machines.

Mira-Cult's 254-state machine (and the 279-state full-logic control that
keeps its logical frontend) represents formulas by natural numbers:

```text
Imp(A,B) = 4·P(A,B)    Rel(i,j) = 4·P(i,j)+1    All(i,A) = 4·P(i,A)+2    Eq(i,j) = 4·P(i,j)+3
P(x,y) = tri(x+y) + y                 F = 1 = Rel(0,0)          0 = Imp(0,0) (truth)
```

with `¬A = A → F`, `A ∧ B = ¬(A → ¬B)` and `∃x A = ¬∀x ¬A`. The pairing is the
repository's `Cantor.toNat`. `C254` is the machine's calculus at the level of
codes: the truth code 0, modus ponens, generalization, the eight rows and
the gated bundle (container C, global-image collection G and atomic
vacuity, emitted only when `c ≠ a, b`). These definitions state the
mathematical content of the published code calculus (upstream
`ZF/m254/coq/logic/Codes254.v`, `Thm254.v`); this file is an independent
Lean formalization, not a port of those proofs.

Results:

* `c254_sound`: every derivable code decodes to a formula true in every
  irreflexive model in which all decoded bundles hold. The collision
  `Imp(0,0) = 0` is harmless because both readings are true.
* `c254_complete`: if the theory of encodable bundles has no irreflexive
  model, then the falsity code 1 is derivable. Atomic vacuity, which the
  calculus emits only inside the gated bundle, is projected out of it with
  the same gate, and the propositional steps use the Lukasiewicz basis.

The soundness model class uses all decoded bundles; the completeness
implication uses literal encodable bundles. Their comparison is not proved
here. The set-theoretic calibration must establish the stated model
obligations, followed separately by the enumerator and machine bridges.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254

open SetTheory.BusyBeaver.ZFC.Tarski
open NF

/-! ## Codes -/

def P (x y : Nat) : Nat := Cantor.toNat (x, y)

theorem unP_P (x y : Nat) : Cantor.ofNat (P x y) = (x, y) := Cantor.ofNat_toNat (x, y)

theorem le_P_left (x y : Nat) : x ≤ P x y := by
  have := Cantor.add_le_toNat x y; simp only [P]; omega

theorem le_P_right (x y : Nat) : y ≤ P x y := by
  have := Cantor.add_le_toNat x y; simp only [P]; omega

theorem P_eq_zero {x y : Nat} (h : P x y = 0) : x = 0 ∧ y = 0 := by
  have := Cantor.add_le_toNat x y
  simp only [P] at h
  omega

def wim (a b : Nat) : Nat := 4 * P a b
def wel (i j : Nat) : Nat := 4 * P i j + 1
def wal (i a : Nat) : Nat := 4 * P i a + 2
def weq (i j : Nat) : Nat := 4 * P i j + 3
def F : Nat := 1
def wn (a : Nat) : Nat := wim a F
def wa (a b : Nat) : Nat := wn (wim a (wn b))
def wex (x a : Nat) : Nat := wn (wal x (wn a))

theorem wel_zero_zero : wel 0 0 = F := by
  simp [wel, F, P, Cantor.toNat, Cantor.tri]

def rho8 (a b c u : Nat) : Nat := wim (wim (wim c u) a) (wim (wim a c) (wim b c))
def rho7 (a b c : Nat) : Nat := wim (weq c a) (wim (weq c b) (weq a b))
def rho6 (a b : Nat) : Nat := wim (wex a (wal a b)) b
def rho5 (a b c : Nat) : Nat := wim (weq c a) (wim (wel c b) (wel a b))
def rho4 (a b c : Nat) : Nat := wim (wal a (wal b c)) (wal b (wal a c))
def rho3 (a b c : Nat) : Nat := wim (weq a b) (wim (wel c a) (wel c b))
def rho2 (a b c : Nat) : Nat := wim (wal a (wim b c)) (wim (wal a b) (wal a c))
def rho1 (a b : Nat) : Nat := wex a (weq a b)

/-- Container C at the free point c. -/
def bundleC (a b c : Nat) : Nat :=
  wex b (wa (wal a (wim (wel a b)
                          (wa (wex c (wa (wal b (wim (wal c (wim (wel c b) (wel c a))) (wel b c)))
                                         (wel c b)))
                              (wal c (wim (wel c a) (wel c b))))))
            (wel c b))

/-- Global-image collection G for the matrix with code c. -/
def bundleG (a b c : Nat) : Nat :=
  wex c (wa (wal a (wim (wel a b) (wal b (wim c (wex b (wa c (wel b c)))))))
            (wal b (wim (wel b c) (wex a c))))

/-- The gated bundle: (C ∧ G) ∧ (membership vacuity ∧ equality vacuity). -/
def bundle (a b c : Nat) : Nat :=
  wa (wa (bundleC a b c) (bundleG a b c))
     (wa (wim (wel a b) (wal c (wel a b))) (wim (weq a b) (wal c (weq a b))))

/-- The machine's calculus at the level of codes. -/
inductive C254 : Nat → Prop
  | truth : C254 0
  | mp {t b : Nat} : C254 t → C254 (wim t b) → C254 b
  | gen (a : Nat) {h : Nat} : C254 h → C254 (wal a h)
  | r1 (a b : Nat) : C254 (rho1 a b)
  | r2 (a b c : Nat) : C254 (rho2 a b c)
  | r3 (a b c : Nat) : C254 (rho3 a b c)
  | r4 (a b c : Nat) : C254 (rho4 a b c)
  | r5 (a b c : Nat) : C254 (rho5 a b c)
  | r6 (a b : Nat) : C254 (rho6 a b)
  | r7 (a b c : Nat) : C254 (rho7 a b c)
  | r8 (a b c u : Nat) : C254 (rho8 a b c u)
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → C254 (bundle a b c)

/-! ## Decoding -/

/-- The truth formula `F → F` decoding code 0. -/
def T0 : NF := imp (rel 0 0) (rel 0 0)

def decF : Nat → Nat → NF
  | 0, _ => T0
  | _ + 1, 0 => T0
  | fuel + 1, n + 1 =>
    match (n + 1) % 4 with
    | 0 => imp (decF fuel (Cantor.ofNat ((n + 1) / 4)).1) (decF fuel (Cantor.ofNat ((n + 1) / 4)).2)
    | 1 => rel (Cantor.ofNat ((n + 1) / 4)).1 (Cantor.ofNat ((n + 1) / 4)).2
    | 2 => all (Cantor.ofNat ((n + 1) / 4)).1 (decF fuel (Cantor.ofNat ((n + 1) / 4)).2)
    | _ => NF.eq (Cantor.ofNat ((n + 1) / 4)).1 (Cantor.ofNat ((n + 1) / 4)).2

def dec (n : Nat) : NF := decF (n + 1) n

theorem ofNat_le (z : Nat) : (Cantor.ofNat z).1 ≤ z ∧ (Cantor.ofNat z).2 ≤ z := by
  have := Cantor.add_le_toNat (Cantor.ofNat z).1 (Cantor.ofNat z).2
  have h : Cantor.toNat ((Cantor.ofNat z).1, (Cantor.ofNat z).2) = z := Cantor.toNat_ofNat z
  constructor <;> omega

theorem decF_stable : ∀ (f g n : Nat), n < f → n < g → decF f n = decF g n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, 0, _, _ => rfl
  | f + 1, g + 1, n + 1, hf, hg => by
      have hz := ofNat_le ((n + 1) / 4)
      have hd : (n + 1) / 4 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      simp only [decF]
      split
      · rw [decF_stable f g _ (by omega) (by omega), decF_stable f g _ (by omega) (by omega)]
      · rfl
      · rw [decF_stable f g _ (by omega) (by omega)]
      · rfl

theorem dec_zero : dec 0 = T0 := rfl

theorem dec_wim {x y : Nat} (h : ¬ (x = 0 ∧ y = 0)) : dec (wim x y) = imp (dec x) (dec y) := by
  have hP : 0 < P x y := Nat.pos_of_ne_zero fun h0 => h (P_eq_zero h0)
  have hx := le_P_left x y
  have hy := le_P_right x y
  obtain ⟨m, hm⟩ : ∃ m, wim x y = m + 1 := ⟨wim x y - 1, by simp only [wim]; omega⟩
  have hmod : (m + 1) % 4 = 0 := by simp only [wim] at hm; omega
  have hdiv : (m + 1) / 4 = P x y := by simp only [wim] at hm; omega
  rw [dec, hm, decF]
  simp only [hmod, hdiv, unP_P]
  rw [decF_stable (m + 1) (x + 1) x (by simp only [wim] at hm; omega) (by omega),
    decF_stable (m + 1) (y + 1) y (by simp only [wim] at hm; omega) (by omega)]
  rfl

theorem dec_wel (i j : Nat) : dec (wel i j) = rel i j := by
  obtain ⟨m, hm⟩ : ∃ m, wel i j = m + 1 := ⟨4 * P i j, by simp only [wel]⟩
  have hmod : (m + 1) % 4 = 1 := by simp only [wel] at hm; omega
  have hdiv : (m + 1) / 4 = P i j := by simp only [wel] at hm; omega
  rw [dec, hm, decF]
  simp only [hmod, hdiv, unP_P]

theorem dec_weq (i j : Nat) : dec (weq i j) = NF.eq i j := by
  obtain ⟨m, hm⟩ : ∃ m, weq i j = m + 1 := ⟨4 * P i j + 2, by simp only [weq]⟩
  have hmod : (m + 1) % 4 = 3 := by simp only [weq] at hm; omega
  have hdiv : (m + 1) / 4 = P i j := by simp only [weq] at hm; omega
  rw [dec, hm, decF]
  simp only [hmod, hdiv, unP_P]

theorem dec_wal (i a : Nat) : dec (wal i a) = all i (dec a) := by
  have ha := le_P_right i a
  obtain ⟨m, hm⟩ : ∃ m, wal i a = m + 1 := ⟨4 * P i a + 1, by simp only [wal]⟩
  have hmod : (m + 1) % 4 = 2 := by simp only [wal] at hm; omega
  have hdiv : (m + 1) / 4 = P i a := by simp only [wal] at hm; omega
  rw [dec, hm, decF]
  simp only [hmod, hdiv, unP_P]
  rw [decF_stable (m + 1) (a + 1) a (by simp only [wal] at hm; omega) (by omega)]
  rfl

theorem dec_F : dec F = rel 0 0 := by
  rw [← wel_zero_zero, dec_wel]

/-! ## Semantics of decoded codes -/

universe u
variable {V : Type u}

theorem sat_T0 (mem : V → V → Prop) (e : Nat → V) : Tarski.Sat mem e T0 := fun h => h

theorem sat_wim (mem : V → V → Prop) (e : Nat → V) (x y : Nat) :
    Tarski.Sat mem e (dec (wim x y)) ↔ (Tarski.Sat mem e (dec x) → Tarski.Sat mem e (dec y)) := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    have : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]
    rw [this, dec_zero]
    exact ⟨fun _ h => h, fun _ => sat_T0 mem e⟩
  · rw [dec_wim h]; exact Iff.rfl

theorem sat_wal (mem : V → V → Prop) (e : Nat → V) (i a : Nat) :
    Tarski.Sat mem e (dec (wal i a)) ↔ ∀ d, Tarski.Sat mem (update e i d) (dec a) := by
  rw [dec_wal]; exact Iff.rfl

theorem sat_wel (mem : V → V → Prop) (e : Nat → V) (i j : Nat) :
    Tarski.Sat mem e (dec (wel i j)) ↔ mem (e i) (e j) := by
  rw [dec_wel]; exact Iff.rfl

theorem sat_weq (mem : V → V → Prop) (e : Nat → V) (i j : Nat) :
    Tarski.Sat mem e (dec (weq i j)) ↔ e i = e j := by
  rw [dec_weq]; exact Iff.rfl

theorem sat_F (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x) (e : Nat → V) :
    ¬ Tarski.Sat mem e (dec F) := by
  rw [dec_F]; exact hirr _

section Irreflexive

variable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
include hirr

theorem sat_wn (e : Nat → V) (a : Nat) : Tarski.Sat mem e (dec (wn a)) ↔ ¬ Tarski.Sat mem e (dec a) := by
  simp only [wn]; rw [sat_wim]
  exact ⟨fun h ha => sat_F mem hirr e (h ha), fun h ha => absurd ha h⟩

theorem sat_wa (e : Nat → V) (a b : Nat) :
    Tarski.Sat mem e (dec (wa a b)) ↔ Tarski.Sat mem e (dec a) ∧ Tarski.Sat mem e (dec b) := by
  simp only [wa]
  rw [sat_wn mem hirr, sat_wim, sat_wn mem hirr]
  exact ⟨fun h => ⟨Classical.byContradiction fun ha => h fun ha' => absurd ha' ha,
    Classical.byContradiction fun hb => h fun _ => hb⟩, fun ⟨ha, hb⟩ h => h ha hb⟩

theorem sat_wex (e : Nat → V) (x a : Nat) :
    Tarski.Sat mem e (dec (wex x a)) ↔ ∃ d, Tarski.Sat mem (update e x d) (dec a) := by
  simp only [wex]
  rw [sat_wn mem hirr, sat_wal]
  exact ⟨fun h => Classical.byContradiction fun hn =>
      h fun d => (sat_wn mem hirr _ a).mpr fun hd => hn ⟨d, hd⟩,
    fun ⟨d, hd⟩ h => (sat_wn mem hirr _ a).mp (h d) hd⟩

end Irreflexive

/-! ## Soundness of the code calculus -/

/-- Rows are valid in every irreflexive structure. -/
theorem rows_valid (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x) (e : Nat → V) :
    (∀ a b, Tarski.Sat mem e (dec (rho1 a b))) ∧
    (∀ a b c, Tarski.Sat mem e (dec (rho2 a b c))) ∧
    (∀ a b c, Tarski.Sat mem e (dec (rho3 a b c))) ∧
    (∀ a b c, Tarski.Sat mem e (dec (rho4 a b c))) ∧
    (∀ a b c, Tarski.Sat mem e (dec (rho5 a b c))) ∧
    (∀ a b, Tarski.Sat mem e (dec (rho6 a b))) ∧
    (∀ a b c, Tarski.Sat mem e (dec (rho7 a b c))) ∧
    (∀ a b c u, Tarski.Sat mem e (dec (rho8 a b c u))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp only [rho1]
    rw [sat_wex mem hirr]
    refine ⟨e b, ?_⟩
    rw [sat_weq]
    by_cases hab : b = a <;> simp [update, hab]
  · intro a b c
    simp only [rho2]
    rw [sat_wim, sat_wal, sat_wim, sat_wal, sat_wal]
    intro h1 h2 d
    exact (sat_wim mem _ b c).mp (h1 d) (h2 d)
  · intro a b c
    simp only [rho3]
    rw [sat_wim, sat_weq, sat_wim, sat_wel, sat_wel]
    intro h1 h2; rwa [← h1]
  · intro a b c
    simp only [rho4]
    rw [sat_wim]
    intro h
    rw [sat_wal]
    intro db
    rw [sat_wal]
    intro da
    by_cases hab : a = b
    · subst hab
      exact (sat_wal mem _ a c).mp ((sat_wal mem e a _).mp h db) da
    · have hh := (sat_wal mem _ b c).mp ((sat_wal mem _ a _).mp h da) db
      have hcomm : update (update e a da) b db = update (update e b db) a da := by
        funext n
        simp only [update]
        by_cases hn : n = b <;> by_cases hm : n = a
        · exact absurd (hm.symm.trans hn) hab
        · simp [hn, Ne.symm hab]
        · simp [hm, hab]
        · simp [hn, hm]
      rwa [hcomm] at hh
  · intro a b c
    simp only [rho5]
    rw [sat_wim, sat_weq, sat_wim, sat_wel, sat_wel]
    intro h1 h2; rwa [← h1]
  · intro a b
    simp only [rho6]
    rw [sat_wim, sat_wex mem hirr]
    rintro ⟨d, hd⟩
    rw [sat_wal] at hd
    have hh : update (update e a d) a (e a) = e := by
      funext n; by_cases hn : n = a <;> simp [update, hn]
    simpa only [hh] using hd (e a)
  · intro a b c
    simp only [rho7]
    rw [sat_wim, sat_weq, sat_wim, sat_weq, sat_weq]
    intro h1 h2; rw [← h1, ← h2]
  · intro a b c u
    simp only [rho8]
    simp only [sat_wim]
    intro h1 h2 _
    exact Classical.byContradiction fun hnc => hnc (h2 (h1 fun hc => absurd hc hnc))

/-- Every derivable code decodes to a valid formula of the bundle theory. -/
theorem c254_sound {D : Type u} (mem : D → D → Prop) (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → D, Tarski.Sat mem e (dec (bundle a b c))) :
    ∀ {n : Nat}, C254 n → ∀ e : Nat → D, Tarski.Sat mem e (dec n) := by
  intro n hn
  induction hn with
  | truth => exact fun e => sat_T0 mem e
  | mp _ _ ih1 ih2 => exact fun e => (sat_wim mem e _ _).mp (ih2 e) (ih1 e)
  | gen a _ ih => exact fun e => (sat_wal mem e a _).mpr fun d => ih _
  | r1 a b => exact fun e => (rows_valid mem hirr e).1 a b
  | r2 a b c => exact fun e => (rows_valid mem hirr e).2.1 a b c
  | r3 a b c => exact fun e => (rows_valid mem hirr e).2.2.1 a b c
  | r4 a b c => exact fun e => (rows_valid mem hirr e).2.2.2.1 a b c
  | r5 a b c => exact fun e => (rows_valid mem hirr e).2.2.2.2.1 a b c
  | r6 a b => exact fun e => (rows_valid mem hirr e).2.2.2.2.2.1 a b
  | r7 a b c => exact fun e => (rows_valid mem hirr e).2.2.2.2.2.2.1 a b c
  | r8 a b c u => exact fun e => (rows_valid mem hirr e).2.2.2.2.2.2.2 a b c u
  | bundle a b c h1 h2 => exact hB a b c h1 h2

/-- If the code 1 is derivable, the decoded bundle theory has no irreflexive model. -/
theorem no_model_of_c254_one (h : C254 F) {D : Type u} (mem : D → D → Prop)
    (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → D, Tarski.Sat mem e (dec (bundle a b c)))
    (e : Nat → D) : False :=
  sat_F mem hirr e (c254_sound mem hirr hB h e)

/-! ## Encoding and completeness -/

/-- Encoding of named formulas; genuine falsity becomes the code `F`. -/
def enc : NF → Nat
  | rel i j => wel i j
  | NF.eq i j => weq i j
  | NF.bot => F
  | imp a b => wim (enc a) (enc b)
  | all i a => wal i (enc a)

/-- The code calculus is an implicational system for `wim`. -/
theorem implicational : Lukasiewicz.Implicational wim C254 where
  mp := fun h1 h2 => C254.mp h2 h1
  rho8 := fun c u a b => C254.r8 a b c u

theorem c254_k (a b : Nat) : C254 (wim a (wim b a)) := Lukasiewicz.k implicational a b
theorem c254_s (a b c : Nat) : C254 (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  Lukasiewicz.s implicational a b c

theorem c254_efq (a : Nat) : C254 (wim F a) := by
  -- F → ∃0 ∀0 a by K, then rho6.
  have h1 : C254 (wim F (wex 0 (wal 0 a))) := c254_k F (wal 0 (wn (wal 0 a)))
  have h2 : C254 (wim F (wim (wex 0 (wal 0 a)) a)) := C254.mp (C254.r6 0 a) (c254_k _ F)
  exact C254.mp h1 (C254.mp h2 (c254_s F (wex 0 (wal 0 a)) a))

theorem c254_classical : Kalmar.Classical wim F C254 where
  mp := fun h1 h2 => C254.mp h2 h1
  k := c254_k
  s := c254_s
  peirce := Lukasiewicz.peirce implicational
  efq := c254_efq

/-- Conjunction elimination at the level of codes. -/
theorem wa_left {a b : Nat} (h : C254 (wa a b)) : C254 a := by
  let f : Kalmar.PF := .imp (.imp (.imp (.var 0) (.imp (.var 1) .bot)) .bot) (.var 0)
  have ht : Kalmar.PF.Tautology f := by
    intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [f, Kalmar.PF.truth, h0, h1]
  have := Kalmar.tautology_complete c254_classical f 2 (by simp [f, Kalmar.PF.Bounded])
    ht (fun n => if n = 0 then a else b)
  exact C254.mp h (by simpa [f, Kalmar.PF.eval, wa, wn] using this)

theorem wa_right {a b : Nat} (h : C254 (wa a b)) : C254 b := by
  let f : Kalmar.PF := .imp (.imp (.imp (.var 0) (.imp (.var 1) .bot)) .bot) (.var 1)
  have ht : Kalmar.PF.Tautology f := by
    intro v
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [f, Kalmar.PF.truth, h0, h1]
  have := Kalmar.tautology_complete c254_classical f 2 (by simp [f, Kalmar.PF.Bounded])
    ht (fun n => if n = 0 then a else b)
  exact C254.mp h (by simpa [f, Kalmar.PF.eval, wa, wn] using this)

/-- Gated atomic vacuity, projected out of the bundle. -/
theorem vac_rel (a b c : Nat) (h1 : c ≠ a) (h2 : c ≠ b) :
    C254 (wim (wel a b) (wal c (wel a b))) :=
  wa_left (wa_right (C254.bundle a b c h1 h2))

theorem vac_eq (a b c : Nat) (h1 : c ≠ a) (h2 : c ≠ b) :
    C254 (wim (weq a b) (wal c (weq a b))) :=
  wa_right (wa_right (C254.bundle a b c h1 h2))

/-- Every derivation of the relative-falsity calculus is a code derivation. -/
theorem c254_of_thmG {Ax : NF → Prop} (hAx : ∀ f, Ax f → C254 (enc f)) {f : NF}
    (h : ThmG (rel 0 0) Ax f) : C254 (enc f) := by
  induction h with
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => exact C254.mp ih2 ih1
  | gen i _ ih => exact C254.gen i ih
  | rho8 c u a b => exact C254.r8 (enc a) (enc b) (enc c) (enc u)
  | rho2 i b c => exact C254.r2 i (enc b) (enc c)
  | rho4 i j c => exact C254.r4 i j (enc c)
  | rho6 i b =>
      simp only [enc, NF.exF, wel_zero_zero]
      exact C254.r6 i (enc b)
  | rho1 i j =>
      simp only [enc, NF.exF, wel_zero_zero]
      exact C254.r1 i j
  | rho7 a b c => exact C254.r7 a b c
  | rho5 a b c => exact C254.r5 a b c
  | rho3 a b c => exact C254.r3 a b c
  | vacRel a b c h1 h2 => exact vac_rel a b c h1 h2
  | vacEq a b c h1 h2 => exact vac_eq a b c h1 h2

/-- The bundle formulas that are literal encodings of named formulas. -/
def EncBundle (f : NF) : Prop :=
  BotFree f ∧ ∃ a b c, c ≠ a ∧ c ≠ b ∧ enc f = bundle a b c

/-- Historical correction: without a valuation or a nonempty-domain premise,
the former no-model hypothesis was impossible, since the empty structure
satisfies every universally quantified bundle vacuously. This theorem
preserves that counterexample; it is not a consistency claim. -/
theorem empty_domain_counterexample :
    ¬ (∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) → False) :=
  fun h => h Empty (fun _ _ => False) (fun x => Empty.elim x) (fun _ _ e => Empty.elim (e 0))

/-- Completeness: if the encodable bundles have no irreflexive model with
a valuation (equivalently, with a nonempty domain), falsity is derivable.
This does not identify encodable bundles with all decoded bundles. -/
theorem c254_complete
    (hnone : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) →
      (Nat → D) → False) :
    C254 F := by
  have hT : ThmG (rel 0 0) EncBundle (rel 0 0) :=
    alias_complete (f := rel 0 0) (fun f hf => hf.1) trivial
      fun D mem hirr hAx e => (hnone D mem hirr hAx e).elim
  have := c254_of_thmG (fun f ⟨_, a, b, c, h1, h2, he⟩ => he ▸ C254.bundle a b c h1 h2) hT
  simpa [enc, wel_zero_zero] using this

end SetTheory.BusyBeaver.ZFC.Code254
