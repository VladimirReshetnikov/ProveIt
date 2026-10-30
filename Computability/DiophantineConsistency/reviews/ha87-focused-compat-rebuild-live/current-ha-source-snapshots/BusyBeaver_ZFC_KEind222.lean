import BusyBeaver.ZFC.KThmK
import BusyBeaver.ZFC.KEqCodes222

/-!
Completeness of the 222/221 code calculus, through the equality interpretation.

Port of `k225-formal/rocq224/src/L224E.v`. `Eind x y` says that `x` and `y` have the same
members and belong to the same sets (auxiliary bound name `aux x y = x + y + 1`), and `th`
replaces every equality atom by `Eind`. Each rule of the Tarski calculus `Thm` interprets in
`ThmK`, which has equality vacuity only at the helper binder (`thm_th`); the five equality rows
become the lemmas `Eind_ex`, `Eind_euclid`, `Eind_el_l`, `Eind_el_r`, `Eind_vac`. Every rule
of `ThmK` is a derivation in the code calculus `C222` (`c222_of_thmK`). With Tarski's
completeness theorem this gives `c222_complete`: if a set of named formulas whose interpreted
codes are derivable has no irreflexive model, the code 1 is derivable.
-/

namespace SetTheory.BusyBeaver.ZFC.KEind222

open SetTheory.BusyBeaver.ZFC.Tarski (NF Thm rn rv complete h0 h1 h2 ded1 ded2 syl dne all_mono ex_mono)
open SetTheory.BusyBeaver.ZFC.Tarski.NF Kalmar SetTheory.BusyBeaver.ZFC.KThmK

/-! ## The interpretation -/

def wa (a b : NF) : NF := neg (imp a (neg b))
def biff (a b : NF) : NF := wa (imp a b) (imp b a)
def Bin (v x y : Nat) : NF := biff (rel v x) (rel v y)
def Bout (v x y : Nat) : NF := biff (rel x v) (rel y v)
def Ev (v x y : Nat) : NF := wa (all v (Bin v x y)) (all v (Bout v x y))
def aux (x y : Nat) : Nat := x + y + 1
def Eind (x y : Nat) : NF := Ev (aux x y) x y

def th : NF → NF
  | rel i j => rel i j
  | NF.eq i j => Eind i j
  | NF.bot => NF.bot
  | imp a b => imp (th a) (th b)
  | all i a => all i (th a)

variable {Ax : NF → Prop}

/-! ## Conjunction -/

theorem and_intro (A B : NF) : ThmK Ax (imp A (imp B (wa A B))) := by
  apply ded2 classical
  apply deduction classical
  -- [A → ¬B, B, A] ⊢ ⊥
  exact .mp (.mp h0 h2) h1

theorem and_l (A B : NF) : ThmK Ax (imp (wa A B) A) := by
  apply syl classical _ (dne classical A)
  apply ded1 classical
  apply deduction classical
  -- [¬A, wa A B] ⊢ ⊥
  have hn : Der NF.imp (ThmK Ax) [neg A, wa A B] (imp A (neg B)) :=
    deduction classical (.mp (.ax (ex_falso (neg B))) (.mp h1 h0))
  exact .mp h1 hn

theorem and_r (A B : NF) : ThmK Ax (imp (wa A B) B) := by
  apply syl classical _ (dne classical B)
  apply ded1 classical
  apply deduction classical
  have hn : Der NF.imp (ThmK Ax) [neg B, wa A B] (imp A (neg B)) := deduction classical h1
  exact .mp h1 hn

/-! ## Syntax facts -/

theorem qf_bin (v x y : Nat) : QF (Bin v x y) := by simp [Bin, biff, wa, neg, QF]
theorem qf_bout (v x y : Nat) : QF (Bout v x y) := by simp [Bout, biff, wa, neg, QF]
theorem ef_bin (v x y : Nat) : EqFree (Bin v x y) := by simp [Bin, biff, wa, neg, EqFree]
theorem ef_bout (v x y : Nat) : EqFree (Bout v x y) := by simp [Bout, biff, wa, neg, EqFree]
theorem ef_ev (v x y : Nat) : EqFree (Ev v x y) := by
  simp [Ev, wa, neg, EqFree, Bin, Bout, biff]

theorem rn_bin {v w x y : Nat} (hx : x ≠ v) (hy : y ≠ v) : rn v w (Bin v x y) = Bin w x y := by
  simp [Bin, biff, wa, neg, rn, rv, hx, hy]
theorem rn_bout {v w x y : Nat} (hx : x ≠ v) (hy : y ≠ v) : rn v w (Bout v x y) = Bout w x y := by
  simp [Bout, biff, wa, neg, rn, rv, hx, hy]

theorem occ_bin {n v x y : Nat} (hv : n ≠ v) (hx : n ≠ x) (hy : n ≠ y) : ¬ Occurs n (Bin v x y) := by
  simp [Bin, biff, wa, neg, Occurs]; omega
theorem occ_bout {n v x y : Nat} (hv : n ≠ v) (hx : n ≠ x) (hy : n ≠ y) : ¬ Occurs n (Bout v x y) := by
  simp [Bout, biff, wa, neg, Occurs]; omega
theorem occ_ev {n v x y : Nat} (hv : n ≠ v) (hx : n ≠ x) (hy : n ≠ y) : ¬ Occurs n (Ev v x y) := by
  simp [Ev, Bin, Bout, biff, wa, neg, Occurs]; omega

/-! ## Renaming the auxiliary label -/

theorem all_bin_alpha {v w x y : Nat} (hx : x ≠ v) (hy : y ≠ v) (hwx : w ≠ x) (hwy : w ≠ y) :
    ThmK Ax (imp (all v (Bin v x y)) (all w (Bin w x y))) := by
  by_cases hvw : w = v
  · subst hvw; exact classical.mp (classical.mp (classical.s _ _ _) (classical.k _ _))
      (classical.k _ (all w (Bin w x y)))
  · have h := alpha_fwd (Ax := Ax) hvw (qf_bin v x y) (ef_bin v x y)
      (occ_bin hvw hwx hwy)
    rwa [rn_bin hx hy] at h

theorem all_bout_alpha {v w x y : Nat} (hx : x ≠ v) (hy : y ≠ v) (hwx : w ≠ x) (hwy : w ≠ y) :
    ThmK Ax (imp (all v (Bout v x y)) (all w (Bout w x y))) := by
  by_cases hvw : w = v
  · subst hvw; exact classical.mp (classical.mp (classical.s _ _ _) (classical.k _ _))
      (classical.k _ (all w (Bout w x y)))
  · have h := alpha_fwd (Ax := Ax) hvw (qf_bout v x y) (ef_bout v x y)
      (occ_bout hvw hwx hwy)
    rwa [rn_bout hx hy] at h

/-- `Ev v x y → Ev w x y` for labels outside `{x, y}`. -/
theorem ev_alpha {v w x y : Nat} (hx : x ≠ v) (hy : y ≠ v) (hwx : w ≠ x) (hwy : w ≠ y) :
    ThmK Ax (imp (Ev v x y) (Ev w x y)) := by
  apply ded1 classical
  have hin : Der NF.imp (ThmK Ax) [Ev v x y] (all w (Bin w x y)) :=
    .mp (.ax (all_bin_alpha hx hy hwx hwy)) (.mp (.ax (and_l _ _)) h0)
  have hout : Der NF.imp (ThmK Ax) [Ev v x y] (all w (Bout w x y)) :=
    .mp (.ax (all_bout_alpha hx hy hwx hwy)) (.mp (.ax (and_r _ _)) h0)
  exact .mp (.mp (.ax (and_intro _ _)) hin) hout

theorem aux_ne_l (x y : Nat) : x ≠ aux x y := by simp [aux]; omega
theorem aux_ne_r (x y : Nat) : y ≠ aux x y := by simp [aux]; omega

theorem eind_to {w x y : Nat} (hwx : w ≠ x) (hwy : w ≠ y) : ThmK Ax (imp (Eind x y) (Ev w x y)) :=
  ev_alpha (aux_ne_l x y) (aux_ne_r x y) hwx hwy

theorem eind_of {w x y : Nat} (hwx : w ≠ x) (hwy : w ≠ y) : ThmK Ax (imp (Ev w x y) (Eind x y)) :=
  ev_alpha (Ne.symm hwx) (Ne.symm hwy) (Ne.symm (aux_ne_l x y)) (Ne.symm (aux_ne_r x y))

/-! ## Specialization of the indiscernibility clauses -/

theorem bin_spec {v x y c : Nat} (hcv : c ≠ v) (hx : x ≠ v) (hy : y ≠ v) :
    ThmK Ax (imp (all v (Bin v x y)) (biff (rel c x) (rel c y))) := by
  have h := spec (Ax := Ax) hcv (qf_bin v x y) (ef_bin v x y)
  have e : rn v c (Bin v x y) = biff (rel c x) (rel c y) := by
    simp [Bin, biff, wa, neg, rn, rv, hx, hy]
  rwa [e] at h

theorem bout_spec {v x y c : Nat} (hcv : c ≠ v) (hx : x ≠ v) (hy : y ≠ v) :
    ThmK Ax (imp (all v (Bout v x y)) (biff (rel x c) (rel y c))) := by
  have h := spec (Ax := Ax) hcv (qf_bout v x y) (ef_bout v x y)
  have e : rn v c (Bout v x y) = biff (rel x c) (rel y c) := by
    simp [Bout, biff, wa, neg, rn, rv, hx, hy]
  rwa [e] at h

/-- A label different from three given ones. -/
def fresh3 (a b c : Nat) : Nat := a + b + c + 1

theorem fresh3_ne (a b c : Nat) : fresh3 a b c ≠ a ∧ fresh3 a b c ≠ b ∧ fresh3 a b c ≠ c := by
  simp [fresh3]; omega

/-- th(rho3): `Eind a b → (c ∈ a → c ∈ b)`. -/
theorem Eind_el_r (a b c : Nat) : ThmK Ax (imp (Eind a b) (imp (rel c a) (rel c b))) := by
  obtain ⟨h1, h2, h3⟩ := fresh3_ne a b c
  have t := eind_to (Ax := Ax) h1 h2
  have s := bin_spec (Ax := Ax) (v := fresh3 a b c) (x := a) (y := b) (c := c) (Ne.symm h3)
    (Ne.symm h1) (Ne.symm h2)
  apply ded1 classical
  have hev : Der NF.imp (ThmK Ax) [Eind a b] (Ev (fresh3 a b c) a b) := .mp (.ax t) h0
  have hb : Der NF.imp (ThmK Ax) [Eind a b] (biff (rel c a) (rel c b)) :=
    .mp (.ax s) (.mp (.ax (and_l _ _)) hev)
  exact .mp (.ax (and_l _ _)) hb

/-- th(rho5): `Eind c a → (c ∈ b → a ∈ b)`. -/
theorem Eind_el_l (a b c : Nat) : ThmK Ax (imp (Eind c a) (imp (rel c b) (rel a b))) := by
  obtain ⟨h1, h2, h3⟩ := fresh3_ne c a b
  have t := eind_to (Ax := Ax) h1 h2
  have s := bout_spec (Ax := Ax) (v := fresh3 c a b) (x := c) (y := a) (c := b) (Ne.symm h3)
    (Ne.symm h1) (Ne.symm h2)
  apply ded1 classical
  have hev : Der NF.imp (ThmK Ax) [Eind c a] (Ev (fresh3 c a b) c a) := .mp (.ax t) h0
  have hb : Der NF.imp (ThmK Ax) [Eind c a] (biff (rel c b) (rel a b)) :=
    .mp (.ax s) (.mp (.ax (and_r _ _)) hev)
  exact .mp (.ax (and_l _ _)) hb

/-! ## Euclid and existence -/

/-- `(p ↔ q) → (p ↔ r) → (q ↔ r)`, propositionally. -/
theorem biff_euclid (p q r : NF) :
    ThmK Ax (imp (biff p q) (imp (biff p r) (biff q r))) := by
  apply ded2 classical
  have pq : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp p q) := .mp (.ax (and_l _ _)) h1
  have qp : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp q p) := .mp (.ax (and_r _ _)) h1
  have pr : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp p r) := .mp (.ax (and_l _ _)) h0
  have rp : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp r p) := .mp (.ax (and_r _ _)) h0
  have qr : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp q r) :=
    deduction classical (.mp pr.weaken (.mp qp.weaken h0))
  have rq : Der NF.imp (ThmK Ax) [biff p r, biff p q] (imp r q) :=
    deduction classical (.mp pq.weaken (.mp rp.weaken h0))
  exact .mp (.mp (.ax (and_intro _ _)) qr) rq

/-- Distribution of a two-premise implication under `∀`. -/
theorem all_mono2 (i : Nat) {a b c : NF} (h : ThmK Ax (imp a (imp b c))) :
    ThmK Ax (imp (all i a) (imp (all i b) (all i c))) :=
  syl classical (all_mono classical i h) (.rho2 i b c)

theorem ev_euclid (v x y z : Nat) : ThmK Ax (imp (Ev v x y) (imp (Ev v x z) (Ev v y z))) := by
  have hin := all_mono2 (Ax := Ax) v (biff_euclid (rel v x) (rel v y) (rel v z))
  have hout := all_mono2 (Ax := Ax) v (biff_euclid (rel x v) (rel y v) (rel z v))
  apply ded2 classical
  have i1 : Der NF.imp (ThmK Ax) [Ev v x z, Ev v x y] (all v (Bin v y z)) :=
    .mp (.mp (.ax hin) (.mp (.ax (and_l _ _)) h1)) (.mp (.ax (and_l _ _)) h0)
  have o1 : Der NF.imp (ThmK Ax) [Ev v x z, Ev v x y] (all v (Bout v y z)) :=
    .mp (.mp (.ax hout) (.mp (.ax (and_r _ _)) h1)) (.mp (.ax (and_r _ _)) h0)
  exact .mp (.mp (.ax (and_intro _ _)) i1) o1

/-- th(rho7): `Eind c a → (Eind c b → Eind a b)`. -/
theorem Eind_euclid (a b c : Nat) : ThmK Ax (imp (Eind c a) (imp (Eind c b) (Eind a b))) := by
  let w := fresh3 a b c
  obtain ⟨ha, hb, hc⟩ := fresh3_ne a b c
  have e := ev_euclid (Ax := Ax) w c a b
  apply ded2 classical
  have x1 : Der NF.imp (ThmK Ax) [Eind c b, Eind c a] (Ev w c a) := .mp (.ax (eind_to hc ha)) h1
  have x2 : Der NF.imp (ThmK Ax) [Eind c b, Eind c a] (Ev w c b) := .mp (.ax (eind_to hc hb)) h0
  exact .mp (.ax (eind_of ha hb)) (.mp (.mp (.ax e) x1) x2)

/-- `x = y → Eind x y`, through the helper binder. -/
theorem Eq_Eind (x y : Nat) : ThmK Ax (imp (NF.eq x y) (Eind x y)) := by
  let w := Code254.wel x y
  have hwx : w ≠ x := Ne.symm (Nat.ne_of_lt (KCode222.lt_wel_left x y))
  have hwy : w ≠ y := Ne.symm (Nat.ne_of_lt (KCode222.lt_wel_right x y))
  -- x = y → (w ∈ x ↔ w ∈ y) and → (x ∈ w ↔ y ∈ w)
  have bi : ThmK Ax (imp (NF.eq x y) (Bin w x y)) := by
    apply ded1 classical
    have f1 : Der NF.imp (ThmK Ax) [NF.eq x y] (imp (rel w x) (rel w y)) := .mp (.ax (.rho3 x y w)) h0
    have f2 : Der NF.imp (ThmK Ax) [NF.eq x y] (imp (rel w y) (rel w x)) :=
      .mp (.ax (.rho3 y x w)) (.mp (.ax (eq_symm x y)) h0)
    exact .mp (.mp (.ax (and_intro _ _)) f1) f2
  have bo : ThmK Ax (imp (NF.eq x y) (Bout w x y)) := by
    apply ded1 classical
    have f1 : Der NF.imp (ThmK Ax) [NF.eq x y] (imp (rel x w) (rel y w)) := .mp (.ax (.rho5 y w x)) h0
    have f2 : Der NF.imp (ThmK Ax) [NF.eq x y] (imp (rel y w) (rel x w)) :=
      .mp (.ax (.rho5 x w y)) (.mp (.ax (eq_symm x y)) h0)
    exact .mp (.mp (.ax (and_intro _ _)) f1) f2
  apply ded1 classical
  have hall : Der NF.imp (ThmK Ax) [NF.eq x y] (all w (NF.eq x y)) := .mp (.ax (.helper x y)) h0
  have i1 : Der NF.imp (ThmK Ax) [NF.eq x y] (all w (Bin w x y)) := .mp (.ax (all_mono classical w bi)) hall
  have o1 : Der NF.imp (ThmK Ax) [NF.eq x y] (all w (Bout w x y)) := .mp (.ax (all_mono classical w bo)) hall
  exact .mp (.ax (eind_of hwx hwy)) (.mp (.mp (.ax (and_intro _ _)) i1) o1)

/-- th(rho1): `∃i Eind(i, j)`. -/
theorem Eind_ex (i j : Nat) : ThmK Ax (ex i (Eind i j)) :=
  ThmK.mp (ex_mono classical i (Eq_Eind i j)) (.rho1 i j)

/-- th(vacEq): `Eind a b → ∀c Eind a b` for `c ≠ a, b`. -/
theorem Eind_vac (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    ThmK Ax (imp (Eind a b) (all c (Eind a b))) := by
  by_cases hc : c = aux a b
  · let w := fresh3 a b c
    obtain ⟨ha, hb, hwc⟩ := fresh3_ne a b c
    have v : ThmK Ax (imp (Ev w a b) (all c (Ev w a b))) :=
      vac_of_not_occurs c _ (ef_ev w a b) (occ_ev (Ne.symm hwc) hca hcb)
    exact syl classical (syl classical (eind_to ha hb) v) (all_mono classical c (eind_of ha hb))
  · exact vac_of_not_occurs c _ (ef_ev _ a b) (occ_ev hc hca hcb)

/-! ## The interpretation of derivations -/

theorem thm_th {f : NF} (h : Thm Ax f) : ThmK (fun g => ∃ a, Ax a ∧ th a = g) (th f) := by
  induction h with
  | ax h => exact .ax ⟨_, h, rfl⟩
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen i _ ih => exact .gen i ih
  | rho8 c u a b => exact .rho8 (th c) (th u) (th a) (th b)
  | rho2 i b c => exact .rho2 i (th b) (th c)
  | rho4 i j c => exact .rho4 i j (th c)
  | rho6 i b => exact .rho6 i (th b)
  | rho1 i j => exact Eind_ex i j
  | rho7 a b c => exact Eind_euclid a b c
  | rho5 a b c => exact Eind_el_l a b c
  | rho3 a b c => exact Eind_el_r a b c
  | vacRel a b c h1 h2 => exact .vacRel a b c h1 h2
  | vacEq a b c h1 h2 => exact Eind_vac a b c h1 h2

/-! ## Into the code calculus -/

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222
  SetTheory.BusyBeaver.ZFC.KEqCodes222

theorem c222_of_thmK {T : NF → Prop} (hT : ∀ f, T f → C222 (enc f)) {f : NF}
    (h : ThmK T f) : C222 (enc f) := by
  induction h with
  | ax h => exact hT _ h
  | mp _ _ ih1 ih2 => exact C222.mp ih2 ih1
  | gen i _ ih => exact C222.gen i ih
  | rho8 c u a b => exact C222.r8 (enc a) (enc b) (enc c) (enc u)
  | rho2 i b c => exact C222.r2 i (enc b) (enc c)
  | rho4 i j c => exact C222.r4 i j (enc c)
  | rho6 i b => exact C222.r6 i (enc b)
  | rho1 i j => exact C222.r1 i j
  | rho7 a b c => exact rho7_222 a b c
  | rho5 a b c => exact C222.r5 a b c
  | rho3 a b c => exact C222.r3 a b c
  | vacRel a b c h1 h2 => exact vrel_of_bundle a b c h1 h2
  | helper a b => exact helper222 a b

/-- Irreflexivity, as a named sentence. -/
def irNF : NF := all 0 (neg (rel 0 0))

/-- **Completeness.** If the named formulas of `T`, whose interpreted codes are derivable, have
no irreflexive model with a valuation, then the code 1 is derivable. -/
theorem c222_complete (T : NF → Prop) (hT : ∀ f, T f → C222 (enc (th f)))
    (hnone : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, T f → ∀ e : Nat → D, Tarski.Sat mem e f) → (Nat → D) → False) :
    C222 F := by
  let Ax : NF → Prop := fun f => T f ∨ f = irNF
  have hbot : Thm Ax NF.bot := by
    apply complete
    intro D mem hAx e
    exact (hnone D mem (fun x => hAx irNF (Or.inr rfl) e x) (fun f hf => hAx f (Or.inl hf)) e).elim
  have hK := thm_th hbot
  have := c222_of_thmK (T := fun g => ∃ a, Ax a ∧ th a = g) (by
    rintro g ⟨a, ha | rfl, rfl⟩
    · exact hT a ha
    · show C222 (wal 0 (wim (wel 0 0) F))
      rw [wel_zero_zero]
      exact C222.gen 0 (self_imp c222_classical F)) hK
  simpa [th, enc] using this

#print axioms c222_complete

end SetTheory.BusyBeaver.ZFC.KEind222
