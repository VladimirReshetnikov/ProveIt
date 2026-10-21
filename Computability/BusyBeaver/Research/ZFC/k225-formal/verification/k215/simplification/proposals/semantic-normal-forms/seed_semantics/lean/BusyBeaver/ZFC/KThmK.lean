import BusyBeaver.ZFC.TarskiLeibniz
import BusyBeaver.ZFC.Lukasiewicz
import BusyBeaver.ZFC.Code254

/-!
`ThmK`: the named calculus that the 222/221 code calculus simulates.

It is the Tarski calculus `Thm` with one change: equality vacuity is available only at the
helper binder, `Eq(a,b) → ∀_{wel a b} Eq(a,b)` (the merged row G gives exactly this, and rho7;
`KEqCodes222`). Membership vacuity stays at every fresh binder.

The derived rules of `TarskiDerived` and `TarskiLeibniz` are re-proved here with the same
proofs, except where `Thm` used equality vacuity at an arbitrary binder:

* `vac_of_not_occurs` and `ex_elim` are stated for equality-free formulas;
* Leibniz's law, specialization and alpha-renaming are stated for quantifier-free,
  respectively equality-free, bodies;
* reflexivity goes through the helper binder `wel x x`.

These restricted forms are all that the equality interpretation (`KEind222`) needs.
-/

namespace SetTheory.BusyBeaver.ZFC.KThmK

open SetTheory.BusyBeaver.ZFC.Tarski NF Kalmar

inductive ThmK (Ax : NF → Prop) : NF → Prop
  | ax {a : NF} : Ax a → ThmK Ax a
  | mp {a b : NF} : ThmK Ax (imp a b) → ThmK Ax a → ThmK Ax b
  | gen (i : Nat) {a : NF} : ThmK Ax a → ThmK Ax (all i a)
  | rho8 (c u a b : NF) : ThmK Ax (luk c u a b)
  | rho2 (i : Nat) (b c : NF) : ThmK Ax (imp (all i (imp b c)) (imp (all i b) (all i c)))
  | rho4 (i j : Nat) (c : NF) : ThmK Ax (imp (all i (all j c)) (all j (all i c)))
  | rho6 (i : Nat) (b : NF) : ThmK Ax (imp (ex i (all i b)) b)
  | rho1 (i j : Nat) : ThmK Ax (ex i (NF.eq i j))
  | rho7 (a b c : Nat) : ThmK Ax (imp (NF.eq c a) (imp (NF.eq c b) (NF.eq a b)))
  | rho5 (a b c : Nat) : ThmK Ax (imp (NF.eq c a) (imp (rel c b) (rel a b)))
  | rho3 (a b c : Nat) : ThmK Ax (imp (NF.eq a b) (imp (rel c a) (rel c b)))
  | vacRel (a b c : Nat) : c ≠ a → c ≠ b → ThmK Ax (imp (rel a b) (all c (rel a b)))
  | helper (a b : Nat) : ThmK Ax (imp (NF.eq a b) (all (Code254.wel a b) (NF.eq a b)))

/-! ## Syntactic classes -/

def EqFree : NF → Prop
  | rel _ _ => True
  | NF.eq _ _ => False
  | NF.bot => True
  | imp a b => EqFree a ∧ EqFree b
  | all _ a => EqFree a

def QF : NF → Prop
  | all _ _ => False
  | imp a b => QF a ∧ QF b
  | _ => True

theorem eqFree_rn (x y : Nat) : ∀ f : NF, EqFree f → EqFree (rn x y f)
  | rel _ _, _ => trivial
  | NF.eq _ _, h => h.elim
  | NF.bot, _ => trivial
  | imp a b, h => ⟨eqFree_rn x y a h.1, eqFree_rn x y b h.2⟩
  | all i a, h => by
      by_cases hi : i = x
      · simp only [rn, hi, if_true]; exact h
      · simp only [rn, hi, if_false]; exact eqFree_rn x y a h

variable {Ax : NF → Prop}

/-! ## Classical basis -/

theorem implicational : Lukasiewicz.Implicational NF.imp (ThmK Ax) where
  mp := ThmK.mp
  rho8 := ThmK.rho8

theorem ex_falso (a : NF) : ThmK Ax (imp bot a) := by
  let x := all 0 (neg (all 0 a))
  let e := ex 0 (all 0 a)
  have hk := Lukasiewicz.k (implicational (Ax := Ax))
  have hs := Lukasiewicz.s (implicational (Ax := Ax))
  have hbe : ThmK Ax (imp bot e) := hk bot x
  have hbea : ThmK Ax (imp bot (imp e a)) :=
    .mp (hk (imp e a) bot) (.rho6 0 a)
  exact .mp (.mp (hs bot e a) hbea) hbe

theorem classical : Classical NF.imp NF.bot (ThmK Ax) where
  mp := ThmK.mp
  k := Lukasiewicz.k implicational
  s := Lukasiewicz.s implicational
  peirce := Lukasiewicz.peirce implicational
  efq := ex_falso

/-! ## Propositional layer (as `TarskiDerived`) -/

theorem h0 {G : List NF} {a : NF} : Der NF.imp (ThmK Ax) (a :: G) a := .hyp (List.mem_cons_self ..)
theorem h1 {G : List NF} {a b : NF} : Der NF.imp (ThmK Ax) (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem h2 {G : List NF} {a b c : NF} : Der NF.imp (ThmK Ax) (c :: b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem thm_of_der0 {a : NF} (d : Der NF.imp (ThmK Ax) [] a) : ThmK Ax a :=
  d.sound classical (fun _ hx => absurd hx List.not_mem_nil)

theorem ded1 {a c : NF} (d : Der NF.imp (ThmK Ax) [a] c) : ThmK Ax (imp a c) :=
  thm_of_der0 (deduction classical d)

theorem ded2 {a b c : NF} (d : Der NF.imp (ThmK Ax) [b, a] c) : ThmK Ax (imp a (imp b c)) :=
  thm_of_der0 (deduction classical (deduction classical d))

theorem ded3 {a b c d : NF} (dd : Der NF.imp (ThmK Ax) [c, b, a] d) :
    ThmK Ax (imp a (imp b (imp c d))) :=
  thm_of_der0 (deduction classical (deduction classical (deduction classical dd)))

theorem syl {a b c : NF} (hab : ThmK Ax (imp a b)) (hbc : ThmK Ax (imp b c)) :
    ThmK Ax (imp a c) :=
  ded1 (.mp (.ax hbc) (.mp (.ax hab) h0))

theorem contra_thm (a b : NF) : ThmK Ax (imp (imp a b) (imp (neg b) (neg a))) :=
  ded3 (.mp h1 (.mp h2 h0))

theorem contra {a b : NF} (h : ThmK Ax (imp a b)) : ThmK Ax (imp (neg b) (neg a)) :=
  ThmK.mp (contra_thm a b) h

theorem dne (a : NF) : ThmK Ax (imp (neg (neg a)) a) := by
  apply ded1
  have inner : Der NF.imp (ThmK Ax) [neg (neg a)] (imp (imp a NF.bot) a) :=
    deduction classical (.mp (.ax (ex_falso a)) (.mp h1 h0))
  exact .mp (.ax (classical.peirce a NF.bot)) inner

theorem dni (a : NF) : ThmK Ax (imp a (neg (neg a))) :=
  ded2 (.mp h0 h1)

theorem imp_cases (a b c : NF) :
    ThmK Ax (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  apply ded3
  have inner : Der NF.imp (ThmK Ax) [neg c, imp a b, imp b c, imp (neg a) c] c := by
    have na : Der NF.imp (ThmK Ax) [neg c, imp a b, imp b c, imp (neg a) c] (neg a) :=
      deduction classical (.mp (Der.hyp (a := neg c) (by simp))
        (.mp (Der.hyp (a := imp b c) (by simp)) (.mp (Der.hyp (a := imp a b) (by simp)) h0)))
    exact .mp (Der.hyp (a := imp (neg a) c) (by simp)) na
  exact .mp (.ax (classical.peirce c NF.bot)) (deduction classical inner)

/-! ## Quantifiers -/

theorem all_mono (i : Nat) {a b : NF} (h : ThmK Ax (imp a b)) :
    ThmK Ax (imp (all i a) (all i b)) :=
  ThmK.mp (.rho2 i a b) (.gen i h)

theorem ex_mono (i : Nat) {a b : NF} (h : ThmK Ax (imp a b)) :
    ThmK Ax (imp (ex i a) (ex i b)) :=
  contra (all_mono i (contra h))

theorem ex_elim_of_vac {i : Nat} {a : NF} (h : ThmK Ax (imp a (all i a))) :
    ThmK Ax (imp (ex i a) a) :=
  syl (ex_mono i h) (.rho6 i a)

theorem vac_neg {i : Nat} {a : NF} (h : ThmK Ax (imp a (all i a))) :
    ThmK Ax (imp (neg a) (all i (neg a))) :=
  syl (contra (ex_elim_of_vac h)) (dne (all i (neg a)))

/-- Vacuity for every equality-free formula not containing the label. -/
theorem vac_of_not_occurs (i : Nat) :
    ∀ f : NF, EqFree f → ¬ Occurs i f → ThmK Ax (imp f (all i f))
  | rel a b, _, h => .vacRel a b i (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.eq _ _, hf, _ => hf.elim
  | NF.bot, _, _ => ex_falso _
  | imp a b, hf, h => by
      have ha := vac_of_not_occurs i a hf.1 (fun o => h (Or.inl o))
      have hb := vac_of_not_occurs i b hf.2 (fun o => h (Or.inr o))
      have hna : ThmK Ax (imp (neg a) (all i (imp a b))) :=
        syl (vac_neg ha) (all_mono i (ded2 (.mp (.ax (ex_falso b)) (.mp h1 h0))))
      have hbb : ThmK Ax (imp b (all i (imp a b))) :=
        syl hb (all_mono i (classical.k b a))
      exact ThmK.mp (ThmK.mp (imp_cases a b (all i (imp a b))) hna) hbb
  | all j a, hf, h => by
      have ha := vac_of_not_occurs i a hf (fun o => h (Or.inr o))
      exact syl (all_mono j ha) (.rho4 j i a)

theorem ex_elim (i : Nat) {a : NF} (hf : EqFree a) (h : ¬ Occurs i a) :
    ThmK Ax (imp (ex i a) a) :=
  ex_elim_of_vac (vac_of_not_occurs i a hf h)

/-! ## Equality -/

theorem eq_refl (x : Nat) : ThmK Ax (NF.eq x x) := by
  have h7 : ThmK Ax (imp (NF.eq (Code254.wel x x) x) (NF.eq x x)) := by
    have r : ThmK Ax (imp (NF.eq (Code254.wel x x) x)
        (imp (NF.eq (Code254.wel x x) x) (NF.eq x x))) := .rho7 x x (Code254.wel x x)
    exact ded1 (.mp (.mp (.ax r) h0) h0)
  have hex : ThmK Ax (ex (Code254.wel x x) (NF.eq x x)) :=
    ThmK.mp (ex_mono (Code254.wel x x) h7) (.rho1 (Code254.wel x x) x)
  exact ThmK.mp (ex_elim_of_vac (.helper x x)) hex

theorem eq_symm (x y : Nat) : ThmK Ax (imp (NF.eq x y) (NF.eq y x)) :=
  ded1 (.mp (.mp (.ax (.rho7 y x x)) h0) (.ax (eq_refl x)))

theorem eq_trans (x y z : Nat) : ThmK Ax (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) := by
  apply ded2
  exact .mp (.mp (.ax (.rho7 x z y)) (.mp (.ax (eq_symm x y)) h1)) h0

theorem rel_L (u v j : Nat) : ThmK Ax (imp (NF.eq u v) (imp (rel u j) (rel v j))) := .rho5 v j u
theorem rel_R (u v i : Nat) : ThmK Ax (imp (NF.eq u v) (imp (rel i u) (rel i v))) := .rho3 u v i

/-! ## Leibniz's law for quantifier-free membership formulas -/

theorem atom_subst (P : Nat → Nat → NF)
    (hL : ∀ u v j, ThmK Ax (imp (NF.eq u v) (imp (P u j) (P v j))))
    (hR : ∀ u v i, ThmK Ax (imp (NF.eq u v) (imp (P i u) (P i v))))
    (x y i j : Nat) : ThmK Ax (imp (NF.eq x y) (imp (P i j) (P (rv x y i) (rv x y j)))) := by
  have step1 : ThmK Ax (imp (NF.eq x y) (imp (P i j) (P (rv x y i) j))) := by
    by_cases hi : i = x
    · subst hi; simp only [rv, if_true]; exact hL i y j
    · simp only [rv, hi, if_false]; exact ded2 h0
  have step2 : ThmK Ax (imp (NF.eq x y) (imp (P (rv x y i) j) (P (rv x y i) (rv x y j)))) := by
    by_cases hj : j = x
    · subst hj; simp only [rv, if_true]; exact hR j y _
    · simp only [rv, hj, if_false]; exact ded2 h0
  apply ded2
  exact .mp (.mp (.ax step2) h1) (.mp (.mp (.ax step1) h1) h0)

theorem atom_subst_rev (P : Nat → Nat → NF)
    (hL : ∀ u v j, ThmK Ax (imp (NF.eq u v) (imp (P u j) (P v j))))
    (hR : ∀ u v i, ThmK Ax (imp (NF.eq u v) (imp (P i u) (P i v))))
    (x y i j : Nat) : ThmK Ax (imp (NF.eq x y) (imp (P (rv x y i) (rv x y j)) (P i j))) := by
  have step1 : ThmK Ax (imp (NF.eq y x) (imp (P (rv x y i) (rv x y j)) (P i (rv x y j)))) := by
    by_cases hi : i = x
    · subst hi; simp only [rv, if_true]; exact hL y i _
    · simp only [rv, hi, if_false]; exact ded2 h0
  have step2 : ThmK Ax (imp (NF.eq y x) (imp (P i (rv x y j)) (P i j))) := by
    by_cases hj : j = x
    · subst hj; simp only [rv, if_true]; exact hR y j i
    · simp only [rv, hj, if_false]; exact ded2 h0
  apply ded2
  have hyx : Der NF.imp (ThmK Ax) [P (rv x y i) (rv x y j), NF.eq x y] (NF.eq y x) :=
    .mp (.ax (eq_symm x y)) h1
  exact .mp (.mp (.ax step2) hyx) (.mp (.mp (.ax step1) hyx) h0)

/-- Leibniz's law for quantifier-free, equality-free formulas. -/
theorem leibniz (x y : Nat) :
    ∀ f : NF, QF f → EqFree f →
      ThmK Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
      ThmK Ax (imp (NF.eq x y) (imp (rn x y f) f))
  | rel i j, _, _ =>
      ⟨atom_subst rel rel_L rel_R x y i j, atom_subst_rev rel rel_L rel_R x y i j⟩
  | NF.eq _ _, _, hf => hf.elim
  | NF.bot, _, _ => ⟨ded2 h0, ded2 h0⟩
  | imp a b, hq, hf => by
      have ha := leibniz x y a hq.1 hf.1
      have hb := leibniz x y b hq.2 hf.2
      constructor
      · apply ded3
        have a0 : Der NF.imp (ThmK Ax) [rn x y a, imp a b, NF.eq x y] a :=
          .mp (.mp (.ax ha.2) h2) h0
        exact .mp (.mp (.ax hb.1) h2) (.mp h1 a0)
      · apply ded3
        have a0 : Der NF.imp (ThmK Ax) [a, imp (rn x y a) (rn x y b), NF.eq x y] (rn x y a) :=
          .mp (.mp (.ax ha.1) h2) h0
        exact .mp (.mp (.ax hb.2) h2) (.mp h1 a0)
  | all _ _, hq, _ => hq.elim

theorem all_imp_ex (i : Nat) (a b : NF) :
    ThmK Ax (imp (all i (imp a b)) (imp (ex i a) (ex i b))) := by
  have c1 : ThmK Ax (imp (all i (imp a b)) (all i (imp (neg b) (neg a)))) :=
    all_mono i (contra_thm a b)
  have c2 := ThmK.rho2 (Ax := Ax) i (neg b) (neg a)
  have c3 : ThmK Ax (imp (all i (imp a b)) (imp (all i (neg b)) (all i (neg a)))) := syl c1 c2
  apply ded2
  apply deduction classical
  exact .mp h1 (.mp (.mp (.ax c3) h2) h0)

theorem qf_bound {n : Nat} : ∀ {f : NF}, QF f → ¬ Bound n f
  | rel _ _, _ => id
  | NF.eq _ _, _ => id
  | NF.bot, _ => id
  | imp _ _, h => fun b => b.elim (qf_bound h.1) (qf_bound h.2)
  | all _ _, h => h.elim

/-- Specialization `∀x φ → φ[y/x]` for quantifier-free, equality-free `φ`. -/
theorem spec {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : QF f) (hf : EqFree f) :
    ThmK Ax (imp (all x f) (rn x y f)) := by
  have L := (leibniz (Ax := Ax) x y f hq hf).1
  have shuffle : ThmK Ax (imp f (imp (NF.eq x y) (rn x y f))) :=
    ded2 (.mp (.mp (.ax L) h0) h1)
  have g : ThmK Ax (imp (all x f) (all x (imp (NF.eq x y) (rn x y f)))) := all_mono x shuffle
  have e : ThmK Ax (imp (all x (imp (NF.eq x y) (rn x y f)))
      (imp (ex x (NF.eq x y)) (ex x (rn x y f)))) := all_imp_ex x _ _
  have elim : ThmK Ax (imp (ex x (rn x y f)) (rn x y f)) :=
    ex_elim x (eqFree_rn x y f hf) (not_occurs_rn hxy f (qf_bound hq))
  apply ded1
  exact .mp (.ax elim) (.mp (.mp (.ax e) (.mp (.ax g) h0)) (.ax (.rho1 x y)))

/-- Alpha-renaming of a binder to a fresh label, both directions. -/
theorem alpha_fwd {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : QF f) (hf : EqFree f)
    (hy : ¬ Occurs y f) : ThmK Ax (imp (all x f) (all y (rn x y f))) := by
  have hyo : ¬ Occurs y (all x f) := by
    simp only [Occurs]; intro o; cases o with
    | inl o => exact hxy o
    | inr o => exact hy o
  exact syl (vac_of_not_occurs y _ hf hyo) (all_mono y (spec hxy hq hf))

theorem qf_rn (x y : Nat) : ∀ f : NF, QF f → QF (rn x y f)
  | rel _ _, _ => trivial
  | NF.eq _ _, _ => trivial
  | NF.bot, _ => trivial
  | imp a b, h => ⟨qf_rn x y a h.1, qf_rn x y b h.2⟩
  | all _ _, h => h.elim

theorem alpha_bwd {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : QF f) (hf : EqFree f)
    (hy : ¬ Occurs y f) : ThmK Ax (imp (all y (rn x y f)) (all x f)) := by
  have s : ThmK Ax (imp (all y (rn x y f)) (rn y x (rn x y f))) :=
    spec (Ne.symm hxy) (qf_rn x y f hq) (eqFree_rn x y f hf)
  rw [rn_rn_fresh f hy] at s
  have hxo : ¬ Occurs x (all y (rn x y f)) := by
    simp only [Occurs]; intro o; cases o with
    | inl o => exact hxy o.symm
    | inr o => exact not_occurs_rn hxy f (qf_bound hq) o
  exact syl (vac_of_not_occurs x _ (eqFree_rn x y f hf) hxo) (all_mono x s)

#print axioms spec
#print axioms alpha_bwd

end SetTheory.BusyBeaver.ZFC.KThmK
