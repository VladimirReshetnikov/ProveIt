import BusyBeaver.ZFC.TarskiDerived

/-!
Substitution inside the substitution-free Tarski calculus.

The machine calculus has no substitution operation and no specialization
row `∀x φ → φ[y/x]`. This module shows the rows nevertheless derive:

* `leibniz`: `x = y → (φ ↔ φ[y/x])` for every formula in which neither label
  is rebound, from the three atomic congruence rows `rho3`, `rho5`, `rho7`;
* `spec`: `∀x φ → φ[y/x]` (specialization), using `rho1 : ∃x (x = y)`;
* `spec_self`: `∀x φ → φ` (the T axiom), via a fresh detour label;
* `alpha_fwd`/`alpha_bwd`: renaming a bound label to a fresh one.

`rn x y φ` replaces the free occurrences of `x` by `y`. The side condition
"neither label is bound in `φ`" excludes capture; arbitrary formulas are
brought into that shape by `alpha` in the completeness proof.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF Kalmar

/-! ## Renaming of free occurrences -/

def rv (x y n : Nat) : Nat := if n = x then y else n

/-- Replace the free occurrences of `x` by `y`. -/
def rn (x y : Nat) : NF → NF
  | rel i j => rel (rv x y i) (rv x y j)
  | NF.eq i j => NF.eq (rv x y i) (rv x y j)
  | NF.bot => NF.bot
  | imp a b => imp (rn x y a) (rn x y b)
  | all i a => if i = x then all i a else all i (rn x y a)

/-- The label is used as a binder somewhere. -/
def Bound (n : Nat) : NF → Prop
  | rel _ _ => False
  | NF.eq _ _ => False
  | NF.bot => False
  | imp a b => Bound n a ∨ Bound n b
  | all i a => n = i ∨ Bound n a

theorem bound_rn (x y n : Nat) : ∀ f : NF, Bound n (rn x y f) ↔ Bound n f
  | rel _ _ => Iff.rfl
  | NF.eq _ _ => Iff.rfl
  | NF.bot => Iff.rfl
  | imp a b => by simp only [rn, Bound, bound_rn x y n a, bound_rn x y n b]
  | all i a => by
      by_cases h : i = x
      · simp only [rn, h, if_true]
      · simp only [rn, h, if_false, Bound, bound_rn x y n a]

theorem bound_occurs {n : Nat} : ∀ {f : NF}, Bound n f → Occurs n f
  | imp _ _, h => h.elim (fun h => Or.inl (bound_occurs h)) (fun h => Or.inr (bound_occurs h))
  | all _ _, h => h.elim Or.inl (fun h => Or.inr (bound_occurs h))

/-- After renaming `x` away, `x` no longer occurs (if it was not a binder). -/
theorem not_occurs_rn {x y : Nat} (hxy : y ≠ x) :
    ∀ f : NF, ¬ Bound x f → ¬ Occurs x (rn x y f)
  | rel i j, _ => by
      simp only [rn, Occurs, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.eq i j, _ => by
      simp only [rn, Occurs, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.bot, _ => id
  | imp a b, hb => by
      simp only [rn, Occurs]
      exact fun o => o.elim (not_occurs_rn hxy a fun h' => hb (Or.inl h'))
        (not_occurs_rn hxy b fun h' => hb (Or.inr h'))
  | all i a, hb => by
      have hix : i ≠ x := fun e => hb (Or.inl e.symm)
      simp only [rn, hix, if_false, Occurs]
      exact fun o => o.elim (fun e => hix e.symm) (not_occurs_rn hxy a fun h' => hb (Or.inr h'))

/-- Labels other than `x` and `y` occur after renaming iff they occurred before. -/
theorem occurs_rn_of_ne {x y n : Nat} (hx : n ≠ x) (hy : n ≠ y) :
    ∀ f : NF, Occurs n (rn x y f) ↔ Occurs n f
  | rel i j => by
      simp only [rn, Occurs, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.eq i j => by
      simp only [rn, Occurs, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.bot => Iff.rfl
  | imp a b => by simp only [rn, Occurs, occurs_rn_of_ne hx hy a, occurs_rn_of_ne hx hy b]
  | all i a => by
      by_cases h : i = x
      · simp only [rn, h, if_true]
      · simp only [rn, h, if_false, Occurs, occurs_rn_of_ne hx hy a]

theorem rn_not_occurs {x y : Nat} : ∀ f : NF, ¬ Occurs x f → rn x y f = f
  | rel i j, h => by
      simp only [Occurs] at h
      simp only [rn, rv]
      have hi : i ≠ x := fun e => h (Or.inl e.symm)
      have hj : j ≠ x := fun e => h (Or.inr e.symm)
      simp [hi, hj]
  | NF.eq i j, h => by
      simp only [Occurs] at h
      simp only [rn, rv]
      have hi : i ≠ x := fun e => h (Or.inl e.symm)
      have hj : j ≠ x := fun e => h (Or.inr e.symm)
      simp [hi, hj]
  | NF.bot, _ => rfl
  | imp a b, h => by
      simp only [rn, rn_not_occurs a (fun o => h (Or.inl o)), rn_not_occurs b (fun o => h (Or.inr o))]
  | all i a, h => by
      have hix : i ≠ x := fun e => h (Or.inl e.symm)
      simp only [rn, hix, if_false, rn_not_occurs a (fun o => h (Or.inr o))]

/-- Renaming back through a fresh label is the identity. -/
theorem rn_rn_fresh {x z : Nat} : ∀ f : NF, ¬ Occurs z f → rn z x (rn x z f) = f
  | rel i j, h => by
      simp only [Occurs] at h
      simp only [rn, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.eq i j, h => by
      simp only [Occurs] at h
      simp only [rn, rv]
      by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj] <;> omega
  | NF.bot, _ => rfl
  | imp a b, h => by
      simp only [rn, rn_rn_fresh a (fun o => h (Or.inl o)), rn_rn_fresh b (fun o => h (Or.inr o))]
  | all i a, h => by
      have hiz : z ≠ i := fun e => h (Or.inl e)
      by_cases hix : i = x
      · rw [show rn x z (all i a) = all i a by simp [rn, hix]]
        simp [rn, Ne.symm hiz, rn_not_occurs a (fun o => h (Or.inr o))]
      · simp only [rn, hix, if_false, Ne.symm hiz, rn_rn_fresh a (fun o => h (Or.inr o))]

theorem rn_self (x : Nat) : ∀ f : NF, rn x x f = f
  | rel i j => by simp only [rn, rv]; by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj]
  | NF.eq i j => by simp only [rn, rv]; by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj]
  | NF.bot => rfl
  | imp a b => by simp only [rn, rn_self x a, rn_self x b]
  | all i a => by by_cases h : i = x <;> simp [rn, h, rn_self x a]

/-! ## Leibniz's law -/

variable {Ax : NF → Prop} {T : NF → Prop}

theorem rel_L [R : Rows T] (u v j : Nat) : T (imp (NF.eq u v) (imp (rel u j) (rel v j))) :=
  R.rho5 v j u
theorem rel_R [R : Rows T] (u v i : Nat) : T (imp (NF.eq u v) (imp (rel i u) (rel i v))) :=
  R.rho3 u v i

theorem eq_L [R : Rows T] (u v j : Nat) : T (imp (NF.eq u v) (imp (NF.eq u j) (NF.eq v j))) :=
  -- rho7: u = v → (u = j → v = j)
  R.rho7 v j u


/-- A label strictly above every label of a formula. -/
def top : NF → Nat
  | rel i j => max i j + 1
  | NF.eq i j => max i j + 1
  | NF.bot => 0
  | imp a b => max (top a) (top b)
  | all i a => max (i + 1) (top a)

theorem not_occurs_of_top_le {n : Nat} : ∀ {f : NF}, top f ≤ n → ¬ Occurs n f
  | rel i j, h => by simp only [top] at h; simp only [Occurs]; omega
  | NF.eq i j, h => by simp only [top] at h; simp only [Occurs]; omega
  | NF.bot, _ => id
  | imp a b, h => by
      simp only [top] at h
      simp only [Occurs]
      intro o
      cases o with
      | inl o | inr o => exact not_occurs_of_top_le (by omega) o
  | all i a, h => by
      simp only [top] at h
      simp only [Occurs]
      intro o
      cases o with
      | inl o => omega
      | inr o => exact not_occurs_of_top_le (by omega) o

section Atoms

variable (hC : Classical NF.imp NF.bot T)
include hC

/-- Rewriting both places of a two-place atom along `x = y`. -/
theorem atom_subst (P : Nat → Nat → NF)
    (hL : ∀ u v j, T (imp (NF.eq u v) (imp (P u j) (P v j))))
    (hR : ∀ u v i, T (imp (NF.eq u v) (imp (P i u) (P i v))))
    (x y i j : Nat) : T (imp (NF.eq x y) (imp (P i j) (P (rv x y i) (rv x y j)))) := by
  have step1 : T (imp (NF.eq x y) (imp (P i j) (P (rv x y i) j))) := by
    by_cases hi : i = x
    · subst hi; simp only [rv, if_true]; exact hL i y j
    · simp only [rv, hi, if_false]; exact ded2 hC h0
  have step2 : T (imp (NF.eq x y) (imp (P (rv x y i) j) (P (rv x y i) (rv x y j)))) := by
    by_cases hj : j = x
    · subst hj; simp only [rv, if_true]; exact hR j y _
    · simp only [rv, hj, if_false]; exact ded2 hC h0
  exact ded2 hC (.mp (.mp (.ax step2) h1) (.mp (.mp (.ax step1) h1) h0))

/-- The reverse rewriting, through symmetry of equality (`hs`). -/
theorem atom_subst_rev (hs : ∀ x y, T (imp (NF.eq x y) (NF.eq y x))) (P : Nat → Nat → NF)
    (hL : ∀ u v j, T (imp (NF.eq u v) (imp (P u j) (P v j))))
    (hR : ∀ u v i, T (imp (NF.eq u v) (imp (P i u) (P i v))))
    (x y i j : Nat) : T (imp (NF.eq x y) (imp (P (rv x y i) (rv x y j)) (P i j))) := by
  have step1 : T (imp (NF.eq y x) (imp (P (rv x y i) (rv x y j)) (P i (rv x y j)))) := by
    by_cases hi : i = x
    · subst hi; simp only [rv, if_true]; exact hL y i _
    · simp only [rv, hi, if_false]; exact ded2 hC h0
  have step2 : T (imp (NF.eq y x) (imp (P i (rv x y j)) (P i j))) := by
    by_cases hj : j = x
    · subst hj; simp only [rv, if_true]; exact hR y j i
    · simp only [rv, hj, if_false]; exact ded2 hC h0
  have hyx : Der NF.imp T [P (rv x y i) (rv x y j), NF.eq x y] (NF.eq y x) :=
    .mp (.ax (hs x y)) h1
  exact ded2 hC (.mp (.mp (.ax step2) hyx) (.mp (.mp (.ax step1) hyx) h0))

/-- Object-level existential monotonicity: `∀i(a → b) → (∃i a → ∃i b)`. -/
theorem all_imp_ex [R : Rows T] (i : Nat) (a b : NF) :
    T (imp (all i (imp a b)) (imp (ex i a) (ex i b))) := by
  have c1 : T (imp (all i (imp a b)) (all i (imp (neg b) (neg a)))) :=
    all_mono hC i (contra_thm hC a b)
  -- ∀i(a→b) → (∀i¬b → ∀i¬a), then contrapose the inner implication.
  have c3 : T (imp (all i (imp a b)) (imp (all i (neg b)) (all i (neg a)))) :=
    syl hC c1 (R.rho2 i (neg b) (neg a))
  -- hypotheses: ∀i(a→b), ∃i a = ¬∀i¬a; goal ∃i b = ¬∀i¬b
  exact ded2 hC (deduction hC (.mp h1 (.mp (.mp (.ax c3) h2) h0)))

end Atoms

section Leibniz

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

theorem eq_R (u v i : Nat) : Thm Ax (imp (NF.eq u v) (imp (NF.eq i u) (NF.eq i v))) :=
  ded2 hC (.mp (.mp (.ax (eq_trans hC i u v)) h0) h1)

/-- Leibniz's law for formulas without rebinding of either label. -/
theorem leibniz (x y : Nat) :
    ∀ f : NF, ¬ Bound x f → ¬ Bound y f →
      Thm Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
      Thm Ax (imp (NF.eq x y) (imp (rn x y f) f))
  | rel i j, _, _ =>
      ⟨atom_subst hC rel (rel_L (T := Thm Ax)) (rel_R (T := Thm Ax)) x y i j,
       atom_subst_rev hC (eq_symm hC) rel (rel_L (T := Thm Ax)) (rel_R (T := Thm Ax)) x y i j⟩
  | NF.eq i j, _, _ =>
      ⟨atom_subst hC NF.eq (eq_L (T := Thm Ax)) (eq_R hC) x y i j,
       atom_subst_rev hC (eq_symm hC) NF.eq (eq_L (T := Thm Ax)) (eq_R hC) x y i j⟩
  | NF.bot, _, _ => ⟨ded2 hC h0, ded2 hC h0⟩
  | imp a b, hx, hy => by
      have ha := leibniz x y a (fun h => hx (Or.inl h)) (fun h => hy (Or.inl h))
      have hb := leibniz x y b (fun h => hx (Or.inr h)) (fun h => hy (Or.inr h))
      -- hypotheses: x = y, a → b, a'; goal b'
      have a0 : Der NF.imp (Thm Ax) [rn x y a, imp a b, NF.eq x y] a :=
        .mp (.mp (.ax ha.2) h2) h0
      have a1 : Der NF.imp (Thm Ax) [a, imp (rn x y a) (rn x y b), NF.eq x y] (rn x y a) :=
        .mp (.mp (.ax ha.1) h2) h0
      exact ⟨ded3 hC (.mp (.mp (.ax hb.1) h2) (.mp h1 a0)),
        ded3 hC (.mp (.mp (.ax hb.2) h2) (.mp h1 a1))⟩
  | all i a, hx, hy => by
      have hix : i ≠ x := fun e => hx (Or.inl e.symm)
      have hiy : i ≠ y := fun e => hy (Or.inl e.symm)
      have ha := leibniz x y a (fun h => hx (Or.inr h)) (fun h => hy (Or.inr h))
      simp only [rn, hix, if_false]
      have lift : ∀ {p q : NF}, Thm Ax (imp (NF.eq x y) (imp p q)) →
          Thm Ax (imp (NF.eq x y) (imp (all i p) (all i q))) := by
        intro p q h
        have g : Thm Ax (imp (all i (NF.eq x y)) (all i (imp p q))) := all_mono hC i h
        have v : Thm Ax (imp (NF.eq x y) (all i (NF.eq x y))) := .vacEq x y i hix hiy
        exact ded2 hC (.mp (.mp (.ax (.rho2 i p q)) (.mp (.ax g) (.mp (.ax v) h1))) h0)
      exact ⟨lift ha.1, lift ha.2⟩

/-! ## Specialization and alpha-renaming -/

/-- Specialization: `∀x φ → φ[y/x]` when neither label is rebound and `y ≠ x`. -/
theorem spec {x y : Nat} (hxy : y ≠ x) {f : NF} (hx : ¬ Bound x f) (hy : ¬ Bound y f) :
    Thm Ax (imp (all x f) (rn x y f)) := by
  -- ∀x(x = y → f') from ∀x f
  have shuffle : Thm Ax (imp f (imp (NF.eq x y) (rn x y f))) :=
    ded2 hC (.mp (.mp (.ax (leibniz hC x y f hx hy).1) h0) h1)
  have g : Thm Ax (imp (all x f) (all x (imp (NF.eq x y) (rn x y f)))) := all_mono hC x shuffle
  have e : Thm Ax (imp (all x (imp (NF.eq x y) (rn x y f)))
      (imp (ex x (NF.eq x y)) (ex x (rn x y f)))) := all_imp_ex hC x _ _
  have elim : Thm Ax (imp (ex x (rn x y f)) (rn x y f)) :=
    ex_elim hC x (not_occurs_rn hxy f hx)
  exact ded1 hC (.mp (.ax elim) (.mp (.mp (.ax e) (.mp (.ax g) h0)) (.ax (.rho1 x y))))

/-- The T axiom `∀x φ → φ`, for `φ` without rebinding of `x`. -/
theorem spec_self {x : Nat} {f : NF} (hx : ¬ Bound x f) : Thm Ax (imp (all x f) f) := by
  let z := max (top f) (x + 1)
  have hz : ¬ Occurs z f := not_occurs_of_top_le (by omega)
  have hzx : z ≠ x := by omega
  have hzb : ¬ Bound z f := fun b => hz (bound_occurs b)
  -- ∀x f → f[z/x]
  have s1 : Thm Ax (imp (all x f) (rn x z f)) := spec hC hzx hx hzb
  -- ∀x f → ∀z ∀x f → ∀z f[z/x]
  have hzo : ¬ Occurs z (all x f) := by simp only [Occurs]; exact fun o => o.elim hzx hz
  have s2 : Thm Ax (imp (all x f) (all z (rn x z f))) :=
    syl hC (vac_of_not_occurs hC z _ hzo) (all_mono hC z s1)
  -- ∀z f[z/x] → f[z/x][x/z] = f
  have hzb' : ¬ Bound z (rn x z f) := fun b => hzb ((bound_rn x z z f).mp b)
  have hxb' : ¬ Bound x (rn x z f) := fun b => hx ((bound_rn x z x f).mp b)
  have s3 : Thm Ax (imp (all z (rn x z f)) (rn z x (rn x z f))) := spec hC (Ne.symm hzx) hzb' hxb'
  rw [rn_rn_fresh f hz] at s3
  exact syl hC s2 s3

/-- Alpha-renaming of a binder to a fresh label, forward direction. -/
theorem alpha_fwd {x y : Nat} (hxy : y ≠ x) {f : NF} (hx : ¬ Bound x f) (hy : ¬ Occurs y f) :
    Thm Ax (imp (all x f) (all y (rn x y f))) := by
  have hyb : ¬ Bound y f := fun b => hy (bound_occurs b)
  have hyo : ¬ Occurs y (all x f) := by simp only [Occurs]; exact fun o => o.elim hxy hy
  exact syl hC (vac_of_not_occurs hC y _ hyo) (all_mono hC y (spec hC hxy hx hyb))

/-- Alpha-renaming of a binder to a fresh label, backward direction. -/
theorem alpha_bwd {x y : Nat} (hxy : y ≠ x) {f : NF} (hx : ¬ Bound x f) (hy : ¬ Occurs y f) :
    Thm Ax (imp (all y (rn x y f)) (all x f)) := by
  have hyb : ¬ Bound y (rn x y f) := fun b => hy (bound_occurs ((bound_rn x y y f).mp b))
  have hxb : ¬ Bound x (rn x y f) := fun b => hx ((bound_rn x y x f).mp b)
  have s : Thm Ax (imp (all y (rn x y f)) (rn y x (rn x y f))) := spec hC (Ne.symm hxy) hyb hxb
  rw [rn_rn_fresh f hy] at s
  have hxo : ¬ Occurs x (all y (rn x y f)) := by
    simp only [Occurs]; exact fun o => o.elim (fun e => hxy e.symm) (not_occurs_rn hxy f hx)
  exact syl hC (vac_of_not_occurs hC x _ hxo) (all_mono hC x s)

end Leibniz

end SetTheory.BusyBeaver.ZFC.Tarski
