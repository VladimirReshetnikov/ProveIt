import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Foundations.PresentedCategory

/-!
# The table category of nonempty finite sets (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The category of finite sets has
exponentials in iPRA": "An arrow `[n] → [m]` is the canonical table of its `n` entries ...
Identity is the table `j ↦ j`. Composition is the table `j ↦ ev(g, ev(f, j))`. Equality is
... literal equality of canonical table codes. Closure and the category laws follow by
evaluating at an arbitrary `j < n`."

This module presents that category in the sense of `Foundations/PresentedCategory` and
derives all nine laws (`finSet`, `finSet_laws`):

* objects: numbers `a ≥ 1` (the sets `[a]`; the empty set is excluded because the digit
  coding needs a positive base);
* arrows `a → b`: codes `f < b^a`, with `ev(f, j) = ⌊f / b^j⌋ mod b`;
* equality of arrows: equality of codes (decidable);
* identity `idc a`: the code of `j ↦ j`; composite `cmpc a b d g f`: the code of
  `j ↦ ev(g, ev(f, j))`, both built with `code` of `Foundations/FiniteSetExponential`.

`ev_id`, `ev_comp` evaluate identity and composite entrywise; `code_congr` says that tables
with equal entries below `N` have equal codes. Associativity and the unit laws are then
entrywise computations followed by `curry_ev`.

`finSet_terminal`: `[1]` is a terminal object (`Terminal` of `Foundations/PresentedCategory`):
the unique table into `[1]` has code `0`, because the only code below `1^x = 1` is `0`
(`one_pw`).

Consequently every theorem about presented categories applies to finite sets; for example
`finSet_inverse_unique`: a table with a left inverse and a right inverse has them equal, as
one closed sentence about codes.
-/

namespace LeanProofs.IPRA.Foundations.FiniteSetCategory

open_ipra exports
open LeanProofs.IPRA.Probability.ProductPower (dg)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open LeanProofs.IPRA.Foundations.PresentedCategory

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Tables with equal entries have equal codes -/

/-- If the entries of two tables agree below `N`, their codes agree. -/
theorem code_congr (t t' : PTm 2) {N m q q' : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (rem (inst2 t (var 0) (Syn.shift q)) (Syn.shift m) ≐
        rem (inst2 t' (var 0) (Syn.shift q')) (Syn.shift m)))) :
    Γ ⊢[PRAAx] code t N m q ≐ code t' N m q' := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT]
  refine (cB_at t _ _ _).eqTrans (.eqTrans ?_ (cB_at t' _ _ _).eqSymm)
  exact congrMul (.impE h.allOpen.wk Prf.hyp0) (.eqRefl _)

/-- The digit depends only on the value of its index. -/
theorem dg_idx {m y y' c : PTm k} (h : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx] dg m y c ≐ dg m y' c :=
  congrAp2 remF (congrAp2 quoF (.eqRefl _) (congrPw (.eqRefl _) h)) (.eqRefl _)

theorem shift_pos (b : PTm k) :
    Fm.shift (b ≐ succ (pred b)) = (Syn.shift b ≐ succ (pred (Syn.shift b))) := by
  simp [Fm.shift, Syn.shift]

/-! ## Identity and composition tables -/

/-- The identity table `j ↦ j`. -/
def idT : PTm 2 := var 0

/-- The code of the identity of `[a]`. -/
abbrev idc (a : PTm k) : PTm k := code idT a a zero

/-- The entry `ev(g, ev(f, j))` of the composite; variables `0 = j`,
`1 = ⟨b, ⟨d, ⟨g, f⟩⟩⟩`. -/
def cmT : PTm 2 :=
  dg (fstT (sndT (var 1))) (dg (fstT (var 1)) (var 0) (sndT (sndT (sndT (var 1)))))
    (fstT (sndT (sndT (var 1))))

/-- The code of `g ∘ f` for `f : [a] → [b]`, `g : [b] → [d]`. -/
abbrev cmpc (a b d g f : PTm k) : PTm k := code cmT a d (pairT b (pairT d (pairT g f)))

theorem cmT_at (j b d g f : PTm k) :
    Γ ⊢[PRAAx] inst2 cmT j (pairT b (pairT d (pairT g f))) ≐ dg d (dg b j f) g := by
  simpa [inst2, cmT, pairVector, pairVectorField, Syn.subst_subst] using
    subst_pairVector_eq (Γ := Γ) (dg (var 2 : PTm 5) (dg (var 1) (var 0) (var 4)) (var 3))
      j ![b, d, g, f]

theorem shift_idc (a : PTm k) : Syn.shift (idc a) = idc (Syn.shift a) := by simp [Syn.shift]

theorem shift_cmpc (a b d g f : PTm k) :
    Syn.shift (cmpc a b d g f) =
      cmpc (Syn.shift a) (Syn.shift b) (Syn.shift d) (Syn.shift g) (Syn.shift f) := by
  simp [Syn.shift]

/-- `ev(1_a, y) = y` for `y < a`. -/
theorem ev_id {a y : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hy : Γ ⊢[PRAAx] lt y a) :
    Γ ⊢[PRAAx] dg a y (idc a) ≐ y := by
  have e : inst2 idT y (zero : PTm k) = y := by simp [inst2, idT]
  have r := ev_curry_of_lt idT (p := (zero : PTm k)) ha hy (by rw [e]; exact hy)
  rw [e] at r
  exact r

/-- `ev(g ∘ f, j) = ev(g, ev(f, j))` for `j < a`. -/
theorem ev_comp {a b d g f j : PTm k} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hj : Γ ⊢[PRAAx] lt j a) :
    Γ ⊢[PRAAx] dg d j (cmpc a b d g f) ≐ dg d (dg b j f) g :=
  (ev_curry cmT hd hj (pairT b (pairT d (pairT g f)))).eqTrans
    ((congrAp2 remF (cmT_at j b d g f) (.eqRefl _)).eqTrans (rem_of_lt hd (dg_lt hd _ _)))

/-! ## The presentation -/

/-- The table category of nonempty finite sets. -/
def finSet : Pres where
  Obj := (var 0 : PTm 1) ≐ succ (pred (var 0))
  Hom := ((var 0 : PTm 3) ≐ succ (pred (var 0))) ⋏
    (((var 1 : PTm 3) ≐ succ (pred (var 1))) ⋏ lt (var 2) (pw (var 1) (var 0)))
  Eqv := (var 2 : PTm 4) ≐ var 3
  idt := code idT (var 0) (var 0) zero
  cmp := code cmT (var 0) (var 2) (pairT (var 1) (pairT (var 2) (pairT (var 3) (var 4))))

theorem fs_obj (a : PTm k) : finSet.obj a = (a ≐ succ (pred a)) := by
  simp [Pres.obj, finSet]

theorem fs_hom (a b f : PTm k) :
    finSet.hom a b f = ((a ≐ succ (pred a)) ⋏ ((b ≐ succ (pred b)) ⋏ lt f (pw b a))) := by
  simp [Pres.hom, finSet]

theorem fs_eqv (a b f g : PTm k) : finSet.eqv a b f g = (f ≐ g) := by
  simp [Pres.eqv, finSet]

theorem fs_id (a : PTm k) : finSet.id1 a = idc a := by
  simp [Pres.id1, finSet]

theorem fs_comp (a b d g f : PTm k) : finSet.comp a b d g f = cmpc a b d g f := by
  simp [Pres.comp, finSet]

/-! ## The laws -/

theorem idl_pt {j b f : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] inst2 cmT j (pairT b (pairT b (pairT (idc b) f))) ≐ inst2 evT j (pairT b f) :=
  (cmT_at j b b (idc b) f).eqTrans ((ev_id hb (dg_lt hb j f)).eqTrans (evT_at j b f).eqSymm)

theorem idr_pt {j a b f : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hj : Γ ⊢[PRAAx] lt j a) :
    Γ ⊢[PRAAx] inst2 cmT j (pairT a (pairT b (pairT f (idc a)))) ≐ inst2 evT j (pairT b f) :=
  (cmT_at j a b f (idc a)).eqTrans ((dg_idx (ev_id ha hj)).eqTrans (evT_at j b f).eqSymm)

theorem assoc_pt {j a b d e f g h : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hj : Γ ⊢[PRAAx] lt j a) :
    Γ ⊢[PRAAx] inst2 cmT j (pairT b (pairT e (pairT (cmpc b d e h g) f))) ≐
      inst2 cmT j (pairT d (pairT e (pairT h (cmpc a b d g f)))) := by
  have l := (cmT_at (Γ := Γ) j b e (cmpc b d e h g) f).eqTrans (ev_comp he (dg_lt hb j f))
  have r := (cmT_at (Γ := Γ) j d e h (cmpc a b d g f)).eqTrans (dg_idx (ev_comp hd hj))
  exact l.eqTrans r.eqSymm

/-- The left unit law. -/
theorem fs_id_left {a b f : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom a b f) :
    Γ ⊢[PRAAx] cmpc a b b (idc b) f ≐ f := by
  rw [fs_hom] at hf
  have hb := Prf.andE₁ (Prf.andE₂ hf)
  refine .eqTrans (code_congr cmT evT (q' := pairT b f) (.allI (.impI ?_)))
    (curry_ev hb (Prf.andE₂ (Prf.andE₂ hf)))
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_idc]
  have hb' := hb.shift
  rw [shift_pos] at hb'
  exact congrAp2 remF (idl_pt hb'.wk) (.eqRefl _)

/-- The right unit law. -/
theorem fs_id_right {a b f : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom a b f) :
    Γ ⊢[PRAAx] cmpc a a b f (idc a) ≐ f := by
  rw [fs_hom] at hf
  have ha := Prf.andE₁ hf
  have hb := Prf.andE₁ (Prf.andE₂ hf)
  refine .eqTrans (code_congr cmT evT (q' := pairT b f) (.allI (.impI ?_)))
    (curry_ev hb (Prf.andE₂ (Prf.andE₂ hf)))
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_idc]
  have ha' := ha.shift
  rw [shift_pos] at ha'
  exact congrAp2 remF (idr_pt ha'.wk Prf.hyp0) (.eqRefl _)

/-- Associativity. -/
theorem fs_assoc {a b d e f g h : PTm k} (hf : Γ ⊢[PRAAx] finSet.hom a b f)
    (hg : Γ ⊢[PRAAx] finSet.hom b d g) (hh : Γ ⊢[PRAAx] finSet.hom d e h) :
    Γ ⊢[PRAAx] cmpc a b e (cmpc b d e h g) f ≐ cmpc a d e h (cmpc a b d g f) := by
  rw [fs_hom] at hf hg hh
  have hb := Prf.andE₁ (Prf.andE₂ hf)
  have hd := Prf.andE₁ (Prf.andE₂ hg)
  have he := Prf.andE₁ (Prf.andE₂ hh)
  refine code_congr cmT cmT (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_pairT,
    shift_cmpc, shift_cmpc]
  have hb' := hb.shift
  rw [shift_pos] at hb'
  have hd' := hd.shift
  rw [shift_pos] at hd'
  have he' := he.shift
  rw [shift_pos] at he'
  exact congrAp2 remF (assoc_pt hb'.wk hd'.wk he'.wk Prf.hyp0) (.eqRefl _)

/-- The table category of nonempty finite sets satisfies the category laws. -/
theorem finSet_laws : finSet.Laws where
  eqv_refl := fun _ => by rw [fs_eqv]; exact .eqRefl _
  eqv_symm := fun h => by rw [fs_eqv] at h ⊢; exact h.eqSymm
  eqv_trans := fun h₁ h₂ => by rw [fs_eqv] at h₁ h₂ ⊢; exact h₁.eqTrans h₂
  id_hom := fun {k Γ a} ha => by
    rw [fs_obj] at ha
    rw [fs_hom, fs_id]
    exact .andI ha (.andI ha (code_lt idT ha a zero))
  comp_hom := fun {k Γ a b d f g} hf hg => by
    rw [fs_hom] at hf hg
    rw [fs_hom, fs_comp]
    exact .andI (Prf.andE₁ hf) (.andI (Prf.andE₁ (Prf.andE₂ hg))
      (code_lt cmT (Prf.andE₁ (Prf.andE₂ hg)) a _))
  comp_congr := fun {k Γ a b d f f' g g'} h₁ h₂ => by
    rw [fs_eqv] at h₁ h₂ ⊢
    exact Prf.eqCongr finSet.cmp fun l => by
      fin_cases l
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _
      · exact h₂
      · exact h₁
  assoc := fun hf hg hh => by
    rw [fs_eqv]
    simp only [fs_comp]
    exact fs_assoc hf hg hh
  id_left := fun hf => by
    rw [fs_eqv, fs_comp, fs_id]
    exact fs_id_left hf
  id_right := fun hf => by
    rw [fs_eqv, fs_comp, fs_id]
    exact fs_id_right hf

/-- Uniqueness of inverses for tables of finite sets, as one closed sentence about codes. -/
theorem finSet_inverse_unique :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (inverseUniqueFormula finSet) :=
  inverse_unique_closed finSet_laws

/-! ## The terminal object `[1]` -/

private theorem one_pw₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] pw (one : PTm 1) (var 0) ≐ one :=
  pw_base_one (var 0)

/-- `1^x = 1`. -/
theorem one_pw (x : PTm k) : Γ ⊢[PRAAx] pw one x ≐ one := by
  simpa using inst (Γ := Γ) one_pw₀ (![x] : Fin 1 → PTm k)

/-- The terminal object `[1]` (no parameter is used). -/
def termT : PTm 1 := one
/-- The unique table `[x] → [1]`: all entries `0`, code `0`. -/
def bangT : PTm 2 := zero

theorem subst_termT (p : PTm k) : Syn.subst ![p] termT = one := by simp [termT]

theorem subst_bangT (p x : PTm k) : Syn.subst ![p, x] bangT = zero := by simp [bangT]

/-- `[1]` is a terminal object of the table category: the only code below `1^x` is `0`. -/
theorem finSet_terminal : Terminal finSet termT bangT where
  bang_hom := fun {k Γ p x} hx => by
    rw [fs_obj] at hx
    rw [subst_termT, subst_bangT, fs_hom]
    exact .andI hx (.andI (pos_of_eq_succ (c := zero) (.eqRefl _))
      (lt_congr (.eqRefl _) (one_pw x).eqSymm (le_refl one)))
  bang_unique := fun {k Γ p x f} hf => by
    rw [subst_termT, fs_hom] at hf
    rw [subst_termT, subst_bangT, fs_eqv]
    have h : Γ ⊢[PRAAx] lt f one := lt_congr (.eqRefl _) (one_pw x) (Prf.andE₂ (Prf.andE₂ hf))
    exact (monus_zero f).eqSymm.eqTrans ((succ_monus_succ f zero).eqSymm.eqTrans h)

end LeanProofs.IPRA.Foundations.FiniteSetCategory
