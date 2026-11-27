import IPRADerivations.DiophantineNumberTheory.PrimitiveReduction

/-!
# Injectivity of canonical powering

Packet: `analytic-number-theory/goldbach_euler_ipra`, Corollary `cor:injective`: if `r` and `u`
are root-free (`RF`: at least `2` and not of the form `w^d` with `d ≥ 2`), `i, j ≥ 1` and
`r^i = u^j`, then `r = u` and `i = j`.

The packet derives this from the canonical decomposition `lem:canonical` (prime factorizations).
The derivation here avoids factorizations altogether:

* `pw_inj`: `x^e = y^e → x = y` for `e ≥ 1`;
* `root_extract`: if `x a = y b + 1` and `r^a = u^b` (`r, u, b ≥ 1`) then `r = W^b` for the explicit
  integer `W = u^x / r^y`; that `r^y ∣ u^x` follows from `(r^y)^b ∣ (u^x)^b`
  (`dvd_of_pw_dvd_pw`);
* `bezout_pos`: for coprime `a, b ≥ 1`, Bézout coefficients with `x a = y b + 1` (one of two
  explicit pairs, from the extended Euclidean algorithm `bezout_at`);
* `exp_one`: if `r` is root-free, `r^a = u^b` and `gcd(a, b) = 1`, then `b = 1`;
* `canonical_injective`: divide `i, j` by `g = gcd(i, j)`, cancel the common power `g`, and apply
  `exp_one` on both sides.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.CanonicalPowers

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PrimitiveReduction (dvd_of_pw_dvd_pw)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `RF(r)`: `r ≥ 2` and `r ≠ w^d` for all `w` and all `d ≥ 2`. -/
abbrev RF (r : PTm n) : Fm PTm n :=
  le two r ⋏ Fm.all (Fm.all (le two (var 0) ⟶ neg (pw (var 1) (var 0) ≐ Syn.shift (Syn.shift r))))

theorem RF_pos {r : PTm n} (h : Γ ⊢[PRAAx] RF r) : Γ ⊢[PRAAx] r ≐ succ (pred r) := by
  refine eq_succ_pred (y := one + monus r two) ?_
  ipra_lc natEq (eq_add_of_le (Prf.andE₁ h))

theorem subst_up_shift_rf {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem subst_sh2 (r w d : PTm n) :
    Syn.subst (Syn.inst d) (Syn.subst (Syn.up (Syn.inst w)) (Syn.shift (Syn.shift r))) = r := by
  rw [subst_up_shift_rf]; simp

theorem RF_inst {r : PTm n} (h : Γ ⊢[PRAAx] RF r) (w d : PTm n) :
    Γ ⊢[PRAAx] le two d ⟶ neg (pw w d ≐ r) := by
  have i := Prf.allE d (Prf.allE w (Prf.andE₂ h))
  simpa [subst_sh2] using i

/-- `x^e = y^e → x = y` for `e ≥ 1`. -/
theorem pw_inj {x y e : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] pw x e ≐ pw y e) :
    Γ ⊢[PRAAx] x ≐ y := by
  have h' : Γ ⊢[PRAAx] pw x (succ (pred e)) ≐ pw y (succ (pred e)) :=
    (congrPw (.eqRefl x) he.eqSymm).eqTrans (h.eqTrans (congrPw (.eqRefl y) he))
  exact le_antisymm (pw_le_cancel (le_congr (.eqRefl _) h' (le_refl _)))
    (pw_le_cancel (le_congr (.eqRefl _) h'.eqSymm (le_refl _)))

/-- `x a = y b + 1` and `r^a = u^b` give `r = W^b` for `W = u^x / r^y`. -/
theorem root_extract {r u a b x y : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (hu : Γ ⊢[PRAAx] u ≐ succ (pred u)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hxy : Γ ⊢[PRAAx] x * a ≐ y * b + one) (h : Γ ⊢[PRAAx] pw r a ≐ pw u b) :
    Γ ⊢[PRAAx] pw (quo (pw u x) (pw r y)) b ≐ r := by
  have e₁ : Γ ⊢[PRAAx] pw (pw u x) b ≐ pw (pw u b) x :=
    (pw_mul u x b).eqTrans ((congrPw (.eqRefl u) (mul_comm x b)).eqTrans (pw_mul u b x).eqSymm)
  have e₂ : Γ ⊢[PRAAx] pw (pw u b) x ≐ pw (pw r a) x := congrPw h.eqSymm (.eqRefl x)
  have e₃ : Γ ⊢[PRAAx] pw (pw r a) x ≐ pw r (y * b + one) :=
    (pw_mul r a x).eqTrans (congrPw (.eqRefl r) ((mul_comm a x).eqTrans hxy))
  have e₄ : Γ ⊢[PRAAx] pw r (y * b + one) ≐ pw (pw r y) b * r :=
    (pw_add r (y * b) one).eqTrans (congrMul (pw_mul r y b).eqSymm (pw_one r))
  have P := e₁.eqTrans (e₂.eqTrans (e₃.eqTrans e₄))
  have hry := pw_pos' hr y
  have hD := pw_pos' hry b
  have dv : Γ ⊢[PRAAx] dvd (pw r y) (pw u x) :=
    dvd_of_pw_dvd_pw hry (pw_pos' hu x) hb (dvd_of_eq' hD P)
  have eW := eq_of_dvd' hry dv
  have Q : Γ ⊢[PRAAx] pw (pw u x) b ≐ pw (pw r y) b * pw (quo (pw u x) (pw r y)) b :=
    (congrPw eW (.eqRefl b)).eqTrans (pw_mul_base _ _ b)
  exact mul_cancel hD (Q.eqSymm.eqTrans P)

/-- Bézout coefficients in the form `x a = y b + 1`, as one of two explicit pairs. -/
theorem bezout_pos {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hg : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] (Bezout.cur one zero (succ b) a b * a ≐ Bezout.cur zero one (succ b) a b * b + one) ⋎
      (monus (b * Bezout.cur zero one (succ b) a b) (Bezout.cur one zero (succ b) a b) * a ≐
        monus (Bezout.cur zero one (succ b) a b * a) (Bezout.cur zero one (succ b) a b) * b + one) := by
  refine .orE (bezout_at a b) (.orI₁ ?_) (.orI₂ ?_)
  · let C : List (Fm PTm n) := (gcd a b + Bezout.cur zero one (succ b) a b * b ≐
      Bezout.cur one zero (succ b) a b * a) :: Γ
    have e := natEq (Prf.hyp0 : C ⊢[PRAAx] _)
    ipra_lc -e + natEq (hg.wk : C ⊢[PRAAx] _)
  · let U := Bezout.cur one zero (succ b) a b
    let V := Bezout.cur zero one (succ b) a b
    let C : List (Fm PTm n) := (gcd a b + U * a ≐ V * b) :: Γ
    have hz : C ⊢[PRAAx] gcd a b + U * a ≐ V * b := Prf.hyp0
    have e := natEq hz
    have g := natEq (hg.wk : C ⊢[PRAAx] _)
    have lx : C ⊢[PRAAx] le U (b * V) := by
      refine le_of_eq_add (d := U * pred a + one) ?_
      ipra_lc -e + g + 𝔞 U * natEq (ha.wk : C ⊢[PRAAx] _)
    have ly : C ⊢[PRAAx] le V (V * a) := by
      refine le_of_eq_add (d := V * pred a) ?_
      ipra_lc 𝔞 V * natEq (ha.wk : C ⊢[PRAAx] _)
    ipra_lc -𝔞 a * natEq (eq_add_of_le lx) + 𝔞 b * natEq (eq_add_of_le ly) - e + g

/-- If `r` is root-free, `r^a = u^b`, `a, b ≥ 1` and `gcd(a, b) = 1`, then `b = 1`. -/
theorem exp_one {r u a b : PTm n} (hRF : Γ ⊢[PRAAx] RF r) (hu : Γ ⊢[PRAAx] u ≐ succ (pred u))
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hg : Γ ⊢[PRAAx] gcd a b ≐ one) (h : Γ ⊢[PRAAx] pw r a ≐ pw u b) : Γ ⊢[PRAAx] b ≐ one := by
  have hr := RF_pos hRF
  refine .orE (lt_or_le one b) ?_ (le_antisymm Prf.hyp0 (one_le_of_pos hb.wk))
  let C : List (Fm PTm n) := lt one b :: Γ
  have h2 : C ⊢[PRAAx] le two b := Prf.hyp0
  let U := Bezout.cur one zero (succ b) a b
  let V := Bezout.cur zero one (succ b) a b
  refine .orE (bezout_pos ha.wk hg.wk) ?_ ?_
  · have w := root_extract hr.wk.wk hu.wk.wk hb.wk.wk
      (Prf.hyp0 : ((U * a ≐ V * b + one) :: C) ⊢[PRAAx] _) h.wk.wk
    exact .botE _ (Prf.impE (Prf.impE (RF_inst hRF.wk.wk _ _) h2.wk) w)
  · have w := root_extract hr.wk.wk hu.wk.wk hb.wk.wk
      (Prf.hyp0 : ((monus (b * V) U * a ≐ monus (V * a) V * b + one) :: C) ⊢[PRAAx] _) h.wk.wk
    exact .botE _ (Prf.impE (Prf.impE (RF_inst hRF.wk.wk _ _) h2.wk) w)

/-- `cor:injective`: root-free `r, u`, `i, j ≥ 1` and `r^i = u^j` give `r = u` and `i = j`. -/
theorem canonical_injective {r u i j : PTm n} (hr : Γ ⊢[PRAAx] RF r) (hu : Γ ⊢[PRAAx] RF u)
    (hi : Γ ⊢[PRAAx] i ≐ succ (pred i)) (hj : Γ ⊢[PRAAx] j ≐ succ (pred j))
    (h : Γ ⊢[PRAAx] pw r i ≐ pw u j) : Γ ⊢[PRAAx] (r ≐ u) ⋏ (i ≐ j) := by
  have hg := gcd_pos (B := j) hi
  have dv := gcd_dvd' (b := j) hi
  have eI := eq_of_dvd' hg (Prf.andE₁ dv)
  have eJ := eq_of_dvd' hg (Prf.andE₂ dv)
  have ha := pos_of_eq_mul hi eI
  have hb := pos_of_eq_mul hj eJ
  have cop := coprime_quotients (c := j) hi
  have hab : Γ ⊢[PRAAx] pw r (quo i (gcd i j)) ≐ pw u (quo j (gcd i j)) := by
    refine pw_inj hg ?_
    refine (pw_mul r _ _).eqTrans ((congrPw (.eqRefl r) ((mul_comm _ _).eqTrans eI.eqSymm)).eqTrans ?_)
    refine h.eqTrans ((congrPw (.eqRefl u) (eJ.eqTrans (mul_comm _ _))).eqTrans (pw_mul u _ _).eqSymm)
  have b1 := exp_one hr (RF_pos hu) ha hb cop hab
  have a1 := exp_one hu (RF_pos hr) hb ha (gcd_comm_one hb cop) hab.eqSymm
  refine .andI ?_ ?_
  · exact (pw_one r).eqSymm.eqTrans ((congrPw (.eqRefl r) a1.eqSymm).eqTrans
      (hab.eqTrans ((congrPw (.eqRefl u) b1).eqTrans (pw_one u))))
  · exact eI.eqTrans ((congrMul (.eqRefl _) (a1.eqTrans b1.eqSymm)).eqTrans eJ.eqSymm)

end LeanProofs.IPRA.AnalyticNumberTheory.CanonicalPowers
