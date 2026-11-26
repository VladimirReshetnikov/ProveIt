import IPRADerivations.DiophantineNumberTheory.PellModular
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Dirichlet's approximation theorem, sharp rational form

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:dir-rational`: for a
rational `r = a/b ≥ 0` and `N ≥ 1`, explicit `1 ≤ q ≤ N` and `p` with `|qr − p| ≤ 1/(N+1)`, i.e.
`(N+1) |qa − pb| ≤ b`.

Pigeonhole (`Core/Pigeonhole`) on `N + 2` points in `N + 1` boxes: the point `k ≤ N` lies in box
`⌊((ka) mod b)(N+1)/b⌋`, and the extra point `N + 1` (the residue `1`) in box `N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (one_le_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq' rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Boxes -/

/-- `⌊x (N+1) / b⌋ ≤ N` for `x < b`. -/
theorem quo_le {x b N : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hx : Γ ⊢[PRAAx] lt x b) :
    Γ ⊢[PRAAx] le (quo (x * succ N) b) N := by
  refine .orE (lt_or_le N (quo (x * succ N) b)) ?_ Prf.hyp0
  refine .botE _ ?_
  refine succ_ne_zero' _ (a := monus b (succ x) * succ N + b * monus (quo (x * succ N) b) (succ N) +
    rem (x * succ N) b + N) ?_
  ipra_lc -natEq ((div_eq (j := x * succ N) hb).wk (ψ := lt N (quo (x * succ N) b))) -
    Groth.ι (Q.mk _ b) * natEq (eq_add_of_le (Prf.hyp0 : (lt N (quo (x * succ N) b) :: Γ) ⊢[PRAAx] _)) -
    (Groth.ι (Q.mk _ N) + 1) * natEq ((eq_add_of_le hx).wk (ψ := lt N (quo (x * succ N) b)))

/-- Decoding `x = ⟨a, ⟨b, N⟩⟩`. -/
abbrev code (a b N : PTm n) : PTm n := pairT a (pairT b N)
abbrev dA (x : PTm n) : PTm n := fstT x
abbrev dB (x : PTm n) : PTm n := fstT (sndT x)
abbrev dN (x : PTm n) : PTm n := sndT (sndT x)

/-- The box of point `k`: `N` for `k = N + 1`, else `⌊((ka) mod b)(N+1)/b⌋`. -/
abbrev box (k a b N : PTm n) : PTm n :=
  eqb k (succ N) * N + monus one (eqb k (succ N)) * quo (rem (k * a) b * succ N) b

abbrev boxB : PTm 2 := box (var 0) (dA (var 1)) (dB (var 1)) (dN (var 1))

theorem inst2_box (k x : PTm n) : inst2 boxB k x = box k (dA x) (dB x) (dN x) := by simp [inst2]

theorem congrBox {k a a' b b' N N' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx] box k a b N ≐ box k a' b' N' := by
  have e := AnalyticNumberTheory.Euler.congrEqb (.eqRefl k) (congrSucc hN)
  exact congrAdd (congrMul e hN) (congrMul (congrMonus (.eqRefl _) e)
    (congrAp2 quoF (congrMul (congrAp2 remF (congrMul (.eqRefl _) ha) hb) (congrSucc hN)) hb))

theorem at_code (k a b N : PTm n) : Γ ⊢[PRAAx] inst2 boxB k (code a b N) ≐ box k a b N := by
  rw [inst2_box]
  exact congrBox (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem box_at_top (a b N : PTm n) : Γ ⊢[PRAAx] box (succ N) a b N ≐ N := by
  have e := eqb_of_eq (Γ := Γ) (.eqRefl (succ N))
  refine (congrAdd (congrMul e (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) e).eqTrans
    ((succ_monus_succ _ _).eqTrans (monus_zero _))) (.eqRefl _))).eqTrans ?_
  ipra_ring

theorem box_below {k a b N : PTm n} (h : Γ ⊢[PRAAx] neg (k ≐ succ N)) :
    Γ ⊢[PRAAx] box k a b N ≐ quo (rem (k * a) b * succ N) b := by
  have e := eqb_of_ne h
  refine (congrAdd (congrMul e (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) e).eqTrans (monus_zero _))
    (.eqRefl _))).eqTrans ?_
  ipra_ring

theorem congrBoxK {k k' a b N : PTm n} (h : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] box k a b N ≐ box k' a b N := by
  have e := AnalyticNumberTheory.Euler.congrEqb h (.eqRefl (succ N))
  exact congrAdd (congrMul e (.eqRefl _)) (congrMul (congrMonus (.eqRefl _) e)
    (congrAp2 quoF (congrMul (congrAp2 remF (congrMul h (.eqRefl _)) (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))

theorem box_lt {a b N : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (k : PTm n) :
    Γ ⊢[PRAAx] lt (box k a b N) (succ N) := by
  refine .orE (eq_or_ne k (succ N)) ?_ ?_
  · exact lt_congr ((box_at_top a b N).eqSymm.eqTrans (congrBoxK Prf.hyp0).eqSymm) (.eqRefl _)
      ((succ_monus_succ _ _).eqTrans (le_refl N))
  · exact lt_congr (box_below Prf.hyp0).eqSymm (.eqRefl _)
      ((succ_monus_succ _ _).eqTrans (quo_le hb.wk (rem_lt' hb.wk _)))

theorem box_range {a b N : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] Permutation.rangeAll boxB (succ N) (code a b N) := by
  refine .allI ?_
  have e₁ : Syn.shift (code a b N) = code (Syn.shift a) (Syn.shift b) (Syn.shift N) := by simp [Syn.shift]
  have e₂ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [e₁, e₂]
  exact lt_congr (at_code _ _ _ _).eqSymm (.eqRefl _) (box_lt (AnalyticNumberTheory.GcdFiber.shift_pos hb) _)

/-! ## Distances -/

/-- `|X − Y|`. -/
abbrev dist (X Y : PTm n) : PTm n := monus X Y + monus Y X

theorem dist_l {X Y e : PTm n} (h : Γ ⊢[PRAAx] Y ≐ X + e) : Γ ⊢[PRAAx] dist X Y ≐ e :=
  (congrAdd ((congrMonus (.eqRefl _) h).eqTrans (monus_add _ _))
    ((congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans (zero_add _)

theorem dist_r {X Y e : PTm n} (h : Γ ⊢[PRAAx] X ≐ Y + e) : Γ ⊢[PRAAx] dist X Y ≐ e :=
  (congrAdd ((congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _))
    ((congrMonus (.eqRefl _) h).eqTrans (monus_add _ _))).eqTrans (add_zero _)

theorem quo_mono {X Y b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (h : Γ ⊢[PRAAx] le X Y) :
    Γ ⊢[PRAAx] le (quo X b) (quo Y b) := by
  refine .orE (lt_or_le (quo Y b) (quo X b)) ?_ Prf.hyp0
  refine .botE _ ?_
  refine succ_ne_zero' _ (a := monus b (succ (rem Y b)) + b * monus (quo X b) (succ (quo Y b)) + rem X b +
    monus Y X) ?_
  ipra_lc -natEq ((eq_add_of_le h).wk (ψ := lt (quo Y b) (quo X b))) +
    natEq ((div_eq (j := Y) hb).wk (ψ := lt (quo Y b) (quo X b))) -
    natEq ((div_eq (j := X) hb).wk (ψ := lt (quo Y b) (quo X b))) -
    Groth.ι (Q.mk _ b) * natEq (eq_add_of_le (Prf.hyp0 : (lt (quo Y b) (quo X b) :: Γ) ⊢[PRAAx] _)) -
    natEq ((eq_add_of_le (rem_lt' hb Y)).wk (ψ := lt (quo Y b) (quo X b)))

theorem congrDist {X X' Y Y' : PTm n} (h₁ : Γ ⊢[PRAAx] X ≐ X') (h₂ : Γ ⊢[PRAAx] Y ≐ Y') :
    Γ ⊢[PRAAx] dist X Y ≐ dist X' Y' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-! ## The two collision cases -/

/-- Collision with the extra point: `q = i`, `p = ⌊ia/b⌋ + 1`. -/
theorem caseA {a b N I : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hI : Γ ⊢[PRAAx] lt I (succ N)) (hbox : Γ ⊢[PRAAx] quo (rem (I * a) b * succ N) b ≐ N) :
    Γ ⊢[PRAAx] le one I ⋏ (le I N ⋏ le (succ N * dist (I * a) (succ (quo (I * a) b) * b)) b) := by
  have hI1 : Γ ⊢[PRAAx] le one I := by
    refine .orE (zero_or_succ I) ?_ (one_le_of_pos Prf.hyp0)
    have x0 : ((I ≐ zero) :: Γ) ⊢[PRAAx] rem (I * a) b ≐ zero :=
      (congrAp2 remF ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (rem_zero _)
    have q0 : ((I ≐ zero) :: Γ) ⊢[PRAAx] quo (rem (I * a) b * succ N) b ≐ zero :=
      (congrAp2 quoF ((congrMul x0 (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans
        (quo_eq hb.wk (q := zero) (r := zero) (by ipra_ring) (zero_lt' hb.wk))
    exact succ_ne_zero' _ (hN.wk.eqSymm.eqTrans (hbox.wk.eqSymm.eqTrans q0))
  have hIN : Γ ⊢[PRAAx] le I N := (succ_monus_succ _ _).eqSymm.eqTrans hI
  have hx := rem_lt' hb (I * a)
  have hd : Γ ⊢[PRAAx] dist (I * a) (succ (quo (I * a) b) * b) ≐ monus b (rem (I * a) b) := by
    refine dist_l ?_
    ipra_lc -natEq (div_eq (j := I * a) hb) + natEq (eq_add_of_le (le_of_lt hx))
  have hbd : Γ ⊢[PRAAx] le (succ N * monus b (rem (I * a) b)) b := by
    refine le_of_eq_add (d := rem (rem (I * a) b * succ N) b) ?_
    ipra_lc natEq (div_eq (j := rem (I * a) b * succ N) hb) + Groth.ι (Q.mk _ b) * natEq hbox +
      (Groth.ι (Q.mk _ N) + 1) * natEq (eq_add_of_le (le_of_lt hx))
  exact .andI hI1 (.andI hIN (le_congr (congrMul (.eqRefl _) hd.eqSymm) (.eqRefl _) hbd))

theorem ident {t a x p b y I J Qi Qj : PTm n} (eJ : Γ ⊢[PRAAx] J ≐ I + t) (eQ : Γ ⊢[PRAAx] Qj ≐ Qi + p)
    (dI : Γ ⊢[PRAAx] I * a ≐ b * Qi + x) (dJ : Γ ⊢[PRAAx] J * a ≐ b * Qj + y) : Γ ⊢[PRAAx] t * a + x ≐ p * b + y := by
  ipra_lc -Groth.ι (Q.mk _ a) * natEq eJ + natEq dJ - natEq dI + Groth.ι (Q.mk _ b) * natEq eQ

theorem gap_bound {X Y d b N c₁ c₂ r₁ r₂ s : PTm n} (ed : Γ ⊢[PRAAx] X ≐ Y + d)
    (d₁ : Γ ⊢[PRAAx] X * succ N ≐ b * c₁ + r₁) (d₂ : Γ ⊢[PRAAx] Y * succ N ≐ b * c₂ + r₂)
    (hc : Γ ⊢[PRAAx] c₁ ≐ c₂) (eB : Γ ⊢[PRAAx] b ≐ succ r₁ + s) :
    Γ ⊢[PRAAx] b ≐ succ N * d + (r₂ + succ s) := by
  ipra_lc natEq eB - natEq d₁ + natEq d₂ - Groth.ι (Q.mk _ b) * natEq hc + (Groth.ι (Q.mk _ N) + 1) * natEq ed

/-- Collision of two real points `i < j ≤ N`: `q = j − i`, `p = ⌊ja/b⌋ − ⌊ia/b⌋`. -/
theorem caseB {a b N I J : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hIJ : Γ ⊢[PRAAx] lt I J)
    (hJN : Γ ⊢[PRAAx] le J N)
    (hbox : Γ ⊢[PRAAx] quo (rem (I * a) b * succ N) b ≐ quo (rem (J * a) b * succ N) b) :
    Γ ⊢[PRAAx] le one (monus J I) ⋏ (le (monus J I) N ⋏
      le (succ N * dist (monus J I * a) (monus (quo (J * a) b) (quo (I * a) b) * b)) b) := by
  have eJ := eq_add_of_le (le_of_lt hIJ)
  have eS := eq_add_of_le hIJ
  have q1 : Γ ⊢[PRAAx] le one (monus J I) := by
    refine le_of_eq_add (d := monus J (succ I)) ?_
    have h₁ := natEq eJ; have h₂ := natEq eS
    apply deriveNat; ipra_simps
    linear_combination -h₁ + h₂
  have q2 : Γ ⊢[PRAAx] le (monus J I) N := le_trans (le_of_eq_add (d := I) (eJ.eqTrans (add_comm _ _))) hJN
  have hQ := quo_mono hb (le_mul_mono (le_of_lt hIJ) (le_refl a))
  have idt := ident eJ (eq_add_of_le hQ) (div_eq (j := I * a) hb) (div_eq (j := J * a) hb)
  have d₁ := div_eq (j := rem (I * a) b * succ N) hb
  have d₂ := div_eq (j := rem (J * a) b * succ N) hb
  refine .andI q1 (.andI q2 ?_)
  refine .orE (lt_or_le (rem (J * a) b) (rem (I * a) b)) ?_ ?_
  · -- `y < x`: `pb = ta + (x − y)`.
    have ed := eq_add_of_le (le_of_lt (Prf.hyp0 : (lt (rem (J * a) b) (rem (I * a) b) :: Γ) ⊢[PRAAx] _))
    have hd : (lt (rem (J * a) b) (rem (I * a) b) :: Γ) ⊢[PRAAx]
        dist (monus J I * a) (monus (quo (J * a) b) (quo (I * a) b) * b) ≐ monus (rem (I * a) b) (rem (J * a) b) := by
      refine dist_l ?_
      have h₁ := natEq (idt.wk (ψ := lt (rem (J * a) b) (rem (I * a) b))); have h₂ := natEq ed
      apply deriveNat; ipra_simps
      linear_combination -h₁ + h₂
    have gb := gap_bound ed d₁.wk d₂.wk hbox.wk (eq_add_of_le (rem_lt' hb.wk (rem (I * a) b * succ N)))
    exact le_congr (congrMul (.eqRefl _) hd.eqSymm) (.eqRefl _) (le_of_eq_add gb)
  · -- `x ≤ y`: `ta = pb + (y − x)`.
    have ed := eq_add_of_le (Prf.hyp0 : (le (rem (I * a) b) (rem (J * a) b) :: Γ) ⊢[PRAAx] _)
    have hd : (le (rem (I * a) b) (rem (J * a) b) :: Γ) ⊢[PRAAx]
        dist (monus J I * a) (monus (quo (J * a) b) (quo (I * a) b) * b) ≐ monus (rem (J * a) b) (rem (I * a) b) := by
      refine dist_r ?_
      have h₁ := natEq (idt.wk (ψ := le (rem (I * a) b) (rem (J * a) b))); have h₂ := natEq ed
      apply deriveNat; ipra_simps
      linear_combination h₁ + h₂
    have gb := gap_bound ed d₂.wk d₁.wk hbox.wk.eqSymm (eq_add_of_le (rem_lt' hb.wk (rem (J * a) b * succ N)))
    exact le_congr (congrMul (.eqRefl _) hd.eqSymm) (.eqRefl _) (le_of_eq_add gb)

/-! ## Assembly -/

alias ne_of_lt' := Common.ne_of_lt

theorem sel_one {c X Y : PTm n} (h : Γ ⊢[PRAAx] c ≐ one) : Γ ⊢[PRAAx] c * X + monus one c * Y ≐ X := by
  refine (congrAdd (congrMul h (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) h).eqTrans
    ((succ_monus_succ _ _).eqTrans (monus_zero _))) (.eqRefl _))).eqTrans ?_
  ipra_ring

theorem sel_zero {c X Y : PTm n} (h : Γ ⊢[PRAAx] c ≐ zero) : Γ ⊢[PRAAx] c * X + monus one c * Y ≐ Y := by
  refine (congrAdd (congrMul h (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) h).eqTrans
    (monus_zero _)) (.eqRefl _))).eqTrans ?_
  ipra_ring

/-- The approximation property `1 ≤ q ≤ N`, `(N+1)·|qa − pb| ≤ b`. -/
abbrev dirF (q p a b N : PTm n) : Fm PTm n :=
  le one q ⋏ (le q N ⋏ le (succ N * dist (q * a) (p * b)) b)

theorem transport {q Q p P a b N : PTm n} (hq : Γ ⊢[PRAAx] q ≐ Q) (hp : Γ ⊢[PRAAx] p ≐ P)
    (h : Γ ⊢[PRAAx] dirF Q P a b N) : Γ ⊢[PRAAx] dirF q p a b N :=
  .andI (le_congr (.eqRefl _) hq.eqSymm (Prf.andE₁ h))
    (.andI (le_congr hq.eqSymm (.eqRefl _) (Prf.andE₁ (Prf.andE₂ h)))
      (le_congr (congrMul (.eqRefl _) (congrDist (congrMul hq.eqSymm (.eqRefl _)) (congrMul hp.eqSymm (.eqRefl _))))
        (.eqRefl _) (Prf.andE₂ (Prf.andE₂ h))))

/-- The colliding indices `i₀ < j₀ ≤ N + 1` from the pigeonhole search. -/
abbrev wI (a b N : PTm n) : PTm n := Pigeonhole.phpI boxB (succ N) (code a b N)
abbrev wJ (a b N : PTm n) : PTm n := Pigeonhole.phpJ boxB (succ N) (code a b N)

/-- The denominator `q`: `i₀` if `j₀` is the extra point, else `j₀ − i₀`. -/
abbrev qD (a b N : PTm n) : PTm n :=
  eqb (wJ a b N) (succ N) * wI a b N + monus one (eqb (wJ a b N) (succ N)) * monus (wJ a b N) (wI a b N)

/-- The numerator `p`. -/
abbrev pD (a b N : PTm n) : PTm n :=
  eqb (wJ a b N) (succ N) * succ (quo (wI a b N * a) b) +
    monus one (eqb (wJ a b N) (succ N)) * monus (quo (wJ a b N * a) b) (quo (wI a b N * a) b)

theorem dirichlet_at {a b N : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] dirF (qD a b N) (pD a b N) a b N := by
  have php := Pigeonhole.pigeonhole (box_range (a := a) (N := N) hb)
  have hIJ : Γ ⊢[PRAAx] lt (wI a b N) (wJ a b N) := Prf.andE₁ php
  have hJle : Γ ⊢[PRAAx] le (wJ a b N) (succ N) := Prf.andE₁ (Prf.andE₂ php)
  have hbx : Γ ⊢[PRAAx] box (wI a b N) a b N ≐ box (wJ a b N) a b N :=
    (at_code _ a b N).eqSymm.eqTrans ((Prf.andE₂ (Prf.andE₂ php)).eqTrans (at_code _ a b N))
  have hIlt : Γ ⊢[PRAAx] lt (wI a b N) (succ N) := lt_of_lt_of_le hIJ hJle
  have bI := box_below (a := a) (b := b) (ne_of_lt' hIlt)
  refine .orE (lt_or_eq_of_le hJle) ?_ ?_
  · have hlt : (lt (wJ a b N) (succ N) :: Γ) ⊢[PRAAx] lt (wJ a b N) (succ N) := Prf.hyp0
    have bJ := box_below (a := a) (b := b) (ne_of_lt' hlt)
    have r := caseB (a := a) hb.wk hIJ.wk ((succ_monus_succ _ _).eqSymm.eqTrans hlt)
      (bI.wk.eqSymm.eqTrans (hbx.wk.eqTrans bJ))
    exact transport (sel_zero (eqb_of_ne (ne_of_lt' hlt))) (sel_zero (eqb_of_ne (ne_of_lt' hlt))) r
  · have hE : ((wJ a b N ≐ succ N) :: Γ) ⊢[PRAAx] wJ a b N ≐ succ N := Prf.hyp0
    have hbox := bI.wk.eqSymm.eqTrans (hbx.wk.eqTrans ((congrBoxK hE).eqTrans (box_at_top a b N)))
    have r := caseA hb.wk hN.wk hIlt.wk hbox
    exact transport (sel_one (eqb_of_eq hE)) (sel_one (eqb_of_eq hE)) r

/-- `thm:dir-rational`: variables `0 = a`, `1 = b − 1`, `2 = N − 1`. -/
abbrev dirichletFormula : Fm PTm 3 :=
  dirF (qD (var 0) (succ (var 1)) (succ (var 2))) (pD (var 0) (succ (var 1)) (succ (var 2)))
    (var 0) (succ (var 1)) (succ (var 2))

theorem dirichlet_rational : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 dirichletFormula :=
  closeUniv 3 (dirichlet_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet
