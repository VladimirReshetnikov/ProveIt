import IPRADerivations.DiophantineNumberTheory.KhinchinScaleCount
import IPRADerivations.Foundations.IntervalOverlap
import IPRADerivations.Foundations.SeparatedCount

/-!
# The overlap of two Khinchin scales (`hurwitz_khinchin_ipra`, (K9))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K9): "Fix `k < ℓ` and one interval
`I` of `E_k(J)`. A radius-`r_ℓ` interval meeting `I` has its center in an interval of length `|I| + 2r_ℓ`.
Separation at scale `ℓ` bounds the number of such centers by `(|I| + 2r_ℓ)4^ℓ + 1`. Multiplying by `2r_ℓ` …
Sum this over the disjoint intervals of `E_k(J)`."

Both scales live on one grid `T = R! G` (`Q_k, Q_ℓ ≤ R`): the members of scale `k` (width `w_k`, parameter
`y_k`) and of scale `ℓ` (width `w_ℓ`, `y_ℓ`) are those of `KhinchinScale`. For `s ≥ 1` with `Q_ℓ² s ≤ T`
(the separation of scale `ℓ`, `KhinchinScale.sep_or`):

* `cnt_meet`: one active interval `I = [A, A + w_k)` meets scale-`ℓ` intervals of total length at most
  `w_ℓ (⌊(w_k + w_ℓ)/s⌋ + 1)`. The meeting active members, shifted by `w_ℓ`, lie in `[A, A + w_k + w_ℓ]`
  (`win_pt`) and are `s`-separated (`pair_pt`), so `Foundations/SeparatedCount.sep_count` applies;
* `empty_zero`: an inactive (empty) interval meets nothing;
* `overlap_bound`: `|E_k ∩ E_ℓ| ≤ w_ℓ (⌊(w_k + w_ℓ)/s⌋ + 1) · #{active members of scale k}`, via
  `Foundations/IntervalOverlap.overlap_split`.

With `T = Q_ℓ² s`, `w = 2r T` this is `|E_k ∩ E_ℓ| ≤ 2r_ℓ ((2r_k + 2r_ℓ)4^ℓ + 1) #𝓡_k`, and with (K3)
`#𝓡_k ≤ L4^k` it gives (K9): `|E_k ∩ E_ℓ| ≤ (L/16) t_k t_ℓ + (5L/16) 4^{k−ℓ} t_ℓ`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinOverlap

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit shift_inst2')
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.IntervalAdditive (sg_of_le_one)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB inst2_loB inst2_hiB acB pos_of_sg_one lt_of_monus_pos
  absurd_one_zero')
open LeanProofs.IPRA.Foundations.IntervalIntersection (meet)
open LeanProofs.IPRA.Foundations.IntervalOverlap (mtB inst2_mtB locB inst2_locB inter overlap_split)
open LeanProofs.IPRA.Foundations.SeparatedCount (sep_count)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK qE AE actE A_at act_at sep_or)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Bits -/

theorem inst2_acB (c : PTm 2) (i x : PTm n) : inst2 (acB c) i x = sg (inst2 c i x) := by
  simp [inst2, Signum.sg]

/-- `1 ≤ X [a]` gives `1 ≤ X` and `[a] = 1`. -/
theorem peel {X a : PTm n} (h : Γ ⊢[PRAAx] le one (X * sg a)) : Γ ⊢[PRAAx] le one X ⋏ (sg a ≐ one) := by
  have h1 := sg_le_one (Γ := Γ) a
  refine .andI (by ipra_le sl h + 𝔞 X * sl h1) ?_
  refine .orE (sg_bit (Γ := Γ) a) ?_ Prf.hyp0
  have hz : ((sg a ≐ zero) :: Γ) ⊢[PRAAx] le one zero :=
    le_congr (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) h.wk
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- A product of four bits is a bit. -/
theorem bit4 (a b c d : PTm n) : Γ ⊢[PRAAx] sg (sg a * sg b * sg c * sg d) ≐ sg a * sg b * sg c * sg d := by
  have h1 := sg_le_one (Γ := Γ) a
  have h2 := sg_le_one (Γ := Γ) b
  have h3 := sg_le_one (Γ := Γ) c
  have h4 := sg_le_one (Γ := Γ) d
  refine sg_of_le_one ?_
  ipra_le sl h1 + 𝔞 (sg a) * sl h2 + 𝔞 (sg a) * 𝔞 (sg b) * sl h3 + 𝔞 (sg a) * 𝔞 (sg b) * 𝔞 (sg c) * sl h4

/-! ## The meeting members of scale `ℓ` as bodies over `W = ⟨lo, ⟨hi, ⟨w_ℓ, y_ℓ⟩⟩⟩` -/

/-- `⟨lo, ⟨hi, ⟨w, y⟩⟩⟩`. -/
abbrev Wt (lo hi w y : PTm n) : PTm n := pairT lo (pairT hi (pairT w y))

/-- `f(j, y)` read from `W`. -/
def lift3 (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (sndT (sndT (var 1)))] f

theorem sub3 (f : PTm 2) (j W : PTm n) :
    Syn.subst ![j, W] (lift3 f) = Syn.subst ![j, sndT (sndT (sndT W))] f := by
  simp only [lift3, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

/-- The shifted point `A'_j + w_ℓ`. -/
def A2 : PTm 2 := lift3 AK + fstT (sndT (sndT (var 1)))

/-- `meet(I, J_j) [act'_j]`. -/
def c2 : PTm 2 :=
  meet (fstT (var 1)) (fstT (sndT (var 1))) (lift3 AK) (lift3 AK + sg (lift3 actK) * fstT (sndT (sndT (var 1)))) *
    sg (lift3 actK)

theorem inst2_A2 (j W : PTm n) :
    inst2 A2 j W = inst2 AK j (sndT (sndT (sndT W))) + fstT (sndT (sndT W)) := by
  simp only [A2, inst2, PTm.subst_add]
  rw [sub3]
  simp

theorem inst2_c2 (j W : PTm n) : inst2 c2 j W =
    meet (fstT W) (fstT (sndT W)) (inst2 AK j (sndT (sndT (sndT W))))
        (inst2 AK j (sndT (sndT (sndT W))) + sg (inst2 actK j (sndT (sndT (sndT W)))) * fstT (sndT (sndT W))) *
      sg (inst2 actK j (sndT (sndT (sndT W)))) := by
  ipra_ind_simp [c2, inst2, Signum.sg]
  rw [sub3, sub3]
  simp

theorem congrMeet {lo lo' hi hi' a a' b b' : PTm n} (h1 : Γ ⊢[PRAAx] lo ≐ lo') (h2 : Γ ⊢[PRAAx] hi ≐ hi')
    (h3 : Γ ⊢[PRAAx] a ≐ a') (h4 : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] meet lo hi a b ≐ meet lo' hi' a' b' :=
  congrMul (congrMul (congrSg (congrMonus h2 h1)) (congrSg (congrMonus h2 h3))) (congrSg (congrMonus h4 h1))

/-- The projections of `W`. -/
theorem projW (lo hi w y : PTm n) :
    (Γ ⊢[PRAAx] fstT (Wt lo hi w y) ≐ lo) ∧ (Γ ⊢[PRAAx] fstT (sndT (Wt lo hi w y)) ≐ hi) ∧
      (Γ ⊢[PRAAx] fstT (sndT (sndT (Wt lo hi w y))) ≐ w) ∧ (Γ ⊢[PRAAx] sndT (sndT (sndT (Wt lo hi w y))) ≐ y) := by
  have s1 : Γ ⊢[PRAAx] sndT (Wt lo hi w y) ≐ pairT hi (pairT w y) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Wt lo hi w y)) ≐ pairT w y := s1.sndE
  exact ⟨fst_pair _ _, s1.fstE, s2.fstE,
    s2.sndE⟩

theorem c2_at (i lo hi w y : PTm n) :
    Γ ⊢[PRAAx] inst2 c2 i (Wt lo hi w y) ≐
      meet lo hi (inst2 AK i y) (inst2 AK i y + sg (inst2 actK i y) * w) * sg (inst2 actK i y) := by
  rw [inst2_c2]
  obtain ⟨p1, p2, p3, p4⟩ := projW (Γ := Γ) lo hi w y
  have eA := congrInst2 AK (.eqRefl i) p4
  have eS := congrSg (congrInst2 actK (.eqRefl i) p4)
  exact congrMul (congrMeet p1 p2 eA (congrAdd eA (congrMul eS p3))) eS

theorem A2_at (i lo hi w y : PTm n) : Γ ⊢[PRAAx] inst2 A2 i (Wt lo hi w y) ≐ inst2 AK i y + w := by
  rw [inst2_A2]
  obtain ⟨_, _, p3, p4⟩ := projW (Γ := Γ) lo hi w y
  exact congrAdd (congrInst2 AK (.eqRefl i) p4) p3

/-- A scale-`ℓ` length term is `w_ℓ · meet [act']`. -/
theorem mt_c2 (j W : PTm n) :
    Γ ⊢[PRAAx] inst2 (mtB (loB AK) (hiB AK actK)) j W ≐ fstT (sndT (sndT W)) * inst2 c2 j W := by
  rw [inst2_mtB, inst2_loB, inst2_hiB, inst2_c2]
  refine (congrMul (.eqRefl _) (add_monus' _ _)).eqTrans ?_
  ipra_ring

theorem c2_bit (j W : PTm n) : Γ ⊢[PRAAx] sg (inst2 c2 j W) ≐ inst2 c2 j W := by
  rw [inst2_c2]; exact bit4 _ _ _ _

/-! ## Window and separation of the meeting members -/

/-- A meeting active member, shifted by `w_ℓ`, lies in `[lo, lo + w_k + w_ℓ]`. -/
theorem win_core {lo hi wk wl A' t : PTm n} (hhi : Γ ⊢[PRAAx] hi ≐ lo + wk) :
    Γ ⊢[PRAAx] (sg (meet lo hi A' (A' + sg t * wl) * sg t) ≐ one) ⟶
      (le lo (A' + wl) ⋏ le (A' + wl) (lo + (wk + wl))) := by
  refine .impI ?_
  let Θ : List (Fm PTm n) := (sg (meet lo hi A' (A' + sg t * wl) * sg t) ≐ one) :: Γ
  have hp := pos_of_sg_one (Prf.hyp0 : Θ ⊢[PRAAx] sg (meet lo hi A' (A' + sg t * wl) * sg t) ≐ one)
  have q1 := peel hp
  have q2 := peel (Prf.andE₁ q1)
  have q3 := peel (Prf.andE₁ q2)
  have hlt : Θ ⊢[PRAAx] lt A' hi := lt_of_monus_pos (pos_of_sg_one (Prf.andE₂ q3))
  have h3 : Θ ⊢[PRAAx] lt lo (A' + sg t * wl) := lt_of_monus_pos (pos_of_sg_one (Prf.andE₂ q2))
  have et := natEq (Prf.andE₂ q1)
  have eh := natEq (hhi.wk : Θ ⊢[PRAAx] hi ≐ lo + wk)
  exact .andI (by ipra_le sl h3 + 1 with 𝔞 wl * et) (by ipra_le sl hlt + 1 with eh)

theorem win_pt {i lo hi wk wl y : PTm n} (hhi : Γ ⊢[PRAAx] hi ≐ lo + wk) :
    Γ ⊢[PRAAx] (sg (inst2 c2 i (Wt lo hi wl y)) ≐ one) ⟶
      (le lo (inst2 A2 i (Wt lo hi wl y)) ⋏ le (inst2 A2 i (Wt lo hi wl y)) (lo + (wk + wl))) := by
  refine .impI ?_
  let Θ : List (Fm PTm n) := (sg (inst2 c2 i (Wt lo hi wl y)) ≐ one) :: Γ
  have hc : Θ ⊢[PRAAx] sg (meet lo hi (inst2 AK i y) (inst2 AK i y + sg (inst2 actK i y) * wl) * sg (inst2 actK i y)) ≐ one :=
    (congrSg (c2_at i lo hi wl y)).eqSymm.eqTrans Prf.hyp0
  have h := Prf.impE (win_core (t := inst2 actK i y) (A' := inst2 AK i y) (wl := wl) hhi.wk) hc
  have ha : Θ ⊢[PRAAx] inst2 A2 i (Wt lo hi wl y) ≐ inst2 AK i y + wl := A2_at _ _ _ _ _
  exact .andI (le_congr (.eqRefl _) ha.eqSymm (Prf.andE₁ h)) (le_congr ha.eqSymm (.eqRefl _) (Prf.andE₂ h))

/-- Two meeting active members of scale `ℓ` are `s`-separated. -/
theorem pair_pt {lo hi wk wl M Ql Q'l R G α γ β s i j : PTm n} (hhi : Γ ⊢[PRAAx] hi ≐ lo + wk)
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQl : Γ ⊢[PRAAx] le Q'l Ql) (hQR : Γ ⊢[PRAAx] le Ql R)
    (hw : Γ ⊢[PRAAx] le (Ql * Ql * s) (fact R * G)) (hij : Γ ⊢[PRAAx] lt i j)
    (hj : Γ ⊢[PRAAx] lt j (monus Ql Q'l * M)) :
    Γ ⊢[PRAAx] (sg (inst2 c2 i (Wt lo hi wl (tup M Q'l (fact R * G) α γ β))) ≐ one) ⟶
      ((sg (inst2 c2 j (Wt lo hi wl (tup M Q'l (fact R * G) α γ β))) ≐ one) ⟶
        ((le lo (inst2 A2 i (Wt lo hi wl (tup M Q'l (fact R * G) α γ β))) ⋏
            le lo (inst2 A2 j (Wt lo hi wl (tup M Q'l (fact R * G) α γ β)))) ⋏
          (le (inst2 A2 i (Wt lo hi wl (tup M Q'l (fact R * G) α γ β)) + s)
              (inst2 A2 j (Wt lo hi wl (tup M Q'l (fact R * G) α γ β))) ⋎
            le (inst2 A2 j (Wt lo hi wl (tup M Q'l (fact R * G) α γ β)) + s)
              (inst2 A2 i (Wt lo hi wl (tup M Q'l (fact R * G) α γ β)))))) := by
  refine .impI (.impI ?_)
  let y := tup M Q'l (fact R * G) α γ β
  let Θ : List (Fm PTm n) := (sg (inst2 c2 j (Wt lo hi wl y)) ≐ one) :: (sg (inst2 c2 i (Wt lo hi wl y)) ≐ one) :: Γ
  have hi1 : Θ ⊢[PRAAx] sg (inst2 c2 i (Wt lo hi wl y)) ≐ one := Prf.hyp1
  have hj1 : Θ ⊢[PRAAx] sg (inst2 c2 j (Wt lo hi wl y)) ≐ one := Prf.hyp0
  have wi := Prf.impE (win_pt (i := i) (wl := wl) (y := y) hhi.wk.wk) hi1
  have wj := Prf.impE (win_pt (i := j) (wl := wl) (y := y) hhi.wk.wk) hj1
  have ti : Θ ⊢[PRAAx] sg (inst2 actK i y) ≐ one :=
    Prf.andE₂ (peel (pos_of_sg_one ((congrSg (c2_at i lo hi wl y)).eqSymm.eqTrans hi1)))
  have tj : Θ ⊢[PRAAx] sg (inst2 actK j y) ≐ one :=
    Prf.andE₂ (peel (pos_of_sg_one ((congrSg (c2_at j lo hi wl y)).eqSymm.eqTrans hj1)))
  have a1 : Θ ⊢[PRAAx] sg (actE Q'l M α γ β i) ≐ one := (congrSg (act_at i M Q'l (fact R * G) α γ β)).eqSymm.eqTrans ti
  have a2 : Θ ⊢[PRAAx] sg (actE Q'l M α γ β j) ≐ one := (congrSg (act_at j M Q'l (fact R * G) α γ β)).eqSymm.eqTrans tj
  have sp := sep_or (w := s) hM.wk.wk hQl.wk.wk hQR.wk.wk hw.wk.wk hij.wk.wk hj.wk.wk a1 a2
  have Ei : Θ ⊢[PRAAx] inst2 A2 i (Wt lo hi wl y) ≐ AE Q'l (fact R * G) M i + wl :=
    (A2_at i lo hi wl y).eqTrans (congrAdd (A_at i M Q'l (fact R * G) α γ β) (.eqRefl _))
  have Ej : Θ ⊢[PRAAx] inst2 A2 j (Wt lo hi wl y) ≐ AE Q'l (fact R * G) M j + wl :=
    (A2_at j lo hi wl y).eqTrans (congrAdd (A_at j M Q'l (fact R * G) α γ β) (.eqRefl _))
  refine .andI (.andI (Prf.andE₁ wi) (Prf.andE₁ wj)) ?_
  refine .orE sp ?_ ?_
  · let Θ' : List (Fm PTm n) := le (AE Q'l (fact R * G) M i + s) (AE Q'l (fact R * G) M j) :: Θ
    have h : Θ' ⊢[PRAAx] le (AE Q'l (fact R * G) M i + s) (AE Q'l (fact R * G) M j) := Prf.hyp0
    have ei := natEq (Ei.wk : Θ' ⊢[PRAAx] _)
    have ej := natEq (Ej.wk : Θ' ⊢[PRAAx] _)
    exact .orI₁ (by ipra_le sl h with ej - ei)
  · let Θ' : List (Fm PTm n) := le (AE Q'l (fact R * G) M j + s) (AE Q'l (fact R * G) M i) :: Θ
    have h : Θ' ⊢[PRAAx] le (AE Q'l (fact R * G) M j + s) (AE Q'l (fact R * G) M i) := Prf.hyp0
    have ei := natEq (Ei.wk : Θ' ⊢[PRAAx] _)
    have ej := natEq (Ej.wk : Θ' ⊢[PRAAx] _)
    exact .orI₂ (by ipra_le sl h with ei - ej)

/-! ## One interval of scale `k` against scale `ℓ` -/

/-- One active interval `[lo, lo + w_k)` meets scale-`ℓ` intervals of total length at most
`w_ℓ (⌊(w_k + w_ℓ)/s⌋ + 1)`. -/
theorem cnt_meet {lo wk wl M Ql Q'l R G α γ β s : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hQl : Γ ⊢[PRAAx] le Q'l Ql) (hQR : Γ ⊢[PRAAx] le Ql R) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hw : Γ ⊢[PRAAx] le (Ql * Ql * s) (fact R * G)) :
    Γ ⊢[PRAAx] le (ap2 (sumF (mtB (loB AK) (hiB AK actK))) (monus Ql Q'l * M)
        (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β))) (wl * succ (quo (wk + wl) s)) := by
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (mtB (loB AK) (hiB AK actK))) (monus Ql Q'l * M)
      (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β)) ≐
      wl * ap2 (sumF (acB c2)) (monus Ql Q'l * M) (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β)) = Wt (Syn.shift lo) (Syn.shift (lo + wk))
      (Syn.shift wl) (Syn.shift (tup M Q'l (fact R * G) α γ β)) by simp only [Wt, shift_pairT]]
    rw [inst2_acB]
    obtain ⟨_, _, p3, _⟩ := projW (Γ := lt (var 0) (Syn.shift (monus Ql Q'l * M)) :: Γ.map Fm.shift)
      (Syn.shift lo) (Syn.shift (lo + wk)) (Syn.shift wl) (Syn.shift (tup M Q'l (fact R * G) α γ β))
    exact (mt_c2 _ _).eqTrans (congrMul p3 (c2_bit _ _).eqSymm)
  have hM1 := Common.pos_shift hM
  have hQl1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Q'l) (Syn.shift Ql) := by
    simpa [Fm.shift, Syn.shift] using hQl.shift
  have hQR1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Ql) (Syn.shift R) := by
    simpa [Fm.shift, Syn.shift] using hQR.shift
  have hw1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Ql * Syn.shift Ql * Syn.shift s)
      (fact (Syn.shift R) * Syn.shift G) := by
    simpa [Fm.shift, Syn.shift] using hw.shift
  have e2 := sep_count A2 c2 (N := monus Ql Q'l * M) (a := lo) (s := s) (lam := wk + wl)
    (y := Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β)) hs ?_ ?_
  · exact le_congr e1.eqSymm (.eqRefl _) (by ipra_le 𝔞 wl * sl e2)
  · -- separation of the meeting members
    intro Δ i j hsub hij hj
    have hM2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift M) ≐
        succ (pred (Syn.shift (Syn.shift M))) := by simpa [Fm.shift, Syn.shift] using hM1.shift
    have hQl2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Q'l)) (Syn.shift (Syn.shift Ql)) := by
      simpa [Fm.shift, Syn.shift] using hQl1.shift
    have hQR2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Ql)) (Syn.shift (Syn.shift R)) := by
      simpa [Fm.shift, Syn.shift] using hQR1.shift
    have hw2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Ql) * Syn.shift (Syn.shift Ql) *
        Syn.shift (Syn.shift s)) (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G)) := by
      simpa [Fm.shift, Syn.shift] using hw1.shift
    rw [show Syn.shift (Syn.shift (monus Ql Q'l * M)) = monus (Syn.shift (Syn.shift Ql)) (Syn.shift (Syn.shift Q'l)) *
      Syn.shift (Syn.shift M) by simp [Syn.shift]] at hj
    rw [show Syn.shift (Syn.shift (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β))) =
      Wt (Syn.shift (Syn.shift lo)) (Syn.shift (Syn.shift lo) + Syn.shift (Syn.shift wk)) (Syn.shift (Syn.shift wl))
        (tup (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift Q'l)) (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G))
          (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ)) (Syn.shift (Syn.shift β))) by simp [Syn.shift]]
    exact pair_pt (.eqRefl _) (hM2.weaken hsub) (hQl2.weaken hsub) (hQR2.weaken hsub) (hw2.weaken hsub) hij hj
  · -- the window
    intro Δ i hsub hi
    rw [show Syn.shift (Wt lo (lo + wk) wl (tup M Q'l (fact R * G) α γ β)) =
      Wt (Syn.shift lo) (Syn.shift lo + Syn.shift wk) (Syn.shift wl) (Syn.shift (tup M Q'l (fact R * G) α γ β)) by
        simp [Syn.shift],
      show Syn.shift (wk + wl) = Syn.shift wk + Syn.shift wl by simp [Syn.shift]]
    exact win_pt (.eqRefl _)

/-- An empty interval meets nothing. -/
theorem empty_zero (A wl y K2 : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (mtB (loB AK) (hiB AK actK))) K2 (Wt A A wl y) ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (Wt A A wl y) = Wt (Syn.shift A) (Syn.shift A) (Syn.shift wl) (Syn.shift y) by
    simp only [Wt, shift_pairT]]
  refine (mt_c2 _ _).eqTrans ((congrMul (.eqRefl _) (c2_at _ _ _ _ _)).eqTrans ?_)
  have z := (congrSg (monus_self (Γ := lt (var 0) (Syn.shift K2) :: Γ.map Fm.shift) (Syn.shift A))).eqTrans sg_zero
  exact (congrMul (.eqRefl _) ((congrMul (congrMul (congrMul z (.eqRefl _)) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (congrMul (zero_mul _) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))))).eqTrans (mul_zero _)

/-! ## The overlap of the two scales -/

/-- `C · [act_j]` over `0 = j`, `1 = ⟨C, y⟩`. -/
def hB : PTm 2 := fstT (var 1) * sg (Syn.subst ![var 0, sndT (var 1)] actK)

theorem inst2_hB (j z : PTm n) : inst2 hB j z = fstT z * sg (inst2 actK j (sndT z)) := by
  simp only [hB, inst2, PTm.subst_mul, Signum.sg, PTm.subst_monus]
  rw [show Syn.subst ![j, z] (Syn.subst ![var 0, sndT (var 1)] actK) = Syn.subst ![j, sndT z] actK by
    rw [Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp]
  simp

/-- One member of scale `k` against scale `ℓ`: at most `C [act_j]`, `C = w_ℓ (⌊(w_k + w_ℓ)/s⌋ + 1)`. -/
theorem loc_pt {j K2 wk yk wl M Ql Q'l R G α γ β s : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hQl : Γ ⊢[PRAAx] le Q'l Ql) (hQR : Γ ⊢[PRAAx] le Ql R) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hw : Γ ⊢[PRAAx] le (Ql * Ql * s) (fact R * G)) (hK2 : Γ ⊢[PRAAx] K2 ≐ monus Ql Q'l * M) :
    Γ ⊢[PRAAx] le (inst2 (locB (loB AK) (hiB AK actK) (loB AK) (hiB AK actK)) j
        (pairT K2 (pairT (pairT wk yk) (pairT wl (tup M Q'l (fact R * G) α γ β)))))
      (inst2 hB j (pairT (wl * succ (quo (wk + wl) s)) yk)) := by
  rw [inst2_locB, inst2_hB, inst2_loB, inst2_hiB]
  let yl := tup M Q'l (fact R * G) α γ β
  let Z := pairT K2 (pairT (pairT wk yk) (pairT wl yl))
  have sZ : Γ ⊢[PRAAx] sndT Z ≐ pairT (pairT wk yk) (pairT wl yl) := snd_pair _ _
  have hK : Γ ⊢[PRAAx] fstT Z ≐ monus Ql Q'l * M := (fst_pair _ _).eqTrans hK2
  have hx1 : Γ ⊢[PRAAx] fstT (sndT Z) ≐ pairT wk yk := sZ.fstE
  have hx2 : Γ ⊢[PRAAx] sndT (sndT Z) ≐ pairT wl yl := sZ.sndE
  have hy : Γ ⊢[PRAAx] sndT (fstT (sndT Z)) ≐ yk := hx1.sndE
  have hwk : Γ ⊢[PRAAx] fstT (fstT (sndT Z)) ≐ wk := hx1.fstE
  have eAj := congrInst2 AK (.eqRefl j) hy
  have eSj := congrSg (congrInst2 actK (.eqRefl j) hy)
  have eL : Γ ⊢[PRAAx] ap2 (sumF (mtB (loB AK) (hiB AK actK))) (fstT Z)
      (pairT (inst2 AK j (sndT (fstT (sndT Z))))
        (pairT (inst2 AK j (sndT (fstT (sndT Z))) + sg (inst2 actK j (sndT (fstT (sndT Z)))) * fstT (fstT (sndT Z)))
          (sndT (sndT Z)))) ≐
      ap2 (sumF (mtB (loB AK) (hiB AK actK))) (monus Ql Q'l * M)
        (Wt (inst2 AK j yk) (inst2 AK j yk + sg (inst2 actK j yk) * wk) wl yl) :=
    congrAp2 (sumF (mtB (loB AK) (hiB AK actK))) hK
      (congrPairT eAj (congrPairT (congrAdd eAj (congrMul eSj hwk)) hx2))
  have eR : Γ ⊢[PRAAx] fstT (pairT (wl * succ (quo (wk + wl) s)) yk) *
      sg (inst2 actK j (sndT (pairT (wl * succ (quo (wk + wl) s)) yk))) ≐
      wl * succ (quo (wk + wl) s) * sg (inst2 actK j yk) :=
    congrMul (fst_pair _ _) (congrSg (congrInst2 actK (.eqRefl _) (snd_pair _ _)))
  refine le_congr eL.eqSymm eR.eqSymm ?_
  refine .orE (sg_bit (Γ := Γ) (inst2 actK j yk)) ?_ ?_
  · -- an inactive member: its interval is empty
    let Θ : List (Fm PTm n) := (sg (inst2 actK j yk) ≐ zero) :: Γ
    have h0 : Θ ⊢[PRAAx] sg (inst2 actK j yk) ≐ zero := Prf.hyp0
    have eh : Θ ⊢[PRAAx] inst2 AK j yk + sg (inst2 actK j yk) * wk ≐ inst2 AK j yk :=
      (congrAdd (.eqRefl _) ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _)
    have z : Θ ⊢[PRAAx] ap2 (sumF (mtB (loB AK) (hiB AK actK))) (monus Ql Q'l * M)
        (Wt (inst2 AK j yk) (inst2 AK j yk + sg (inst2 actK j yk) * wk) wl yl) ≐ zero :=
      (congrAp2 (sumF (mtB (loB AK) (hiB AK actK))) (.eqRefl _)
        (congrPairT (.eqRefl _) (congrPairT eh (.eqRefl _)))).eqTrans (empty_zero _ _ _ _)
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  · -- an active member
    let Θ : List (Fm PTm n) := (sg (inst2 actK j yk) ≐ one) :: Γ
    have h1 : Θ ⊢[PRAAx] sg (inst2 actK j yk) ≐ one := Prf.hyp0
    have eh : Θ ⊢[PRAAx] inst2 AK j yk + sg (inst2 actK j yk) * wk ≐ inst2 AK j yk + wk :=
      congrAdd (.eqRefl _) ((congrMul h1 (.eqRefl _)).eqTrans (one_mul _))
    have c := cnt_meet (Γ := Θ) (lo := inst2 AK j yk) (wk := wk) (wl := wl) (α := α) (γ := γ) (β := β)
      hM.wk hQl.wk hQR.wk hs.wk hw.wk
    have eC : Θ ⊢[PRAAx] wl * succ (quo (wk + wl) s) * sg (inst2 actK j yk) ≐ wl * succ (quo (wk + wl) s) :=
      (congrMul (.eqRefl _) h1).eqTrans ((mul_comm _ _).eqTrans (one_mul _))
    exact le_congr (congrAp2 (sumF (mtB (loB AK) (hiB AK actK))) (.eqRefl _)
      (congrPairT (.eqRefl _) (congrPairT eh (.eqRefl _)))).eqSymm eC.eqSymm c

/-- (K9), the exact form: on the common grid `T = R! G`, `|E_k ∩ E_ℓ|` is at most
`w_ℓ (⌊(w_k + w_ℓ)/s⌋ + 1)` times the number of active members of scale `k`. -/
theorem overlap_bound {M Qk Q'k Ql Q'l R G wk wl α γ β s T' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hQl : Γ ⊢[PRAAx] le Q'l Ql) (hQR : Γ ⊢[PRAAx] le Ql R) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hw : Γ ⊢[PRAAx] le (Ql * Ql * s) (fact R * G)) :
    Γ ⊢[PRAAx] le (inter (loB AK) (hiB AK actK) (loB AK) (hiB AK actK) T' (monus Qk Q'k * M)
        (pairT wk (tup M Q'k (fact R * G) α γ β)) (monus Ql Q'l * M) (pairT wl (tup M Q'l (fact R * G) α γ β)))
      (wl * succ (quo (wk + wl) s) *
        ap2 (sumF (acB actK)) (monus Qk Q'k * M) (tup M Q'k (fact R * G) α γ β)) := by
  refine le_trans (overlap_split _ _ _ _ T' _ _ _ _) ?_
  have eR : Γ ⊢[PRAAx] ap2 (sumF hB) (monus Qk Q'k * M) (pairT (wl * succ (quo (wk + wl) s)) (tup M Q'k (fact R * G) α γ β)) ≐
      wl * succ (quo (wk + wl) s) * ap2 (sumF (acB actK)) (monus Qk Q'k * M) (tup M Q'k (fact R * G) α γ β) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_hB, inst2_acB]
    exact congrMul (fst_pair _ _) (congrSg (congrInst2 actK (.eqRefl _) (snd_pair _ _)))
  refine le_trans ?_ (le_congr (.eqRefl _) eR (le_refl _))
  have hM1 := Common.pos_shift hM
  have hQl1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Q'l) (Syn.shift Ql) := by
    simpa [Fm.shift, Syn.shift] using hQl.shift
  have hQR1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Ql) (Syn.shift R) := by
    simpa [Fm.shift, Syn.shift] using hQR.shift
  have hs1 := Common.pos_shift hs
  have hw1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Ql * Syn.shift Ql * Syn.shift s)
      (fact (Syn.shift R) * Syn.shift G) := by
    simpa [Fm.shift, Syn.shift] using hw.shift
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (monus Qk Q'k * M)) :: Γ.map Fm.shift
  rw [show Syn.shift (pairT (monus Ql Q'l * M) (pairT (pairT wk (tup M Q'k (fact R * G) α γ β))
      (pairT wl (tup M Q'l (fact R * G) α γ β)))) =
      pairT (monus (Syn.shift Ql) (Syn.shift Q'l) * Syn.shift M)
        (pairT (pairT (Syn.shift wk) (Syn.shift (tup M Q'k (fact R * G) α γ β)))
          (pairT (Syn.shift wl) (tup (Syn.shift M) (Syn.shift Q'l) (fact (Syn.shift R) * Syn.shift G)
            (Syn.shift α) (Syn.shift γ) (Syn.shift β)))) by simp [Syn.shift],
    show Syn.shift (pairT (wl * succ (quo (wk + wl) s)) (tup M Q'k (fact R * G) α γ β)) =
      pairT (Syn.shift wl * succ (quo (Syn.shift wk + Syn.shift wl) (Syn.shift s)))
        (Syn.shift (tup M Q'k (fact R * G) α γ β)) by simp [Syn.shift]]
  exact loc_pt (hM1.wk : Θ ⊢[PRAAx] _) (hQl1.wk : Θ ⊢[PRAAx] _) (hQR1.wk : Θ ⊢[PRAAx] _) (hs1.wk : Θ ⊢[PRAAx] _)
    (hw1.wk : Θ ⊢[PRAAx] _) (.eqRefl _)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinOverlap
