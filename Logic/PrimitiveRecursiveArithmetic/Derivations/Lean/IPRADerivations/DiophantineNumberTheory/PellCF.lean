import IPRADerivations.DiophantineNumberTheory.PellCFStep
import IPRADerivations.Core.Fubini
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.CertificateTactics

/-!
# The continued fraction of `√D` and its integer invariants

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:cfinvariants`. With `a² < D < (a + 1)²`
the states `S_k = (m_k, d_k, p_{k−1}, p_{k−2}, q_{k−1}, q_{k−2})` are computed by one primitive recursion
(`St`): `S_0 = (0, 1, 1, 0, 0, 1)` and, with the digit `c_k = ⌊(a + m_k)/d_k⌋`,
  `m_{k+1} = d_k c_k − m_k`, `d_{k+1} = (D − m_{k+1}²)/d_k`, `p_k = c_k p_{k−1} + p_{k−2}`,
  `q_k = c_k q_{k−1} + q_{k−2}` (`eq:cfstep`).

* `St_zero`, `St_succ`: the defining equations, component by component;
* `red_succ`: every state from index `1` on is reduced (`PellCFStep.start_reduced`, `step_closure`);
* `exact_step`: the step is exact at every index: `d_k c_k = m_{k+1} + m_k`, `D = m_{k+1}² + d_k d_{k+1}`;
* `cf_invariants` (`lem:cfinvariants`): for every `k`,
  `p_{k−1} = m_k q_{k−1} + d_k q_{k−2}`, `D q_{k−1} = m_k p_{k−1} + d_k p_{k−2}`, and
  `p_{k−1} q_{k−2} − p_{k−2} q_{k−1} = (−1)^k` (as `p q' + [k odd] = p' q + [k even]`);
* `cf_norm` (`eq:cfnorm`): `p_{k−1}² − D q_{k−1}² = (−1)^k d_k`, as
  `p_{k−1}² + [k odd] d_k = D q_{k−1}² + [k even] d_k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellCF

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.PellCFStep
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## States -/

/-- A six-component state `⟨m, ⟨d, ⟨p, ⟨p', ⟨q, q'⟩⟩⟩⟩⟩`. -/
abbrev mk6 (m d p p' q q' : PTm n) : PTm n := pairT m (pairT d (pairT p (pairT p' (pairT q q'))))

abbrev sm (S : PTm n) : PTm n := fstT S
abbrev sd (S : PTm n) : PTm n := fstT (sndT S)
abbrev sp (S : PTm n) : PTm n := fstT (sndT (sndT S))
abbrev sp' (S : PTm n) : PTm n := fstT (sndT (sndT (sndT S)))
abbrev sq (S : PTm n) : PTm n := fstT (sndT (sndT (sndT (sndT S))))
abbrev sq' (S : PTm n) : PTm n := sndT (sndT (sndT (sndT (sndT S))))

/-- The successor state of `S` for `D`, `a`. -/
abbrev stepOf (S D a : PTm n) : PTm n :=
  mk6 (mS a (sm S) (sd S)) (PellCFStep.dS D a (sm S) (sd S)) (cD a (sm S) (sd S) * sp S + sp' S) (sp S)
    (cD a (sm S) (sd S) * sq S + sq' S) (sq S)

/-- The step body, over `0 = k`, `1 = S`, `2 = ⟨D, a⟩`. -/
abbrev stepB : PTm 3 := stepOf (var 1) (fstT (var 2)) (sndT (var 2))
abbrev initB : PTm 1 := mk6 zero one one zero zero one

/-- The state `S_k` for `D`, `a`. -/
abbrev St (k D a : PTm n) : PTm n := ap2 (rec2 initB stepB) k (pairT D a)

theorem mk6_parts (m d p p' q q' : PTm n) :
    Γ ⊢[PRAAx] (sm (mk6 m d p p' q q') ≐ m) ⋏ ((sd (mk6 m d p p' q q') ≐ d) ⋏ ((sp (mk6 m d p p' q q') ≐ p) ⋏
      ((sp' (mk6 m d p p' q q') ≐ p') ⋏ ((sq (mk6 m d p p' q q') ≐ q) ⋏ (sq' (mk6 m d p p' q q') ≐ q'))))) := by
  have s1 : Γ ⊢[PRAAx] sndT (mk6 m d p p' q q') ≐ pairT d (pairT p (pairT p' (pairT q q'))) := snd_pair _ _
  have s2 := (congrSnd s1).eqTrans (snd_pair (Γ := Γ) d (pairT p (pairT p' (pairT q q'))))
  have s3 := (congrSnd s2).eqTrans (snd_pair (Γ := Γ) p (pairT p' (pairT q q')))
  have s4 := (congrSnd s3).eqTrans (snd_pair (Γ := Γ) p' (pairT q q'))
  exact .andI (fst_pair _ _) (.andI ((congrFst s1).eqTrans (fst_pair _ _)) (.andI ((congrFst s2).eqTrans (fst_pair _ _))
    (.andI ((congrFst s3).eqTrans (fst_pair _ _)) (.andI ((congrFst s4).eqTrans (fst_pair _ _))
      ((congrSnd s4).eqTrans (snd_pair _ _))))))

theorem St_zero (D a : PTm n) : Γ ⊢[PRAAx] St zero D a ≐ mk6 zero one one zero zero one := by
  refine (rec2_zero _ _ _).eqTrans ?_
  have e : Syn.subst ![pairT D a] initB = (mk6 zero one one zero zero one : PTm n) := by simp
  rw [e]; exact .eqRefl _

/-- Congruence of the step in its parameters. -/
theorem stepOf_congr {S D D' a a' : PTm n} (hD : Γ ⊢[PRAAx] D ≐ D') (ha : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] stepOf S D a ≐ stepOf S D' a' := by
  have hc : Γ ⊢[PRAAx] cD a (sm S) (sd S) ≐ cD a' (sm S) (sd S) := congrAp2 quoF (congrAdd ha (.eqRefl _)) (.eqRefl _)
  have hm : Γ ⊢[PRAAx] mS a (sm S) (sd S) ≐ mS a' (sm S) (sd S) := congrMonus (congrMul (.eqRefl _) hc) (.eqRefl _)
  have hd : Γ ⊢[PRAAx] PellCFStep.dS D a (sm S) (sd S) ≐ PellCFStep.dS D' a' (sm S) (sd S) :=
    congrAp2 quoF (congrMonus hD (congrMul hm hm)) (.eqRefl _)
  exact congrPairT hm (congrPairT hd (congrPairT (congrAdd (congrMul hc (.eqRefl _)) (.eqRefl _))
    (congrPairT (.eqRefl _) (congrPairT (congrAdd (congrMul hc (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))))

theorem St_succ (k D a : PTm n) : Γ ⊢[PRAAx] St (succ k) D a ≐ stepOf (St k D a) D a := by
  refine (rec2_succ _ _ _ _).eqTrans ?_
  have e : Syn.subst ![k, St k D a, pairT D a] stepB = stepOf (St k D a) (fstT (pairT D a)) (sndT (pairT D a)) := by
    simp [stepOf]
  rw [e]
  exact stepOf_congr (fst_pair _ _) (snd_pair _ _)

/-! ## Components -/

abbrev M (k D a : PTm n) : PTm n := sm (St k D a)
abbrev Dd (k D a : PTm n) : PTm n := sd (St k D a)
abbrev P (k D a : PTm n) : PTm n := sp (St k D a)
abbrev P' (k D a : PTm n) : PTm n := sp' (St k D a)
abbrev Q (k D a : PTm n) : PTm n := sq (St k D a)
abbrev Q' (k D a : PTm n) : PTm n := sq' (St k D a)
abbrev C (k D a : PTm n) : PTm n := cD a (M k D a) (Dd k D a)

theorem succ_parts (k D a : PTm n) :
    Γ ⊢[PRAAx] (M (succ k) D a ≐ mS a (M k D a) (Dd k D a)) ⋏ ((Dd (succ k) D a ≐ PellCFStep.dS D a (M k D a) (Dd k D a)) ⋏
      ((P (succ k) D a ≐ C k D a * P k D a + P' k D a) ⋏ ((P' (succ k) D a ≐ P k D a) ⋏
      ((Q (succ k) D a ≐ C k D a * Q k D a + Q' k D a) ⋏ (Q' (succ k) D a ≐ Q k D a))))) := by
  have s := St_succ (Γ := Γ) k D a
  have pr := mk6_parts (Γ := Γ) (mS a (M k D a) (Dd k D a)) (PellCFStep.dS D a (M k D a) (Dd k D a))
    (C k D a * P k D a + P' k D a) (P k D a) (C k D a * Q k D a + Q' k D a) (Q k D a)
  have f1 := congrFst s
  have g1 := congrSnd s
  have g2 := congrSnd g1
  have g3 := congrSnd g2
  have g4 := congrSnd g3
  exact .andI (f1.eqTrans (Prf.andE₁ pr)) (.andI ((congrFst g1).eqTrans (Prf.andE₁ (Prf.andE₂ pr)))
    (.andI ((congrFst g2).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ pr))))
    (.andI ((congrFst g3).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr)))))
    (.andI ((congrFst g4).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr))))))
      ((congrSnd g4).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr))))))))))

theorem zero_parts (D a : PTm n) :
    Γ ⊢[PRAAx] (M zero D a ≐ zero) ⋏ ((Dd zero D a ≐ one) ⋏ ((P zero D a ≐ one) ⋏ ((P' zero D a ≐ zero) ⋏
      ((Q zero D a ≐ zero) ⋏ (Q' zero D a ≐ one))))) := by
  have s := St_zero (Γ := Γ) D a
  have pr := mk6_parts (Γ := Γ) (zero : PTm n) one one zero zero one
  have g1 := congrSnd s
  have g2 := congrSnd g1
  have g3 := congrSnd g2
  have g4 := congrSnd g3
  exact .andI ((congrFst s).eqTrans (Prf.andE₁ pr)) (.andI ((congrFst g1).eqTrans (Prf.andE₁ (Prf.andE₂ pr)))
    (.andI ((congrFst g2).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ pr))))
    (.andI ((congrFst g3).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr)))))
    (.andI ((congrFst g4).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr))))))
      ((congrSnd g4).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ pr))))))))))

/-! ## Reducedness and exactness -/

theorem cD_congr {a m m' d d' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] cD a m d ≐ cD a m' d' := congrAp2 quoF (congrAdd (.eqRefl _) hm) hd
theorem mS_congr {a m m' d d' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] mS a m d ≐ mS a m' d' := congrMonus (congrMul hd (cD_congr hm hd)) hm
theorem dS_congr {D a m m' d d' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] PellCFStep.dS D a m d ≐ PellCFStep.dS D a m' d' :=
  congrAp2 quoF (congrMonus (.eqRefl _) (congrMul (mS_congr hm hd) (mS_congr hm hd))) hd

section Seq

variable {D a : PTm n} (hA : Γ ⊢[PRAAx] lt (a * a) D) (hB : Γ ⊢[PRAAx] lt D (succ a * succ a))
include hA hB

theorem red_one : Γ ⊢[PRAAx] Red D a (M (succ zero) D a) (Dd (succ zero) D a) := by
  have z := zero_parts (Γ := Γ) D a
  have sp := succ_parts (Γ := Γ) zero D a
  have st := start_reduced hA hB
  refine Red_congr ?_ ?_ (Prf.andE₁ st)
  · exact ((Prf.andE₁ sp).eqTrans (mS_congr (Prf.andE₁ z) (Prf.andE₁ (Prf.andE₂ z)))).eqSymm
  · exact ((Prf.andE₁ (Prf.andE₂ sp)).eqTrans (dS_congr (Prf.andE₁ z) (Prf.andE₁ (Prf.andE₂ z)))).eqSymm

theorem red_step {k : PTm n} (h : Γ ⊢[PRAAx] Red D a (M (succ k) D a) (Dd (succ k) D a)) :
    Γ ⊢[PRAAx] Red D a (M (succ (succ k)) D a) (Dd (succ (succ k)) D a) := by
  have sp := succ_parts (Γ := Γ) (succ k) D a
  exact Red_congr (Prf.andE₁ sp).eqSymm (Prf.andE₁ (Prf.andE₂ sp)).eqSymm (Prf.andE₁ (step_closure hA hB h))

/-- Every state from index `1` on is reduced. -/
theorem red_succ (k : PTm n) : Γ ⊢[PRAAx] Red D a (M (succ k) D a) (Dd (succ k) D a) := by
  have hA' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a * Syn.shift a) (Syn.shift D) := by
    simpa [Fm.shift, Syn.shift] using hA.shift
  have hB' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift D) (succ (Syn.shift a) * succ (Syn.shift a)) := by
    simpa [Fm.shift, Syn.shift] using hB.shift
  have hall : Γ ⊢[PRAAx] Fm.all (Red (Syn.shift D) (Syn.shift a) (M (succ (var 0)) (Syn.shift D) (Syn.shift a))
      (Dd (succ (var 0)) (Syn.shift D) (Syn.shift a))) := by
    refine PRA.qfInd _ ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ ?_ ?_
    · simp only [Red, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
        PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact red_one hA hB
    · simp only [Red, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
        PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact red_step hA'.wk hB'.wk (k := var 0) Prf.hyp0
  have h := Prf.allE k hall
  simp only [Red, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
    PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- `d_k ≥ 1`. -/
theorem dpos (k : PTm n) : Γ ⊢[PRAAx] Dd k D a ≐ succ (pred (Dd k D a)) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have z := zero_parts (Γ := (k ≐ zero) :: Γ) D a
    have e : ((k ≐ zero) :: Γ) ⊢[PRAAx] Dd k D a ≐ one :=
      (congrFst (congrSnd (congrAp2 _ Prf.hyp0 (.eqRefl _)))).eqTrans (Prf.andE₁ (Prf.andE₂ z))
    exact e.eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred e.eqSymm)))
  · have r := red_succ hA.wk hB.wk (Γ := (k ≐ succ (pred k)) :: Γ) (pred k)
    have e : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] Dd k D a ≐ Dd (succ (pred k)) D a :=
      congrFst (congrSnd (congrAp2 _ Prf.hyp0 (.eqRefl _)))
    have p := pos_of_le_one (Prf.andE₁ (Prf.andE₂ r))
    exact AnalyticNumberTheory.Primes.eq_succ_pred (e.eqTrans p)

/-- The step is exact at every index: `d_k c_k = m_{k+1} + m_k`, `D = m_{k+1}² + d_k d_{k+1}`. -/
theorem exact_step (k : PTm n) :
    Γ ⊢[PRAAx] (Dd k D a * C k D a ≐ M (succ k) D a + M k D a) ⋏
      (D ≐ M (succ k) D a * M (succ k) D a + Dd k D a * Dd (succ k) D a) := by
  have sp := succ_parts (Γ := Γ) k D a
  have em := Prf.andE₁ sp
  have ed := Prf.andE₁ (Prf.andE₂ sp)
  refine .orE (zero_or_succ k) ?_ ?_
  · let G := (k ≐ zero) :: Γ
    have z := zero_parts (Γ := G) D a
    have stG := start_reduced (Γ := G) hA.wk hB.wk
    have hm0 : G ⊢[PRAAx] M k D a ≐ zero := (congrFst (congrAp2 _ Prf.hyp0 (.eqRefl _))).eqTrans (Prf.andE₁ z)
    have hd0 : G ⊢[PRAAx] Dd k D a ≐ one :=
      (congrFst (congrSnd (congrAp2 _ Prf.hyp0 (.eqRefl _)))).eqTrans (Prf.andE₁ (Prf.andE₂ z))
    have c0 : G ⊢[PRAAx] C k D a ≐ cD a zero one := cD_congr hm0 hd0
    have m1 : G ⊢[PRAAx] M (succ k) D a ≐ mS a zero one := em.wk.eqTrans (mS_congr hm0 hd0)
    have d1 : G ⊢[PRAAx] Dd (succ k) D a ≐ PellCFStep.dS D a zero one := ed.wk.eqTrans (dS_congr hm0 hd0)
    refine .andI ?_ ?_
    · exact (congrMul hd0 c0).eqTrans ((Prf.andE₁ (Prf.andE₂ stG)).eqTrans (congrAdd m1.eqSymm hm0.eqSymm))
    · exact (Prf.andE₂ (Prf.andE₂ stG)).eqTrans (congrAdd (congrMul m1.eqSymm m1.eqSymm) (congrMul hd0.eqSymm d1.eqSymm))
  · let G := (k ≐ succ (pred k)) :: Γ
    have r := red_succ (Γ := G) hA.wk hB.wk (pred k)
    have hmk : G ⊢[PRAAx] M k D a ≐ M (succ (pred k)) D a := congrFst (congrAp2 _ Prf.hyp0 (.eqRefl _))
    have hdk : G ⊢[PRAAx] Dd k D a ≐ Dd (succ (pred k)) D a := congrFst (congrSnd (congrAp2 _ Prf.hyp0 (.eqRefl _)))
    have cl := step_closure (Γ := G) hA.wk hB.wk r
    have c0 : G ⊢[PRAAx] C k D a ≐ cD a (M (succ (pred k)) D a) (Dd (succ (pred k)) D a) := cD_congr hmk hdk
    have m1 : G ⊢[PRAAx] M (succ k) D a ≐ mS a (M (succ (pred k)) D a) (Dd (succ (pred k)) D a) :=
      em.wk.eqTrans (mS_congr hmk hdk)
    have d1 : G ⊢[PRAAx] Dd (succ k) D a ≐ PellCFStep.dS D a (M (succ (pred k)) D a) (Dd (succ (pred k)) D a) :=
      ed.wk.eqTrans (dS_congr hmk hdk)
    refine .andI ?_ ?_
    · exact (congrMul hdk c0).eqTrans ((Prf.andE₁ (Prf.andE₂ cl)).eqTrans (congrAdd m1.eqSymm hmk.eqSymm))
    · exact (Prf.andE₂ (Prf.andE₂ cl)).eqTrans (congrAdd (congrMul m1.eqSymm m1.eqSymm) (congrMul hdk.eqSymm d1.eqSymm))

/-- The invariants at index `k`. -/
abbrev InvF (k D a : PTm n) : Fm PTm n :=
  (P k D a ≐ M k D a * Q k D a + Dd k D a * Q' k D a) ⋏
    ((D * Q k D a ≐ M k D a * P k D a + Dd k D a * P' k D a) ⋏
      (P k D a * Q' k D a + par k ≐ P' k D a * Q k D a + monus one (par k)))

omit hA hB in
theorem par_flip (k : PTm n) : Γ ⊢[PRAAx] monus one (par (succ k)) ≐ par k := by
  refine (congrMonus (.eqRefl _) (par_succ k)).eqTrans ?_
  refine .orE (par_cases k) ?_ ?_
  · exact (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans monus_one_zero)).eqTrans
      (monus_one_one.eqTrans Prf.hyp0.eqSymm)
  · exact (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans monus_one_one)).eqTrans
      (monus_one_zero.eqTrans Prf.hyp0.eqSymm)

omit hA hB in
theorem inv_zero : Γ ⊢[PRAAx] InvF zero D a := by
  have z := zero_parts (Γ := Γ) D a
  have m0 := natEq (Prf.andE₁ z); have d0 := natEq (Prf.andE₁ (Prf.andE₂ z))
  have p0 := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ z)))
  have p0' := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ z))))
  have q0 := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ z)))))
  have q0' := natEq (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ z)))))
  have pz := natEq (par_zero (Γ := Γ) (n := n))
  have mz := natEq ((congrMonus (.eqRefl _) (par_zero (Γ := Γ) (n := n))).eqTrans monus_one_zero)
  refine .andI ?_ (.andI ?_ ?_) <;> (apply deriveNat; ipra_simps)
  · linear_combination p0 - 𝔞 (Q zero D a) * m0 - 𝔞 (M zero D a) * q0 * 0 - (𝔞 (Q' zero D a)) * d0 - q0'
  · linear_combination 𝔞 D * q0 - 𝔞 (P zero D a) * m0 - 𝔞 (P' zero D a) * d0 - p0'
  · linear_combination 𝔞 (Q' zero D a) * p0 + q0' + pz - 𝔞 (Q zero D a) * p0' - mz

theorem inv_step {k : PTm n} (h : Γ ⊢[PRAAx] InvF k D a) : Γ ⊢[PRAAx] InvF (succ k) D a := by
  have sp := succ_parts (Γ := Γ) k D a
  have ex := exact_step hA hB (Γ := Γ) k
  have hd := dpos hA hB (Γ := Γ) k
  have sP := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sp)))
  have sP' := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp))))
  have sQ := natEq (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp)))))
  have sQ' := natEq (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp)))))
  have e1 := natEq (Prf.andE₁ ex); have e2 := natEq (Prf.andE₂ ex)
  have i1 := natEq (Prf.andE₁ h); have i2 := natEq (Prf.andE₁ (Prf.andE₂ h)); have dt := natEq (Prf.andE₂ (Prf.andE₂ h))
  refine .andI ?_ (.andI ?_ ?_)
  · refine Combinatorics.BinomialIdentities.mul_cancel hd ?_
    ipra_lc 𝔞 (Dd k D a) * sP - 𝔞 (Dd k D a) * 𝔞 (M (succ k) D a) * sQ +
      (𝔞 (P k D a) - 𝔞 (M (succ k) D a) * 𝔞 (Q k D a)) * e1 - i2 + 𝔞 (M (succ k) D a) * i1 + 𝔞 (Q k D a) * e2 -
      𝔞 (Dd k D a) * 𝔞 (Dd (succ k) D a) * sQ'
  · refine Combinatorics.BinomialIdentities.mul_cancel hd ?_
    ipra_lc 𝔞 D * 𝔞 (Dd k D a) * sQ - 𝔞 (Dd k D a) * 𝔞 (M (succ k) D a) * sP +
      (𝔞 D * 𝔞 (Q k D a) - 𝔞 (M (succ k) D a) * 𝔞 (P k D a)) * e1 - 𝔞 D * i1 + 𝔞 (M (succ k) D a) * i2 +
      𝔞 (P k D a) * e2 - 𝔞 (Dd k D a) * 𝔞 (Dd (succ k) D a) * sP'
  · ipra_lc 𝔞 (P (succ k) D a) * sQ' + 𝔞 (Q k D a) * sP - 𝔞 (P' (succ k) D a) * sQ -
      (𝔞 (C k D a) * 𝔞 (Q k D a) + 𝔞 (Q' k D a)) * sP' + natEq (par_succ (Γ := Γ) k) - natEq (par_flip (Γ := Γ) k) -
      dt

/-- `lem:cfinvariants`: `p_{k−1} = m_k q_{k−1} + d_k q_{k−2}`, `D q_{k−1} = m_k p_{k−1} + d_k p_{k−2}`, and
`p_{k−1} q_{k−2} − p_{k−2} q_{k−1} = (−1)^k`, for every `k`. -/
theorem cf_invariants (k : PTm n) : Γ ⊢[PRAAx] InvF k D a := by
  have hA' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a * Syn.shift a) (Syn.shift D) := by
    simpa [Fm.shift, Syn.shift] using hA.shift
  have hB' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift D) (succ (Syn.shift a) * succ (Syn.shift a)) := by
    simpa [Fm.shift, Syn.shift] using hB.shift
  have hall : Γ ⊢[PRAAx] Fm.all (InvF (var 0) (Syn.shift D) (Syn.shift a)) := by
    refine PRA.qfInd _ ⟨trivial, trivial, trivial⟩ ?_ ?_
    · simp only [InvF, Fm.subst_and, Fm.subst_eq, subst_ap1, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
        PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact inv_zero
    · simp only [InvF, Fm.subst_and, Fm.subst_eq, subst_ap1, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
        PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact inv_step hA'.wk hB'.wk (k := var 0) Prf.hyp0
  have h := Prf.allE k hall
  simp only [InvF, Fm.subst_and, Fm.subst_eq, subst_ap1, subst_ap2, subst_pairT, subst_fstT, subst_sndT,
    PTm.subst_add, PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- `eq:cfnorm`: `p_{k−1}² − D q_{k−1}² = (−1)^k d_k`, as `p² + [k odd] d = D q² + [k even] d`. -/
theorem cf_norm (k : PTm n) :
    Γ ⊢[PRAAx] P k D a * P k D a + par k * Dd k D a ≐ D * (Q k D a * Q k D a) + monus one (par k) * Dd k D a := by
  have h := cf_invariants hA hB (Γ := Γ) k
  ipra_lc 𝔞 (P k D a) * natEq (Prf.andE₁ h) - 𝔞 (Q k D a) * natEq (Prf.andE₁ (Prf.andE₂ h)) +
    𝔞 (Dd k D a) * natEq (Prf.andE₂ (Prf.andE₂ h))

end Seq

end LeanProofs.IPRA.DiophantineNumberTheory.PellCF
