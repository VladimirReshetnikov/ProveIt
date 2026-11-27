import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.ProdLemmas

/-!
# Primitive scaling: the gcd of a list (`ipra_presentations_to_witnesses`, `lem:primitive-scaling`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:primitive-scaling`: "Compute
`g = gcd(|u_1|, …, |u_D|)` by the Euclidean algorithm, folded along the finite list. Since `u` is
nonzero, `g > 0`. Every `u_i` is divisible by `g`, so `w_i = u_i / g` is an integer and the gcd
of its absolute coordinates is one."

For a term `ω(i, x)` (the entries `|u_i|`) and a positive seed `s` (a nonzero entry, which a
bounded scan of a nonzero vector supplies), the fold is

`G_0 = s`,  `G_{i+1} = gcd(G_i, ω_i)`,

with `gcd` of `Core/Gcd`. For `s ≥ 1`:

* `G_zero`, `G_succ`: the recursion; `G_pos`: every `G_i` is positive;
* `G_chain`, `G_mono`: `G_{i+1} ∣ G_i`, `G_{i+1} ∣ ω_i`, and `G_N ∣ G_i` for `i ≤ N`;
* `G_dvd_entry`, `G_dvd_seed`: `G_N` divides every `ω_i` with `i < N`, and the seed;
* `G_greatest`: a positive common divisor of the seed and of all `ω_i`, `i < N`, divides `G_N`.
  The hypothesis is a bounded universal statement; the induction is the quantifier-free
  induction rule in a context that contains it;
* `primitive`: if `d G_N` divides the seed and every `ω_i`, `i < N`, then `d = 1`: the quotients
  `ω_i / G_N` have no common divisor above one.

Not derived: the clearing of denominators (`u = L v`), the transport of the eigenvector equation
along the scaling, and the Bezout coefficients `∑ e_i w_i = 1` by the extended algorithm
(`Foundations/EigenvalueIntegral` takes them as a hypothesis).
-/

namespace LeanProofs.IPRA.Foundations.PrimitiveScaling

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
  (gcd_dvd' gcd_greatest' dvd_trans' dvd_self' dvd_le' one_le_of_pos)

variable {k : ℕ} {Γ : List (Fm PTm k)}

theorem gcd_congr' {a a' b b' : PTm k} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] gcd a b ≐ gcd a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (gcd (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simp only [subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ] at h
  exact h

theorem shift_pos' (e : PTm k) :
    Fm.shift (e ≐ succ (pred e)) = (Syn.shift e ≐ succ (pred (Syn.shift e))) := by
  simp [Fm.shift, Syn.shift]

variable (ω : PTm 2)

/-! ## The fold -/

/-- `G_0 = s`; variable `0 = ⟨s, x⟩`. -/
def gBase : PTm 1 := fstT (var 0)

/-- `G_{i+1} = gcd(G_i, ω(i, x))`; variables `0 = i`, `1 = G_i`, `2 = ⟨s, x⟩`. -/
def gStep : PTm 3 := gcd (var 1) (inst2 ω (var 0) (sndT (var 2)))

/-- The gcd of the seed `s` and the entries `ω(0, x), …, ω(i - 1, x)`. -/
abbrev G (i s x : PTm k) : PTm k := ap2 (rec2 gBase (gStep ω)) i (pairT s x)

theorem G_zero (s x : PTm k) : Γ ⊢[PRAAx] G ω zero s x ≐ s := by
  have h := rec2_zero (Γ := Γ) gBase (gStep ω) (pairT s x)
  have e : Syn.subst ![pairT s x] gBase = fstT (pairT s x) := by simp [gBase]
  rw [e] at h
  exact h.eqTrans (fst_pair _ _)

theorem G_succ (i s x : PTm k) :
    Γ ⊢[PRAAx] G ω (succ i) s x ≐ gcd (G ω i s x) (inst2 ω i x) := by
  have h := rec2_succ (Γ := Γ) gBase (gStep ω) i (pairT s x)
  have e : Syn.subst ![i, ap2 (rec2 gBase (gStep ω)) i (pairT s x), pairT s x] (gStep ω) =
      gcd (G ω i s x) (inst2 ω i (sndT (pairT s x))) := by
    show Syn.subst ![i, ap2 (rec2 gBase (gStep ω)) i (pairT s x), pairT s x]
      (gcd (var 1) (inst2 ω (var 0) (sndT (var 2)))) = _
    simp only [subst_ex2, subst_inst2, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ConciseIPRA.PTm.subst_succ]
  rw [e] at h
  exact h.eqTrans (gcd_congr' (.eqRefl _) (congrInst2 ω (.eqRefl _) (snd_pair _ _)))

/-! ## Positivity and divisibility -/

/-- Variables: `0 = i`, `1 = s`, `2 = x`. -/
private abbrev posF : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (G ω (var 0) (var 1) (var 2) ≐ succ (pred (G ω (var 0) (var 1) (var 2))))

private theorem pos₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] posF ω := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2, subst_pairT]
  · exact .impI (pos_of_eq_succ ((G_zero ω _ _).eqTrans Prf.hyp0))
  · exact .impI (pos_of_eq_succ ((G_succ ω _ _ _).eqTrans (gcd_pos (.impE Prf.hyp1 Prf.hyp0))))

/-- Every partial gcd is positive. -/
theorem G_pos {s : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (i x : PTm k) :
    Γ ⊢[PRAAx] G ω i s x ≐ succ (pred (G ω i s x)) := by
  have h := inst (Γ := Γ) (pos₀ ω) (![i, s, x] : Fin 3 → PTm k)
  simp at h
  exact .impE h hs

/-- `G_{i+1}` divides `G_i` and `ω_i`. -/
theorem G_chain {s : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (i x : PTm k) :
    Γ ⊢[PRAAx] dvd (G ω (succ i) s x) (G ω i s x) ⋏ dvd (G ω (succ i) s x) (inst2 ω i x) := by
  have d := gcd_dvd' (b := inst2 ω i x) (G_pos ω hs i x)
  exact .andI (dvd_congr_left (G_succ ω i s x).eqSymm (Prf.andE₁ d))
    (dvd_congr_left (G_succ ω i s x).eqSymm (Prf.andE₂ d))

theorem mono_step {N i s x : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hle : Γ ⊢[PRAAx] le i (succ N))
    (ih : Γ ⊢[PRAAx] le i N ⟶ dvd (G ω N s x) (G ω i s x)) :
    Γ ⊢[PRAAx] dvd (G ω (succ N) s x) (G ω i s x) := by
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · have h' : (lt i (succ N) :: Γ) ⊢[PRAAx] le i N :=
      (succ_monus_succ i N).eqSymm.eqTrans Prf.hyp0
    exact dvd_trans' (G_pos ω hs.wk (succ N) x) (G_pos ω hs.wk N x)
      (Prf.andE₁ (G_chain ω hs N x)).wk (.impE ih.wk h')
  · have hi : ((i ≐ succ N) :: Γ) ⊢[PRAAx] i ≐ succ N := Prf.hyp0
    exact dvd_congr (congrAp2 _ hi.eqSymm (.eqRefl _)) (dvd_self' (G_pos ω hs.wk (succ N) x))

/-- Variables: `0 = N`, `1 = i`, `2 = s`, `3 = x`. -/
private abbrev monoF : Fm PTm 4 :=
  (var 2 ≐ succ (pred (var 2))) ⟶ le (var 1) (var 0) ⟶
    dvd (G ω (var 0) (var 2) (var 3)) (G ω (var 1) (var 2) (var 3))

private theorem mono₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] monoF ω := by
  ipra_ind (⟨trivial, trivial, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · refine .impI (.impI ?_)
    have hi : [le (var 0 : PTm 3) zero, (var 1 : PTm 3) ≐ succ (pred (var 1))] ⊢[PRAAx]
        (var 0 : PTm 3) ≐ zero := (monus_zero _).eqSymm.eqTrans Prf.hyp0
    exact dvd_congr (congrAp2 _ hi.eqSymm (.eqRefl _)) (dvd_self' (G_pos ω Prf.hyp1 zero _))
  · exact .impI (.impI (mono_step ω Prf.hyp1 Prf.hyp0 (.impE hyp2 Prf.hyp1)))

/-- A later partial gcd divides an earlier one. -/
theorem G_mono {s i N : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (h : Γ ⊢[PRAAx] le i N)
    (x : PTm k) : Γ ⊢[PRAAx] dvd (G ω N s x) (G ω i s x) := by
  have j := inst (Γ := Γ) (mono₀ ω) (![N, i, s, x] : Fin 4 → PTm k)
  simp at j
  exact .impE (.impE j hs) h

/-- The gcd divides every entry. -/
theorem G_dvd_entry {s i N : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hi : Γ ⊢[PRAAx] lt i N) (x : PTm k) : Γ ⊢[PRAAx] dvd (G ω N s x) (inst2 ω i x) :=
  dvd_trans' (G_pos ω hs N x) (G_pos ω hs (succ i) x) (G_mono ω hs hi x)
    (Prf.andE₂ (G_chain ω hs i x))

/-- The gcd divides the seed. -/
theorem G_dvd_seed {s : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (N x : PTm k) :
    Γ ⊢[PRAAx] dvd (G ω N s x) s :=
  dvd_congr (G_zero ω s x) (G_mono ω hs (zero_le N) x)

/-! ## The gcd is the greatest common divisor -/

/-- A positive common divisor of the seed and of the entries below `N` divides `G_N`. -/
theorem G_greatest {e s x N : PTm k} (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hse : Γ ⊢[PRAAx] dvd e s)
    (hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift e) (inst2 ω (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] dvd e (G ω N s x) := by
  have h : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift e) (G ω (var 0) (Syn.shift s) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa using .impI (dvd_congr (G_zero (Γ := le zero N :: Γ) ω s x).eqSymm hse.wk)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have he' := he.shift
      rw [shift_pos'] at he'
      have hm : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            dvd (Syn.shift e) (G ω (var 0) (Syn.shift s) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      exact dvd_congr (G_succ ω (var 0) _ _).eqSymm
        (gcd_greatest' he'.wk.wk (Prf.impE Prf.hyp1 hm)
          (Prf.impE hall.allOpen.wk.wk Prf.hyp0))
  have h2 := Prf.allE N h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- The scaled vector is primitive: if `d G_N` divides the seed and every entry below `N`,
then `d = 1`. -/
theorem primitive {d s x N : PTm k} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hse : Γ ⊢[PRAAx] dvd (d * G ω N s x) s)
    (hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift (d * G ω N s x)) (inst2 ω (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] d ≐ one := by
  have hG := G_pos ω hs N x
  have he := pos_mul' hd hG
  have l := dvd_le' he (G_greatest ω he hse hall) hG
  have e := natEq hG
  have l₁ : Γ ⊢[PRAAx] le d one :=
    mul_le_cancel (d' := pred (G ω N s x))
      (le_congr (by apply deriveNat; ipra_simps; linear_combination 𝔞 d * e)
        (by ipra_lc e) l)
  exact le_antisymm l₁ (one_le_of_pos hd)

end LeanProofs.IPRA.Foundations.PrimitiveScaling
