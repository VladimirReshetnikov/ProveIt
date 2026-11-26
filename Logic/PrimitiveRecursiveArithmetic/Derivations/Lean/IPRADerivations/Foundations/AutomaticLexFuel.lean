import IPRADerivations.Foundations.LexChain
import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Foundations.IntersectionEnumeration
import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Automatic fuel for fixed-dimensional descent (`ipra_resources_and_elimination_2026-11-15`, `thm:automatic-lex-fuel`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, theorem `thm:automatic-lex-fuel`:
for a total one-step transition `τ(x, u)`, an initial state `u_0(x)`, the finite simulation
`u(x, 0) = u_0(x)`, `u(x, t + 1) = τ(x, u(x, t))`, an activity predicate `A` with inactive
states absorbing, a quantifier-free invariant `I` (initialized and preserved), and rank
functions `r_0, …, r_{d−1}` with the local obligation

`I(x, u) ∧ A(x, u) ∧ A(x, τ(x, u)) ⟹ r(x, u) >_lex r(x, τ(x, u))`,

"there is an explicitly defined primitive-recursive `B(x)` such that iPRA proves
`¬A(x, u(x, B(x)))`." Proof: "Define the trajectory envelope
`h(x, t) = max({0} ∪ {r_j(x, u(x, q)) : q ≤ t, j < d})` ... Set `B(x) = F_d(x, 0)` using this
`h`. ... Suppose that `u(x, B(x))` were active. Since inactive states are absorbing, all states
`u(x, 0), …, u(x, B(x))` would then be active ... The local rank obligation gives a controlled
strictly descending chain of `B(x) + 1` rank tuples. Theorem `thm:controlled-lex` would imply
`B(x) + 1 ≤ F_d(x, 0) = B(x)`, a contradiction."

Derived for every external dimension `d`, with activity as a bit `a(x, u)` (active when
`a ≠ 0`) and the four premises as rules (they are universally valid statements about the
supplied terms):

* `traj`, `traj_zero`, `traj_succ`, `traj_congr`: the finite simulation;
* `inv_at`: the invariant holds along the trajectory (quantifier-free induction);
* `inactive_forward`, `active_back`: inactivity persists forward, hence activity at a later
  time gives activity at every earlier time, with no case distinction;
* `lexgt_congr`: the lexicographic order respects derivable equality of coordinates;
* `Mx_mono`: the bounded maximum is nondecreasing in its bound;
* `rankT`, `envV`, `envH`: the rank of the trajectory as a term, the maximum over the
  coordinates, and the envelope `h(x, t) = max_{q ≤ t} max_j r_j(x, u(x, q))`; `env_le`,
  `envH_mono`;
* `automatic_fuel`: `a(x, u(x, B(x))) = 0` for `B(x) = F_d(x, 0)`: the state at time `B(x)` is
  inactive.

The postcondition clause of the theorem ("if iPRA additionally proves
`I ∧ ¬A → R(x, out(x, u))` then `R(x, w(x))`") is one application of that rule to `inv_at` and
`automatic_fuel`, stated as `automatic_post`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.AutomaticLexFuel

open_ipra
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open LeanProofs.IPRA.Foundations.IterationFusion (rel subst_rel rel_congr)
open LeanProofs.IPRA.Foundations.LexFuelMonotone (itStep itP itP_zero itP_succ F succ_le)
open LeanProofs.IPRA.Foundations.LexPotential (itP_congr_count lexgt)
open LeanProofs.IPRA.Foundations.LexChain (co controlled_lex)
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (maxFin le_maxFin)
open LeanProofs.IPRA.Probability.UnionUtility (mxF Mx mx_succ mx_upper)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The finite simulation -/

section Trajectory

variable (τ : PTm 2) (u0 : PTm 1)

/-- `u(x, t)`: the state after `t` steps. -/
abbrev traj (t x : PTm k) : PTm k := itP τ t x (inst1 u0 x)

theorem traj_zero (x : PTm k) : Γ ⊢[PRAAx] traj τ u0 zero x ≐ inst1 u0 x := itP_zero τ x _

theorem traj_succ (t x : PTm k) :
    Γ ⊢[PRAAx] traj τ u0 (succ t) x ≐ inst2 τ x (traj τ u0 t x) := itP_succ τ t x _

theorem traj_congr {t t' : PTm k} (h : Γ ⊢[PRAAx] t ≐ t') (x : PTm k) :
    Γ ⊢[PRAAx] traj τ u0 t x ≐ traj τ u0 t' x := itP_congr_count τ h x _

/-! ### The invariant -/

variable (I : Fm PTm 2)

/-- Variables: `0 = t`, `1 = x`. -/
private def invF : Fm PTm 2 := rel I (var 1) (traj τ u0 (var 0) (var 1))

private theorem inv₀ (hqf : I.QF)
    (hI0 : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] rel I x (inst1 u0 x))
    (hIs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] rel I x (inst2 τ x u))) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] invF τ u0 I := by
  ipra_ind (subst_QF' hqf _) [invF, subst_rel, subst_ap2, subst_pairT, subst_inst1]
  · exact rel_congr I (.eqRefl _) (traj_zero τ u0 _).eqSymm (hI0 _)
  · have ih : [invF τ u0 I] ⊢[PRAAx] rel I (var 1) (traj τ u0 (var 0) (var 1)) := Prf.hyp0
    exact rel_congr I (.eqRefl _) (traj_succ τ u0 _ _).eqSymm (hIs ih)

/-- The invariant holds at every time. -/
theorem inv_at (hqf : I.QF)
    (hI0 : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] rel I x (inst1 u0 x))
    (hIs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] rel I x (inst2 τ x u)))
    (t x : PTm k) : Γ ⊢[PRAAx] rel I x (traj τ u0 t x) := by
  have i := inst (Γ := Γ) (inv₀ τ u0 I hqf hI0 hIs) (![t, x] : Fin 2 → PTm k)
  simpa [invF] using i

/-! ### Activity -/

variable (a : PTm 2)

/-- Variables: `0 = j`, `1 = i`, `2 = x`. -/
private abbrev fwF : Fm PTm 3 :=
  (inst2 a (var 2) (traj τ u0 (var 1) (var 2)) ≐ zero) ⟶
    (inst2 a (var 2) (traj τ u0 (var 1 + var 0) (var 2)) ≐ zero)

private theorem fw₀
    (habs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] inst2 a x (inst2 τ x u) ≐ zero)) :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] fwF τ u0 a := by
  ipra_ind (⟨trivial, trivial⟩) [subst_inst2, subst_ap2, subst_pairT, subst_inst1]
  · exact .impI ((congrInst2 a (.eqRefl _) (traj_congr τ u0 (add_zero _) _)).eqTrans Prf.hyp0)
  · exact .impI ((congrInst2 a (.eqRefl _)
      ((traj_congr τ u0 (add_succ _ _) _).eqTrans (traj_succ τ u0 _ _))).eqTrans
      (habs (.impE Prf.hyp1 Prf.hyp0)))

/-- Inactive states are absorbing along the trajectory. -/
theorem inactive_forward
    (habs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] inst2 a x (inst2 τ x u) ≐ zero))
    {i x : PTm k} (j : PTm k) (h : Γ ⊢[PRAAx] inst2 a x (traj τ u0 i x) ≐ zero) :
    Γ ⊢[PRAAx] inst2 a x (traj τ u0 (i + j) x) ≐ zero := by
  have e := inst (Γ := Γ) (fw₀ τ u0 a habs) (![j, i, x] : Fin 3 → PTm k)
  simp at e
  exact .impE e h

/-- A state that is active at time `B` was active at every earlier time. -/
theorem active_back
    (habs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] inst2 a x (inst2 τ x u) ≐ zero))
    {i B x : PTm k} (hle : Γ ⊢[PRAAx] le i B)
    (hB : Γ ⊢[PRAAx] neg (inst2 a x (traj τ u0 B x) ≐ zero)) :
    Γ ⊢[PRAAx] neg (inst2 a x (traj τ u0 i x) ≐ zero) :=
  .impI (.impE hB.wk
    ((congrInst2 a (.eqRefl _) (traj_congr τ u0 (eq_add_of_le hle).wk x)).eqTrans
      (inactive_forward τ u0 a habs (monus B i) Prf.hyp0)))

end Trajectory

/-- The lexicographic order respects derivable equality of the coordinates. -/
theorem lexgt_congr : {d : ℕ} → {Γ : List (Fm PTm k)} → {c c' e e' : Fin d → PTm k} →
    (∀ j, Γ ⊢[PRAAx] c j ≐ e j) → (∀ j, Γ ⊢[PRAAx] c' j ≐ e' j) →
    (Γ ⊢[PRAAx] lexgt c c') → (Γ ⊢[PRAAx] lexgt e e')
  | 0, _, _, _, _, _, _, _, h => h
  | d + 1, Γ, c, c', e, e', h₁, h₂, h => by
    refine .orE h (.orI₁ ?_) (.orI₂ ?_)
    · exact lt_congr (h₂ 0).wk (h₁ 0).wk Prf.hyp0
    · exact .andI (((h₁ 0).wk.eqSymm.eqTrans (Prf.andE₁ Prf.hyp0)).eqTrans (h₂ 0).wk)
        (lexgt_congr (c := fun j => c j.succ) (c' := fun j => c' j.succ)
          (fun j => (h₁ j.succ).wk) (fun j => (h₂ j.succ).wk) (Prf.andE₂ Prf.hyp0))

/-! ## The bounded maximum is monotone -/

section Max

variable (V : PTm 2)

/-- Variables: `0 = j`, `1 = n`, `2 = x`. -/
private abbrev mmF : Fm PTm 3 := le (Mx V (var 1) (var 2)) (Mx V (var 1 + var 0) (var 2))

private theorem mm₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] mmF V := by
  ipra_ind [subst_le, subst_ap2]
  · exact le_congr (.eqRefl _) (congrAp2 (mxF V) (add_zero _).eqSymm (.eqRefl _)) (le_refl _)
  · refine le_trans Prf.hyp0 ?_
    exact le_congr (.eqRefl _)
      ((congrAp2 (mxF V) (add_succ _ _) (.eqRefl _)).eqTrans (mx_succ V _ _)).eqSymm
      (le_add_right _ _)

/-- `max_{q < K} V(q) ≤ max_{q < K'} V(q)` for `K ≤ K'`. -/
theorem Mx_mono {K K' : PTm k} (h : Γ ⊢[PRAAx] le K K') (x : PTm k) :
    Γ ⊢[PRAAx] le (Mx V K x) (Mx V K' x) := by
  have i := inst (Γ := Γ) (mm₀ V) (![monus K' K, K, x] : Fin 3 → PTm k)
  simp at i
  exact le_congr (.eqRefl _) (congrAp2 (mxF V) (eq_add_of_le h).eqSymm (.eqRefl _)) i

end Max

theorem subst_maxFin {m : ℕ} (σ : Fin k → PTm m) : {d : ℕ} → (c : Fin d → PTm k) →
    Syn.subst σ (maxFin c) = maxFin fun j => Syn.subst σ (c j)
  | 0, _ => by simp [maxFin]
  | d + 1, c => by
    simp only [maxFin, PTm.subst_add, PTm.subst_monus]
    rw [subst_maxFin σ (fun j => c j.succ)]

/-! ## The envelope -/

section Envelope

variable (τ : PTm 2) (u0 : PTm 1) {d : ℕ} (r : Fin d → PTm 2)

/-- The trajectory as a term; variables `0 = i`, `1 = x`. -/
def trajT : PTm 2 :=
  ap2 (rec2 (sndT (var 0)) (itStep τ)) (var 0) (pairT (var 1) (Syn.subst ![var 1] u0))

theorem trajT_at (i x : PTm k) : Syn.subst ![i, x] (trajT τ u0) = traj τ u0 i x := by
  have e : Syn.subst ![i, x] (Syn.subst ![(var 1 : PTm 2)] u0) = inst1 u0 x := by
    simp only [inst1, Syn.subst_subst]
    congr 1; funext l; fin_cases l; rfl
  simp only [trajT, subst_ap2, subst_pairT, Syn.subst_var, e]
  rfl

/-- The `j`-th rank along the trajectory; variables `0 = i`, `1 = x`. -/
def rankT (j : Fin d) : PTm 2 := Syn.subst ![var 1, trajT τ u0] (r j)

theorem rankT_at (j : Fin d) (i x : PTm k) :
    inst2 (rankT τ u0 r j) i x = inst2 (r j) x (traj τ u0 i x) := by
  simp only [inst2, rankT, Syn.subst_subst]
  congr 1; funext l; fin_cases l
  · rfl
  · exact trajT_at τ u0 i x

theorem rank_eq (j : Fin d) (i x : PTm k) :
    Γ ⊢[PRAAx] inst2 (r j) x (traj τ u0 i x) ≐ inst2 (rankT τ u0 r j) i x := by
  rw [rankT_at]
  exact .eqRefl _

/-- The maximum of the ranks at one time. -/
def envV : PTm 2 := maxFin (rankT τ u0 r)

/-- The envelope `h(x, t) = max_{q ≤ t} max_j r_j(x, u(x, q))`; variables `0 = x`, `1 = t`. -/
def envH : PTm 2 := ap2 (mxF (envV τ u0 r)) (succ (var 1)) (var 0)

theorem envH_at (x t : PTm k) :
    inst2 (envH τ u0 r) x t = Mx (envV τ u0 r) (succ t) x := by
  simp [inst2, envH]

/-- Every rank at time `q` is below the envelope at time `q`. -/
theorem env_le (j : Fin d) (q x : PTm k) :
    Γ ⊢[PRAAx] le (inst2 (rankT τ u0 r j) q x) (inst2 (envH τ u0 r) x q) := by
  rw [envH_at]
  have e : inst2 (envV τ u0 r) q x = maxFin fun j => inst2 (rankT τ u0 r j) q x := by
    simp only [inst2, envV]
    exact subst_maxFin _ _
  have up := mx_upper (Γ := Γ) (envV τ u0 r) (K := succ q) (b := q) (x := x) (le_refl _)
  rw [e] at up
  exact le_trans (le_maxFin (fun j => inst2 (rankT τ u0 r j) q x) j) up

/-- The envelope is nondecreasing in the time. -/
theorem envH_mono {x s t : PTm k} (h : Γ ⊢[PRAAx] le s t) :
    Γ ⊢[PRAAx] le (inst2 (envH τ u0 r) x s) (inst2 (envH τ u0 r) x t) := by
  rw [envH_at, envH_at]
  exact Mx_mono (envV τ u0 r) (succ_le h) x

end Envelope

/-! ## The theorem -/

section Main

variable (τ : PTm 2) (u0 : PTm 1) (I : Fm PTm 2) (a : PTm 2) {d : ℕ} (r : Fin d → PTm 2)

/-- `B(x) = F_d(x, 0)` for the trajectory envelope. -/
abbrev fuel (x : PTm k) : PTm k := inst2 (F (envH τ u0 r) d) x zero

theorem shift_act (x B : PTm k) :
    Fm.shift (neg (inst2 a x (traj τ u0 B x) ≐ zero)) =
      neg (inst2 a (Syn.shift x) (traj τ u0 (Syn.shift B) (Syn.shift x)) ≐ zero) := by
  simp [Fm.shift, Syn.shift]

/-- `thm:automatic-lex-fuel`: the state at time `B(x) = F_d(x, 0)` is inactive. -/
theorem automatic_fuel (hqf : I.QF)
    (hI0 : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] rel I x (inst1 u0 x))
    (hIs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] rel I x (inst2 τ x u)))
    (habs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] inst2 a x (inst2 τ x u) ≐ zero))
    (hrank : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] neg (inst2 a x u ≐ zero)) →
      (Γ ⊢[PRAAx] neg (inst2 a x (inst2 τ x u) ≐ zero)) →
      (Γ ⊢[PRAAx] lexgt (fun j => inst2 (r j) x u) (fun j => inst2 (r j) x (inst2 τ x u))))
    (x : PTm k) :
    Γ ⊢[PRAAx] inst2 a x (traj τ u0 (fuel τ u0 r x) x) ≐ zero := by
  refine .orE (eq_or_ne (inst2 a x (traj τ u0 (fuel τ u0 r x) x)) zero) Prf.hyp0 ?_
  refine not_succ_le_self (fuel τ u0 r x) _ ?_
  have hact : (neg (inst2 a x (traj τ u0 (fuel τ u0 r x) x) ≐ zero) :: Γ) ⊢[PRAAx]
      neg (inst2 a x (traj τ u0 (fuel τ u0 r x) x) ≐ zero) := Prf.hyp0
  have hact' := hact.shift
  rw [shift_act] at hact'
  have cl := controlled_lex (Γ := neg (inst2 a x (traj τ u0 (fuel τ u0 r x) x) ≐ zero) :: Γ)
    (h := envH τ u0 r) (fun hle => envH_mono τ u0 r hle) (rankT τ u0 r)
    (s := zero) (x := x) (y := x) (L' := fuel τ u0 r x)
    (.allI (.impI (lexgt_congr
      (fun j => rank_eq τ u0 r j (var 0) (Syn.shift x))
      (fun j => (congrInst2 (r j) (.eqRefl _) (traj_succ τ u0 (var 0) (Syn.shift x)).eqSymm).eqTrans
        (rank_eq τ u0 r j (succ (var 0)) (Syn.shift x)))
      (hrank (inv_at τ u0 I hqf hI0 hIs (var 0) (Syn.shift x))
        (active_back τ u0 a habs (le_of_lt Prf.hyp0) hact'.wk)
        (.impI (.impE (active_back τ u0 a habs
            (Prf.hyp1 : (_ :: lt (var 0) (Syn.shift (fuel τ u0 r x)) :: _) ⊢[PRAAx]
              le (succ (var 0)) (Syn.shift (fuel τ u0 r x))) hact'.wk.wk)
          ((congrInst2 a (.eqRefl _) (traj_succ τ u0 (var 0) (Syn.shift x))).eqTrans
            Prf.hyp0)))))))
    (fun j => env_le τ u0 r j zero x)
    (fun j => .allI (.impI (by
      rw [show Syn.shift (zero : PTm k) = zero from by simp [Syn.shift]]
      exact le_congr (.eqRefl _)
        (congrInst2 (envH τ u0 r) (.eqRefl _) (congrSucc (zero_add (var 0))).eqSymm)
        (env_le τ u0 r j (succ (var 0)) (Syn.shift x)))))
  exact le_congr (congrSucc (zero_add _)) (.eqRefl _) cl

/-- The postcondition clause: a local output theorem at inactive states with the invariant
gives the output at time `B(x)`. -/
theorem automatic_post (hqf : I.QF) {R : Fm PTm 2}
    (hI0 : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] rel I x (inst1 u0 x))
    (hIs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] rel I x (inst2 τ x u)))
    (habs : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] inst2 a x (inst2 τ x u) ≐ zero))
    (hrank : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] neg (inst2 a x u ≐ zero)) →
      (Γ ⊢[PRAAx] neg (inst2 a x (inst2 τ x u) ≐ zero)) →
      (Γ ⊢[PRAAx] lexgt (fun j => inst2 (r j) x u) (fun j => inst2 (r j) x (inst2 τ x u))))
    (hout : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x u : PTm k},
      (Γ ⊢[PRAAx] rel I x u) → (Γ ⊢[PRAAx] inst2 a x u ≐ zero) → (Γ ⊢[PRAAx] rel R x u))
    (x : PTm k) : Γ ⊢[PRAAx] rel R x (traj τ u0 (fuel τ u0 r x) x) :=
  hout (inv_at τ u0 I hqf hI0 hIs _ x) (automatic_fuel τ u0 I a r hqf hI0 hIs habs hrank x)

end Main

end LeanProofs.IPRA.Foundations.AutomaticLexFuel
