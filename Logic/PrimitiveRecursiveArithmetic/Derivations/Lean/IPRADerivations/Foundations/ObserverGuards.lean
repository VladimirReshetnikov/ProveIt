import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Foundations.CoherentTower

/-!
# Sign guards, diameter composition and independent certificates

Three small observer rules of the framework packets.

* `foundations/ipra_finitary_interface_compiler_2026-11-15`, `paper/sections/11_names_and_guards.tex`,
  Lemma "Guard soundness": if the guard on an approximation `q` with error `e` returns `+`, then `x > η`;
  if it returns `−`, then `x < −η`; "when the theorem assumes an apartness margin, sufficiently strong
  precision guarantees resolution".

  Signed values are pairs of naturals `x = x⁺ − x⁻` (cleared numerators); `|x − q| ≤ e` is the two
  inequalities `ErrLo`, `ErrHi`. The guard returns `+` when `q − e > η` and `−` when `q + e < −η`.
  `guard_pos`, `guard_neg`: the two sound cases; `resolve_pos`, `resolve_neg`: if `x > η + 2e`
  (respectively `x < −η − 2e`), the guard returns `+` (respectively `−`).

* `foundations/scoped_certificate_realization_ipra_2026-11-16`, `paper/sections/10_observer.tex`,
  Theorem "Diameter composition": if `F` has modulus `m` (`d_X(x, x') ≤ m → d_Y(F x, F x') ≤ ε`) and a
  certificate cloud has diameter at most `m`, the image cloud has diameter at most `ε`
  (`diameter_composition`, the modulus and the cloud premise as rules).

* `foundations/ipra_finite_query_normal_form_2026-11-16`, `paper/sections/11_observations.tex`, Theorem
  "Stable observable from independent certificates": from a local stability derivation
  `Valid(p, c) → Valid(r, c') → Stable(p, r, c, c')` (open, in the empty context) and two independently
  produced valid certificates, the observations are stable (`stable_of_independent`: specialization and
  implication elimination twice; no coherent stream).

* `foundations/ipra_certified_finitary_framework_2026-11-15`, `paper/sections/09_metastability_consumers.tex`,
  Theorem `thm:finite-consumer` ("Metastable finite-consumer theorem"): from the stable window `Win`
  (`eq:meta` at the consumer's control `G`: `∃ N ≤ M ∀ i, j ∈ [N, N + G(N)], d(x_i, x_j) ≤ ε`), the query
  bound `N ≤ q_t ≤ N + G(N)` and the consumer's local soundness under pairwise stability of its queried
  values, `∃ N ≤ M` with the consumer contract (`win_at`, `finite_consumer`); with a PR producer of the
  window base, the contract at that base (`finite_consumer_at`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ObserverGuards

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IterationFusion (app1 subst_app1)
open LeanProofs.IPRA.Foundations.CoherentTower (ex_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Guard soundness -/

section Guard

variable (xp xn qp qn e η : PTm k)

/-- `q − x ≤ e`. -/
abbrev ErrLo : Fm PTm k := le (qp + xn) (e + xp + qn)
/-- `x − q ≤ e`. -/
abbrev ErrHi : Fm PTm k := le (xp + qn) (e + qp + xn)

variable {xp xn qp qn e η}

/-- The guard returns `+` (`q − e > η`): then `x > η`. -/
theorem guard_pos (hlo : Γ ⊢[PRAAx] ErrLo xp xn qp qn e) (hg : Γ ⊢[PRAAx] lt (η + e + qn) qp) :
    Γ ⊢[PRAAx] lt (η + xn) xp := by
  have hg' : Γ ⊢[PRAAx] le (succ (η + e + qn)) qp := hg
  show Γ ⊢[PRAAx] le (succ (η + xn)) xp
  ipra_le sl hlo + sl hg'

/-- The guard returns `−` (`q + e < −η`): then `x < −η`. -/
theorem guard_neg (hhi : Γ ⊢[PRAAx] ErrHi xp xn qp qn e) (hg : Γ ⊢[PRAAx] lt (η + e + qp) qn) :
    Γ ⊢[PRAAx] lt (η + xp) xn := by
  have hg' : Γ ⊢[PRAAx] le (succ (η + e + qp)) qn := hg
  show Γ ⊢[PRAAx] le (succ (η + xp)) xn
  ipra_le sl hhi + sl hg'

/-- Resolution: if `x > η + 2e`, the guard returns `+`. -/
theorem resolve_pos (hhi : Γ ⊢[PRAAx] ErrHi xp xn qp qn e) (hx : Γ ⊢[PRAAx] lt (η + e + e + xn) xp) :
    Γ ⊢[PRAAx] lt (η + e + qn) qp := by
  have hx' : Γ ⊢[PRAAx] le (succ (η + e + e + xn)) xp := hx
  show Γ ⊢[PRAAx] le (succ (η + e + qn)) qp
  ipra_le sl hhi + sl hx'

/-- Resolution: if `x < −η − 2e`, the guard returns `−`. -/
theorem resolve_neg (hlo : Γ ⊢[PRAAx] ErrLo xp xn qp qn e) (hx : Γ ⊢[PRAAx] lt (η + e + e + xp) xn) :
    Γ ⊢[PRAAx] lt (η + e + qp) qn := by
  have hx' : Γ ⊢[PRAAx] le (succ (η + e + e + xp)) xn := hx
  show Γ ⊢[PRAAx] le (succ (η + e + qp)) qn
  ipra_le sl hlo + sl hx'

end Guard

/-! ## Diameter composition -/

/-- "Diameter composition": a certificate cloud of diameter `≤ m` has an image cloud of diameter `≤ ε`. -/
theorem diameter_composition {d dY : PTm 2} {F o V : PTm 1} {m ε : PTm k}
    (hmod : ∀ {a b : PTm k}, (Γ ⊢[PRAAx] le (inst2 d a b) m) →
      (Γ ⊢[PRAAx] le (inst2 dY (app1 F a) (app1 F b)) ε))
    (hcloud : ∀ {c c' : PTm k}, (Γ ⊢[PRAAx] app1 V c ≐ one) → (Γ ⊢[PRAAx] app1 V c' ≐ one) →
      (Γ ⊢[PRAAx] le (inst2 d (app1 o c) (app1 o c')) m))
    {c c' : PTm k} (hc : Γ ⊢[PRAAx] app1 V c ≐ one) (hc' : Γ ⊢[PRAAx] app1 V c' ≐ one) :
    Γ ⊢[PRAAx] le (inst2 dY (app1 F (app1 o c)) (app1 F (app1 o c'))) ε :=
  hmod (hcloud hc hc')

/-! ## Stable observable from independent certificates -/

/-- "Stable observable from independent certificates": variables of `Stab` are `p, r, c, c'`. -/
theorem stable_of_independent {Val : Fm PTm 2} {Stab : Fm PTm 4}
    (hloc : ([] : List (Fm PTm 4)) ⊢[PRAAx]
      (Val.subst ![Syn.var 0, Syn.var 2] ⟶ Val.subst ![Syn.var 1, Syn.var 3] ⟶ Stab))
    {p r c c' : PTm k} (hc : Γ ⊢[PRAAx] Val.subst ![p, c]) (hc' : Γ ⊢[PRAAx] Val.subst ![r, c']) :
    Γ ⊢[PRAAx] Stab.subst ![p, r, c, c'] := by
  have i := inst (Γ := Γ) hloc ![p, r, c, c']
  have e1 : (Val.subst ![Syn.var 0, Syn.var 2]).subst ![p, r, c, c'] = Val.subst ![p, c] := by
    rw [Fm.subst_subst]; congr 1; funext i; fin_cases i <;> rfl
  have e2 : (Val.subst ![Syn.var 1, Syn.var 3]).subst ![p, r, c, c'] = Val.subst ![r, c'] := by
    rw [Fm.subst_subst]; congr 1; funext i; fin_cases i <;> rfl
  rw [Fm.subst_imp, Fm.subst_imp, e1, e2] at i
  exact .impE (.impE i hc) hc'

/-! ## The metastable finite consumer -/

section Consumer

variable {m : ℕ}

/-- `i ∈ [N, N + G(N)]`. -/
abbrev inW (G : PTm 1) (N i : PTm m) : Fm PTm m := le N i ⋏ le i (N + app1 G N)

/-- The stable window `∀ i, j ∈ [N, N + G(N)], d(x_i, x_j) ≤ ε` of `eq:meta`. -/
abbrev Win (d : PTm 2) (G : PTm 1) (ε N : PTm m) : Fm PTm m :=
  Fm.all (Fm.all ((inW G (Syn.shift (Syn.shift N)) (Syn.var 1) ⋏ inW G (Syn.shift (Syn.shift N)) (Syn.var 0)) ⟶
    le (inst2 d (Syn.var 1) (Syn.var 0)) (Syn.shift (Syn.shift ε))))

/-- Instantiating the window at two indices. -/
theorem win_at {Δ : List (Fm PTm m)} {d : PTm 2} {G : PTm 1} {ε N i j : PTm m}
    (h : Δ ⊢[PRAAx] Win d G ε N) (hi : Δ ⊢[PRAAx] inW G N i) (hj : Δ ⊢[PRAAx] inW G N j) :
    Δ ⊢[PRAAx] le (inst2 d i j) ε := by
  have a := Prf.allE j (Prf.allE i h)
  have a' : Δ ⊢[PRAAx] (inW G N i ⋏ inW G N j) ⟶ le (inst2 d i j) ε := by
    simpa [Win, inW, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using a
  exact .impE a' (.andI hi hj)

/-- "Metastable finite-consumer theorem": a window `N ≤ M` stable to `ε` (`eq:meta` at the consumer's
control `G` and precision), the query bound `N ≤ q_t ≤ N + G(N)` for `t < L`, and the consumer's local
soundness under pairwise `ε`-stability of the queried values give `∃ N ≤ M` with the consumer contract.
`N` is variable `0` of `C`. -/
theorem finite_consumer {d q : PTm 2} {G : PTm 1} {ε M L : PTm k} {C : Fm PTm (k + 1)}
    (hmeta : Γ ⊢[PRAAx] Fm.ex (le (Syn.var 0) (Syn.shift M) ⋏ Win d G (Syn.shift ε) (Syn.var 0)))
    (hquery : ∀ {Δ : List (Fm PTm (k + 1))} {t : PTm (k + 1)}, (Δ ⊢[PRAAx] lt t (Syn.shift L)) →
      (Δ ⊢[PRAAx] inW G (Syn.var 0) (inst2 q t (Syn.var 0))))
    (hsound : ∀ {Δ : List (Fm PTm (k + 1))},
      (∀ {t t' : PTm (k + 1)}, (Δ ⊢[PRAAx] lt t (Syn.shift L)) → (Δ ⊢[PRAAx] lt t' (Syn.shift L)) →
        (Δ ⊢[PRAAx] le (inst2 d (inst2 q t (Syn.var 0)) (inst2 q t' (Syn.var 0))) (Syn.shift ε))) →
      (Δ ⊢[PRAAx] C)) :
    Γ ⊢[PRAAx] Fm.ex (le (Syn.var 0) (Syn.shift M) ⋏ C) := by
  refine ex_mono hmeta ?_
  have hA : ((le (Syn.var 0) (Syn.shift M) ⋏ Win d G (Syn.shift ε) (Syn.var 0)) :: Γ.map Fm.shift) ⊢[PRAAx]
      (le (Syn.var 0) (Syn.shift M) ⋏ Win d G (Syn.shift ε) (Syn.var 0)) := Prf.hyp0
  exact .andI (Prf.andE₁ hA) (hsound fun ht ht' => win_at (Prf.andE₂ hA) (hquery ht) (hquery ht'))

/-- With a primitive-recursive producer of the window base `N`, the output is at that `N`. -/
theorem finite_consumer_at {d q : PTm 2} {G : PTm 1} {ε L N : PTm k} {C : Fm PTm k}
    (hwin : Γ ⊢[PRAAx] Win d G ε N)
    (hquery : ∀ {t : PTm k}, (Γ ⊢[PRAAx] lt t L) → (Γ ⊢[PRAAx] inW G N (inst2 q t N)))
    (hsound : (∀ {t t' : PTm k}, (Γ ⊢[PRAAx] lt t L) → (Γ ⊢[PRAAx] lt t' L) →
        (Γ ⊢[PRAAx] le (inst2 d (inst2 q t N) (inst2 q t' N)) ε)) → (Γ ⊢[PRAAx] C)) :
    Γ ⊢[PRAAx] C :=
  hsound fun ht ht' => win_at hwin (hquery ht) (hquery ht')

end Consumer

end LeanProofs.IPRA.Foundations.ObserverGuards
