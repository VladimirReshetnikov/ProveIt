import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Core.OrderCertificates

/-!
# Iterates of a contraction on an invariant ball

Packet: `foundations/ipra_framework`, `paper/sections/06_analysis.tex`, Theorem `ana:series` ("Certified
power-series branch"), item 1, `eq:ana:iterate`: under the contraction contract `ana:contract` (by
`ana:contraction`, `F` maps the ball `‖V‖_R ≤ ρ` to itself and halves distances on it), the Picard iterates
`Z_0 = 0`, `Z_{n+1} = F(Z_n)` satisfy, for `m ≥ n`,
`‖Z_n‖_R ≤ ρ` and `‖Z_m − Z_n‖_R ≤ ρ 2^{−n}`.

The space is abstract: codes `s`, a ball test `B(s) = 1` (`‖s‖_R ≤ ρ`, e.g. after truncation modulo
`X^{K+1}`), a cleared distance `d(s, t)` and the step `F`; `Contr` holds the two conclusions of
`ana:contraction` as rules.

* `iter_add`: `F^{j+n}(x) = F^n(F^j(x))`;
* `CInv`, `contract_step`, `iter_contract`: for `V`, `W` in the ball, `F^n V` and `F^n W` stay in the ball and
  `2^n d(F^n V, F^n W) ≤ d(V, W)` (quantifier-free induction on `n`);
* `cauchy_iterates` (`eq:ana:iterate`): with `Z_0` in the ball and `d(s, Z_0) ≤ ρ` on the ball,
  `Z_n` is in the ball and `2^n d(Z_{j+n}, Z_n) ≤ ρ`, since `Z_{j+n} = F^n(Z_j)` and `Z_n = F^n(Z_0)`.

The coefficient names `c_k` (item 2) and the majorant arithmetic behind `ana:contraction` are not derived
here.
-/

namespace LeanProofs.IPRA.Foundations.ContractionIterates

open_ipra exports

variable {k : ℕ} {Γ : List (Fm PTm k)}

@[simp] theorem subst_one' {m : ℕ} (σ : Fin k → PTm m) : Syn.subst σ (one : PTm k) = one := by
  simp only [one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] theorem subst_two' {m : ℕ} (σ : Fin k → PTm m) : Syn.subst σ (two : PTm k) = two := by
  simp only [two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem congrIter (f : PTm 1) {n n' x x' : PTm k} (h₁ : Γ ⊢[PRAAx] n ≐ n') (h₂ : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] iter f n x ≐ iter f n' x' :=
  congrAp2 _ h₁ h₂

/-- `F^{j+n}(x) = F^n(F^j(x))`. -/
theorem iter_add (f : PTm 1) (j n x : PTm k) : Γ ⊢[PRAAx] iter f (j + n) x ≐ iter f n (iter f j x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (iter f (Syn.shift j + Syn.var 0) (Syn.shift x) ≐
      iter f (Syn.var 0) (iter f (Syn.shift j) (Syn.shift x))) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact (congrIter f (add_zero _) (.eqRefl _)).eqTrans (iter_zero f _).eqSymm
    · have ih : ((iter f (Syn.shift j + Syn.var 0) (Syn.shift x) ≐
          iter f (Syn.var 0) (iter f (Syn.shift j) (Syn.shift x))) :: Γ.map Fm.shift) ⊢[PRAAx]
          iter f (Syn.shift j + Syn.var 0) (Syn.shift x) ≐
            iter f (Syn.var 0) (iter f (Syn.shift j) (Syn.shift x)) := Prf.hyp0
      exact ((congrIter f (add_succ _ _) (.eqRefl _)).eqTrans (iter_succ f _ _)).eqTrans
        ((congrApp1 f ih).eqTrans (iter_succ f _ _).eqSymm)
  have h2 := Prf.allE n hall
  simpa only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using h2

/-- The two conclusions of `ana:contraction`, as rules: `F` preserves the ball and halves distances on it. -/
structure Contr (F B : PTm 1) (d : PTm 2) : Prop where
  pres : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 B s ≐ one) → (Γ ⊢[PRAAx] app1 B (app1 F s) ≐ one)
  half : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s t : PTm k},
    (Γ ⊢[PRAAx] app1 B s ≐ one) → (Γ ⊢[PRAAx] app1 B t ≐ one) →
      (Γ ⊢[PRAAx] le (two * inst2 d (app1 F s) (app1 F t)) (inst2 d s t))

variable {F B : PTm 1} {d : PTm 2}

/-- `F^n V`, `F^n W` in the ball and `2^n d(F^n V, F^n W) ≤ d(V, W)`. -/
abbrev CInv (F B : PTm 1) (d : PTm 2) (V W n : PTm k) : Fm PTm k :=
  ((app1 B (iter F n V) ≐ one) ⋏ (app1 B (iter F n W) ≐ one)) ⋏
    le (pw two n * inst2 d (iter F n V) (iter F n W)) (inst2 d V W)

theorem contract_step (H : Contr F B d) {V W n : PTm k} (ih : Γ ⊢[PRAAx] CInv F B d V W n) :
    Γ ⊢[PRAAx] CInv F B d V W (succ n) := by
  have hv := Prf.andE₁ (Prf.andE₁ ih)
  have hw := Prf.andE₂ (Prf.andE₁ ih)
  have hle := Prf.andE₂ ih
  have sV := iter_succ (Γ := Γ) F n V
  have sW := iter_succ (Γ := Γ) F n W
  have hh := H.half hv hw
  refine .andI (.andI ((congrApp1 B sV).eqTrans (H.pres hv)) ((congrApp1 B sW).eqTrans (H.pres hw))) ?_
  have p := natEq (pw_succ (Γ := Γ) two n)
  have e := natEq (congrInst2 d sV sW)
  ipra_le 𝔞 (pw two n) * sl hh + sl hle using rw [p, e]; ring

/-- For `V`, `W` in the ball: `F^n V`, `F^n W` stay in the ball and `2^n d(F^n V, F^n W) ≤ d(V, W)`. -/
theorem iter_contract (H : Contr F B d) {V W : PTm k} (hV : Γ ⊢[PRAAx] app1 B V ≐ one)
    (hW : Γ ⊢[PRAAx] app1 B W ≐ one) (n : PTm k) : Γ ⊢[PRAAx] CInv F B d V W n := by
  have hall : Γ ⊢[PRAAx] Fm.all (CInv F B d (Syn.shift V) (Syn.shift W) (Syn.var 0)) := by
    ipra_qfind (⟨⟨trivial, trivial⟩, le_QF _ _⟩) [subst_le, subst_ap2, subst_app1, subst_inst2, subst_one', subst_two']
    · have zV := iter_zero (Γ := Γ) F V
      have zW := iter_zero (Γ := Γ) F W
      refine .andI (.andI ((congrApp1 B zV).eqTrans hV) ((congrApp1 B zW).eqTrans hW)) ?_
      have p := natEq (pw_zero (Γ := Γ) two)
      have e := natEq (congrInst2 d zV zW)
      ipra_le 0 using rw [p, e]; ring
    · exact contract_step H Prf.hyp0
  have h2 := Prf.allE n hall
  simpa only [Fm.subst_and, Fm.subst_eq, subst_le, subst_ap2, subst_app1, subst_inst2, PTm.subst_mul, subst_one', subst_two',
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h2

/-- `eq:ana:iterate`: `Z_n` is in the ball and `2^n d(Z_{j+n}, Z_n) ≤ ρ`, for `Z_i = F^i(Z_0)`. -/
theorem cauchy_iterates (H : Contr F B d) {z₀ ρ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 B z₀ ≐ one)
    (hrad : ∀ {s : PTm k}, (Γ ⊢[PRAAx] app1 B s ≐ one) → (Γ ⊢[PRAAx] le (inst2 d s z₀) ρ)) (j n : PTm k) :
    Γ ⊢[PRAAx] (app1 B (iter F n z₀) ≐ one) ⋏
      le (pw two n * inst2 d (iter F (j + n) z₀) (iter F n z₀)) ρ := by
  have hj := Prf.andE₁ (Prf.andE₁ (iter_contract H h₀ h₀ j))
  have c := iter_contract H hj h₀ n
  refine .andI (Prf.andE₂ (Prf.andE₁ c)) ?_
  have r := hrad hj
  have e := natEq (congrInst2 (Γ := Γ) d (iter_add F j n z₀) (.eqRefl (iter F n z₀)))
  have hc := Prf.andE₂ c
  ipra_le sl hc + sl r using rw [e]; ring

end LeanProofs.IPRA.Foundations.ContractionIterates
