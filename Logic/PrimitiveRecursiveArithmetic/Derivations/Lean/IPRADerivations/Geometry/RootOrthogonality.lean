import IPRADerivations.Core.SumSplit

/-!
# Finite orthogonality by pairing (`isoperimetric_ipra`, `lem:ortho`)

Packet: `geometry/isoperimetric_ipra`, lemma `lem:ortho` (5.3): `∑_{j<N} ζ^{hj} = 0` for
`N ∤ h`. Proof: "Put `M = N/2^{v+1}`. Then `ζ^{hM} = ζ^{bN/2} = −1`. In every consecutive block
of `2M` indices, the second half cancels the first. This is a finite pairing argument; no
algebraic inverse or analytic geometric-series limit occurs."

The pairing argument, for an arbitrary integer-valued sequence `z(j) = p(j) − q(j)` given by two
natural-number bodies (the real or the imaginary part of `ζ^{hj}` at a fixed precision is of
this form), with half-period `M` and `z(M + j) = −z(j)`:

* `antiF p q M x`: the hypothesis, `p(M + j) + p(j) = q(M + j) + q(j)` for all `j`;
* `block_cancel`: a block of `2M` consecutive indices at any offset `B` has
  `∑ p = ∑ q`: its second half cancels its first;
* `blocks_cancel`: `K` consecutive blocks: `∑_{j < K·2M} p(j) = ∑_{j < K·2M} q(j)`, that is
  `∑_{j<N} z(j) = 0` for `N = 2MK`.

Reusable tools:

* `allE_under`: a hypothesis `Γ ⊢ ∀ j, φ(j)` used at an arbitrary term under one binder,
  `Γ.map shift ⊢ φ(t)`;
* `sum_pair_congr`: `f₁(i) + f₂(i) = g₁(i) + g₂(i)` for `i < N`, the four bodies with their
  own parameters, gives `∑ f₁ + ∑ f₂ = ∑ g₁ + ∑ g₂`.

Not derived: the reduction of `h` modulo `N` and the `2`-adic splitting `h = 2^v b` that
produce `M`, and the root-of-unity names themselves.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.RootOrthogonality

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A universal hypothesis under a binder -/

/-- `Γ ⊢ ∀ j, φ(j)` gives `Γ.map shift ⊢ φ(t)` for every term `t` of the extended context. -/
theorem allE_under {φ : Fm PTm (n + 1)} (H : Γ ⊢[PRAAx] Fm.all φ) (t : PTm (n + 1)) :
    (Γ.map Fm.shift) ⊢[PRAAx] φ.subst (Syn.repl t) := by
  have h := H.allOpen.subst (Syn.repl t)
  have e : (Γ.map Fm.shift).map (fun ψ => ψ.subst (Syn.repl t)) = Γ.map Fm.shift := by
    rw [List.map_map]
    refine List.map_congr_left fun ψ _ => ?_
    show (Fm.shift ψ).subst (Syn.repl t) = Fm.shift ψ
    rw [Fm.subst_shift]
    simp [Fm.shift, Syn.repl_succ]
  rw [e] at h
  exact h

theorem subst_up_shift (t : PTm n) :
    Syn.subst (Syn.up fun i : Fin n => (Syn.var i.succ : PTm (n + 1))) (Syn.shift t) =
      Syn.shift (Syn.shift t) := by
  rw [Syn.subst_shift]
  simp only [Syn.up_succ]
  exact (Syn.shift_subst _ _).symm

theorem shift_pair (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-! ## Four sums -/

/-- The induction formula of `sum_pair_congr`; variable `0` is the upper limit. -/
abbrev pairF (f₁ f₂ g₁ g₂ : PTm 2) (N x₁ x₂ y₁ y₂ : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift N) ⟶
    (ap2 (sumF f₁) (var 0) (Syn.shift x₁) + ap2 (sumF f₂) (var 0) (Syn.shift x₂) ≐
      ap2 (sumF g₁) (var 0) (Syn.shift y₁) + ap2 (sumF g₂) (var 0) (Syn.shift y₂))

/-- `∑ f₁ + ∑ f₂ = ∑ g₁ + ∑ g₂` from the same relation between the terms below `N`. -/
theorem sum_pair_congr (f₁ f₂ g₁ g₂ : PTm 2) {N x₁ x₂ y₁ y₂ : PTm n}
    (H : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f₁ (var 0) (Syn.shift x₁) + inst2 f₂ (var 0) (Syn.shift x₂) ≐
        inst2 g₁ (var 0) (Syn.shift y₁) + inst2 g₂ (var 0) (Syn.shift y₂)))) :
    Γ ⊢[PRAAx] ap2 (sumF f₁) N x₁ + ap2 (sumF f₂) N x₂ ≐
      ap2 (sumF g₁) N y₁ + ap2 (sumF g₂) N y₂ := by
  have hall : Γ ⊢[PRAAx] Fm.all (pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
    · refine .impI ?_
      have a₁ := natEq (sum_zero (Γ := le zero N :: Γ) f₁ x₁)
      have a₂ := natEq (sum_zero (Γ := le zero N :: Γ) f₂ x₂)
      have b₁ := natEq (sum_zero (Γ := le zero N :: Γ) g₁ y₁)
      have b₂ := natEq (sum_zero (Γ := le zero N :: Γ) g₂ y₂)
      apply deriveNat; ipra_simps
      linear_combination a₁ + a₂ - b₁ - b₂
    · refine .impI ?_
      have ih := natEq (Prf.impE (Prf.hyp1 (Γ := Γ.map Fm.shift)
        (φ := pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂) (ψ := le (succ (var 0)) (Syn.shift N)))
        (le_trans (le_succ_self _) Prf.hyp0))
      have pt := natEq (Prf.impE H.allOpen.wk.wk
        (Prf.hyp0 (Γ := pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂ :: Γ.map Fm.shift)
          (φ := le (succ (var 0)) (Syn.shift N))))
      have a₁ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂ :: Γ.map Fm.shift) f₁ (var 0) (Syn.shift x₁))
      have a₂ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂ :: Γ.map Fm.shift) f₂ (var 0) (Syn.shift x₂))
      have b₁ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂ :: Γ.map Fm.shift) g₁ (var 0) (Syn.shift y₁))
      have b₂ := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        pairF f₁ f₂ g₁ g₂ N x₁ x₂ y₁ y₂ :: Γ.map Fm.shift) g₂ (var 0) (Syn.shift y₂))
      apply deriveNat; ipra_simps
      linear_combination a₁ + a₂ - b₁ - b₂ + ih + pt
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## One block -/

section Blocks

variable (p q : PTm 2)

/-- `z(M + j) = −z(j)` for all `j`, in parts: `p(M + j) + p(j) = q(M + j) + q(j)`. -/
abbrev antiF (M x : PTm n) : Fm PTm n :=
  Fm.all (inst2 p (Syn.shift M + var 0) (Syn.shift x) + inst2 p (var 0) (Syn.shift x) ≐
    inst2 q (Syn.shift M + var 0) (Syn.shift x) + inst2 q (var 0) (Syn.shift x))

theorem shift_anti (M x : PTm n) :
    Fm.shift (antiF p q M x) = antiF p q (Syn.shift M) (Syn.shift x) := by
  simp only [Fm.shift, Fm.subst_all, Fm.subst_eq, PTm.subst_add, subst_inst2, Syn.subst_var,
    Syn.up_zero, subst_up_shift]

/-- `g(B + i, x)` as a body with the parameter `⟨B, x⟩`. -/
theorem off_at (g : PTm 2) (i B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB g) i (pairT B x) ≐ inst2 g (B + i) x := by
  rw [inst2_offB]
  exact congrInst2 g (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem off2_at (g : PTm 2) (j M B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB (offB g)) j (pairT M (pairT B x)) ≐ inst2 g (M + (B + j)) x := by
  refine (off_at (offB g) j M (pairT B x)).eqTrans ((off_at g (M + j) B x).eqTrans ?_)
  refine congrInst2 g ?_ (.eqRefl x)
  ipra_ring

theorem block_point {M B x j : PTm n}
    (h : Γ ⊢[PRAAx] inst2 p (M + (B + j)) x + inst2 p (B + j) x ≐
      inst2 q (M + (B + j)) x + inst2 q (B + j) x) :
    Γ ⊢[PRAAx] inst2 (offB (offB p)) j (pairT M (pairT B x)) + inst2 (offB p) j (pairT B x) ≐
      inst2 (offB (offB q)) j (pairT M (pairT B x)) + inst2 (offB q) j (pairT B x) :=
  (congrAdd (off2_at p j M B x) (off_at p j B x)).eqTrans
    (h.eqTrans (congrAdd (off2_at q j M B x) (off_at q j B x)).eqSymm)

/-- A block of `2M` consecutive indices at offset `B`: the second half cancels the first. -/
theorem block_cancel {M x : PTm n} (B : PTm n) (H : Γ ⊢[PRAAx] antiF p q M x) :
    Γ ⊢[PRAAx] ap2 (sumF (offB p)) (M + M) (pairT B x) ≐
      ap2 (sumF (offB q)) (M + M) (pairT B x) := by
  have sp := sum_split (Γ := Γ) (offB p) M M (pairT B x)
  have sq := sum_split (Γ := Γ) (offB q) M M (pairT B x)
  have key := sum_pair_congr (Γ := Γ) (offB (offB p)) (offB p) (offB (offB q)) (offB q)
    (N := M) (x₁ := pairT M (pairT B x)) (x₂ := pairT B x)
    (y₁ := pairT M (pairT B x)) (y₂ := pairT B x) (.allI (.impI (by
      simp only [shift_pair]
      have h := allE_under H (Syn.shift B + var 0)
      have h' : (Γ.map Fm.shift) ⊢[PRAAx]
          inst2 p (Syn.shift M + (Syn.shift B + var 0)) (Syn.shift x) +
            inst2 p (Syn.shift B + var 0) (Syn.shift x) ≐
          inst2 q (Syn.shift M + (Syn.shift B + var 0)) (Syn.shift x) +
            inst2 q (Syn.shift B + var 0) (Syn.shift x) := by
        simpa [subst_repl_shift, Syn.repl_zero] using h
      exact block_point p q h'.wk)))
  refine sp.eqTrans (.eqTrans ?_ sq.eqSymm)
  ipra_lc natEq key

end Blocks

/-! ## Consecutive blocks -/

/-- One more block. -/
theorem blocks_step (p q : PTm 2) {M x K : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF p) (K * (M + M)) x ≐ ap2 (sumF q) (K * (M + M)) x)
    (H : Γ ⊢[PRAAx] antiF p q M x) :
    Γ ⊢[PRAAx] ap2 (sumF p) (succ K * (M + M)) x ≐ ap2 (sumF q) (succ K * (M + M)) x := by
  have eb : Γ ⊢[PRAAx] succ K * (M + M) ≐ K * (M + M) + (M + M) := by
    ipra_ring
  have sp := (congrAp2 (sumF p) eb (.eqRefl x)).eqTrans (sum_split p (K * (M + M)) (M + M) x)
  have sq := (congrAp2 (sumF q) eb (.eqRefl x)).eqTrans (sum_split q (K * (M + M)) (M + M) x)
  exact sp.eqTrans ((congrAdd ih (block_cancel p q (K * (M + M)) H)).eqTrans sq.eqSymm)

/-- The induction formula; variable `0` is the number of blocks. -/
abbrev blocksF (p q : PTm 2) (M x : PTm n) : Fm PTm (n + 1) :=
  ap2 (sumF p) (var 0 * (Syn.shift M + Syn.shift M)) (Syn.shift x) ≐
    ap2 (sumF q) (var 0 * (Syn.shift M + Syn.shift M)) (Syn.shift x)

/-- `lem:ortho`, the pairing argument: over `K` consecutive blocks of `2M` indices the
positive and the negative parts have equal sums, `∑_{j < K·2M} z(j) = 0`. -/
theorem blocks_cancel (p q : PTm 2) {M x : PTm n} (K : PTm n) (H : Γ ⊢[PRAAx] antiF p q M x) :
    Γ ⊢[PRAAx] ap2 (sumF p) (K * (M + M)) x ≐ ap2 (sumF q) (K * (M + M)) x := by
  have hall : Γ ⊢[PRAAx] Fm.all (blocksF p q M x) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] ap2 (sumF p) (zero * (M + M)) x ≐ ap2 (sumF q) (zero * (M + M)) x :=
        (congrAp2 (sumF p) (zero_mul _) (.eqRefl x)).eqTrans ((sum_zero p x).eqTrans
          ((sum_zero q x).eqSymm.eqTrans (congrAp2 (sumF q) (zero_mul _) (.eqRefl x)).eqSymm))
      simpa using b
    · have H' : (Γ.map Fm.shift) ⊢[PRAAx] antiF p q (Syn.shift M) (Syn.shift x) := by
        rw [← shift_anti]
        exact H.shift
      have st : (blocksF p q M x :: Γ.map Fm.shift) ⊢[PRAAx]
          ap2 (sumF p) (succ (var 0) * (Syn.shift M + Syn.shift M)) (Syn.shift x) ≐
            ap2 (sumF q) (succ (var 0) * (Syn.shift M + Syn.shift M)) (Syn.shift x) :=
        blocks_step p q Prf.hyp0 H'.wk
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE K hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

end LeanProofs.IPRA.Geometry.RootOrthogonality
