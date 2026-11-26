import IPRADerivations.Probability.DyadicSLLN

/-!
# The union over the dyadic blocks

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, proof of `thm:dyadic-slln`:
"The union bound over `r ≥ K` up to the last block is at most the infinite geometric majorant … `σ²/(ε² 2^K)`".

With the block probabilities `P_j = Pblk(K + j)` of `DyadicSLLN` as a body in the block index `j` (`pjB`, `inst2_pjB`),
`DyadicSLLN.block_hyp` is the hypothesis of `DyadicUnion.dyadic_union` for `c = e² W²` and `B = (WQ ∸ S²) T_H`:

* `union_bound`: `e² W² 2^K Σ_{j<J} P_j ≤ (WQ ∸ S²) T_H` for every number `J` of blocks — the bad-block probabilities of
  the blocks `K, …, K + J − 1` sum to at most `σ²/(e² 2^K)` (in units of the total mass `T_H`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicAssembly

open_ipra
open LeanProofs.IPRA.Probability.ProductPower (Tt)
open LeanProofs.IPRA.Probability.DyadicBlock (pcB Pc)
open LeanProofs.IPRA.Probability.DyadicSLLN (lw aB Nm Pblk block_hyp)
open LeanProofs.IPRA.Probability.DyadicUnion (UF dyadic_union)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Union

variable (w0 X0 : PTm 2)

/-- `P_j = Pblk(K + j)` over `(j, ⟨K, ⟨e, ⟨H, ⟨M, x⟩⟩⟩⟩)`. -/
def pjB : PTm 2 :=
  ap2 (sumF (pcB (lw w0) (lw X0) (aB w0))) (pw (fstT (sndT (sndT (sndT (var 1))))) (fstT (sndT (sndT (var 1)))))
    (pairT (Nm (fstT (var 1) + var 0) (fstT (sndT (sndT (var 1)))))
      (pairT (fstT (sndT (sndT (var 1))))
        (pairT (fstT (sndT (sndT (sndT (var 1)))))
          (pairT (pairT (fstT (var 1) + var 0) (fstT (sndT (var 1)))) (sndT (sndT (sndT (sndT (var 1)))))))))

abbrev Yb (K e H M x : PTm n) : PTm n := pairT K (pairT e (pairT H (pairT M x)))

theorem Nm_congr {r r' H H' : PTm n} (er : Γ ⊢[PRAAx] r ≐ r') (eH : Γ ⊢[PRAAx] H ≐ H') :
    Γ ⊢[PRAAx] Nm r H ≐ Nm r' H' :=
  congrMonus (congrAp2 powF (congrSucc er) (.eqRefl _)) (congrMonus (congrAp2 powF (congrSucc er) (.eqRefl _)) eH)

theorem inst2_pjB (j K e H M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pjB w0 X0) j (Yb K e H M x) ≐ Pblk w0 X0 (K + j) e H M x := by
  have h : inst2 (pjB w0 X0) j (Yb K e H M x) =
      ap2 (sumF (pcB (lw w0) (lw X0) (aB w0)))
        (pw (fstT (sndT (sndT (sndT (Yb K e H M x))))) (fstT (sndT (sndT (Yb K e H M x)))))
        (pairT (Nm (fstT (Yb K e H M x) + j) (fstT (sndT (sndT (Yb K e H M x)))))
          (pairT (fstT (sndT (sndT (Yb K e H M x))))
            (pairT (fstT (sndT (sndT (sndT (Yb K e H M x)))))
              (pairT (pairT (fstT (Yb K e H M x) + j) (fstT (sndT (Yb K e H M x))))
                (sndT (sndT (sndT (sndT (Yb K e H M x))))))))) := by
    simp [pjB, inst2]
  rw [h]
  have s1 : Γ ⊢[PRAAx] sndT (Yb K e H M x) ≐ pairT e (pairT H (pairT M x)) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Yb K e H M x)) ≐ pairT H (pairT M x) := s1.sndE
  have s3 : Γ ⊢[PRAAx] sndT (sndT (sndT (Yb K e H M x))) ≐ pairT M x := s2.sndE
  have hK : Γ ⊢[PRAAx] fstT (Yb K e H M x) ≐ K := fst_pair _ _
  have he : Γ ⊢[PRAAx] fstT (sndT (Yb K e H M x)) ≐ e := s1.fstE
  have hH : Γ ⊢[PRAAx] fstT (sndT (sndT (Yb K e H M x))) ≐ H := s2.fstE
  have hM : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (Yb K e H M x)))) ≐ M := s3.fstE
  have hx : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (Yb K e H M x)))) ≐ x := s3.sndE
  have hr : Γ ⊢[PRAAx] fstT (Yb K e H M x) + j ≐ K + j := congrAdd hK (.eqRefl _)
  exact congrAp2 _ (congrAp2 powF hH hM)
    (congrPairT (Nm_congr hr hH) (congrPairT hH (congrPairT hM (congrPairT (congrPairT hr he) hx))))

/-- `e² W² 2^K Σ_{j<J} P_j ≤ (WQ ∸ S²) T_H`. -/
theorem union_bound {M x H : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w0) M x ≐ succ (pred (ap2 (sumF w0) M x))) (K e J : PTm n) :
    Γ ⊢[PRAAx] le (e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x) * pw two K * ap2 (sumF (pjB w0 X0)) J (Yb K e H M x))
      (monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
        (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have hW' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF w0) (Syn.shift M) (Syn.shift x) ≐
      succ (pred (ap2 (sumF w0) (Syn.shift M) (Syn.shift x))) := by
    simpa [Fm.shift, Syn.shift] using hW.shift
  have u := dyadic_union (P := pjB w0 X0) (c := e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x)) (K := K)
    (B := monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
      (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) (x := Yb K e H M x) (J := J)
    (.allI (.impI (by
      have b := block_hyp (Γ := lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) w0 X0 hM'.wk hW'.wk (Syn.shift K + var 0) (Syn.shift e) (H := Syn.shift H)
      have eq := inst2_pjB (Γ := lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) w0 X0 (var 0) (Syn.shift K) (Syn.shift e)
        (Syn.shift H) (Syn.shift M) (Syn.shift x)
      have s1 : Syn.shift (Yb K e H M x) = Yb (Syn.shift K) (Syn.shift e) (Syn.shift H) (Syn.shift M) (Syn.shift x) := by
        simp [Syn.shift]
      have s2 : Syn.shift (e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x)) =
          Syn.shift e * Syn.shift e * (ap2 (sumF w0) (Syn.shift M) (Syn.shift x) * ap2 (sumF w0) (Syn.shift M) (Syn.shift x)) := by
        simp [Syn.shift]
      have s3 : Syn.shift (monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
          (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) =
          monus (ap2 (sumF w0) (Syn.shift M) (Syn.shift x) * ap2 (sumF (w0 * (X0 * X0))) (Syn.shift M) (Syn.shift x))
            (ap2 (sumF (w0 * X0)) (Syn.shift M) (Syn.shift x) * ap2 (sumF (w0 * X0)) (Syn.shift M) (Syn.shift x)) *
            Tt w0 (Syn.shift H) (Syn.shift M) (Syn.shift x) := by
        simp [Syn.shift]
      rw [s1, s2, s3]
      exact le_congr (congrMul (.eqRefl _) eq.eqSymm) (.eqRefl _) b)))
  -- `c 2^K 2^J S + B ≤ 2^J B` gives `c 2^K S ≤ B`
  have pJ := AnalyticNumberTheory.Valuation.pw_pos' (congrSucc (pred_succ _).eqSymm : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two)) J
  have ep := natEq pJ
  refine Geometry.HypercubeSplit.le_cancel_pos pJ (le_of_eq_add (d := monus (pw two J *
      (monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
        (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x))
      (e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x) * pw two K * pw two J * ap2 (sumF (pjB w0 X0)) J (Yb K e H M x) +
        monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
          (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) +
      monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
        (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) ?_)
  ipra_lc natEq (eq_add_of_le u)

end Union

end LeanProofs.IPRA.Probability.DyadicAssembly
