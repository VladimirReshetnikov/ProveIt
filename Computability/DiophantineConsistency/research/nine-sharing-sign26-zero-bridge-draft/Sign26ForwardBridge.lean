import DiophantineConsistency.Sign26CoordinateDrop
import DiophantineConsistency.Sign26SeedGap

/-! SOURCE-ONLY: forward zero assembly using a represented gap and q3. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed27Sextic.firstResidual p :: SharingSeed27Sextic.remainingResiduals p =
      [SharingSeed27Sextic.firstResidual p,
       Sign26RemainingCuts.oldR01 p,
       Sign26RemainingCuts.oldR02 p,
       Sign26RemainingCuts.oldR03 p,
       Sign26RemainingCuts.oldR04 p,
       Sign26RemainingCuts.oldR05 p,
       Sign26RemainingCuts.oldR06 p,
       Sign26RemainingCuts.oldR07 p,
       Sign26CongruenceCuts.oldGap p,
       Sign26CongruenceCuts.oldTau p,
       Sign26RemainingCuts.oldR10 p,
       Sign26RemainingCuts.oldR11 p,
       Sign26CongruenceCuts.oldInner p,
       Sign26RemainingCuts.oldR13 p,
       Sign26RemainingCuts.oldR14 p,
       Sign26RemainingCuts.oldR15 p,
       Sign26RemainingCuts.oldR16 p,
       Sign26RemainingCuts.oldR17 p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta K : V) (v : Fin 27 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hbeta : 1 ≤ beta) (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    ∃ gap : V, ι gap = Sign26CongruenceCuts.ringGap p v ∧
      InternalZero (SharingSeed27Sextic.seed p) (Sign26CongruenceCuts.lift gap v) := by
  obtain ⟨gap, hg⟩ := Sign26SeedGap.exists_gap p beta K v hp0 hp1 hbeta hz
  have hgap : ι gap = Sign26CongruenceCuts.ringGap p v := by
    simpa only [Sign26CongruenceCuts.ringGap] using hg
  have hq3 := Sign26ZeroExtraction.q3_eq p v hz
  refine ⟨gap, hgap, ?_⟩
  have hn := (SharingSign26Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign27Squares.seed_zero_iff_residuals p (Sign26CongruenceCuts.lift gap v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.first_eval p v gap)).mpr (hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R01_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R02_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R03_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R03_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R04_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R04_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R05_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R06_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R06_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R07_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R07_row p)))))
  · exact Sign26CongruenceCuts.oldGap_zero p v gap hgap
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.Tau_eval p v gap hgap hq3)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26CongruenceCuts.new_Tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R10_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R11_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.Inner_eval p v gap hgap hq3)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26CongruenceCuts.new_Inner_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R13_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R14_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R15_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R15_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R16_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R16_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R17_eval p v gap)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.new_R17_row p)))))
end DiophantineConsistency.Sign26ZeroBridge
#print axioms DiophantineConsistency.Sign26ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign26ZeroBridge.forward
