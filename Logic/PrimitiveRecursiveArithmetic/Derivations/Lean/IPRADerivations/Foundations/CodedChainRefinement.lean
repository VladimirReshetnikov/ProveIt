import IPRADerivations.Foundations.ViableChainSelection
import IPRADerivations.Core.SubstCommand

/-!
# Bounded object-evidence refinement of numerical chain codes

Source: `ipra_evidence_framework/report.tex`, "Constraint refinement under
stronger evidence", lines 54--62. Strong and weak instances share the exact
candidate-bound and horizon syntax. The input is an OBJECT formula of
bounded inequalities between sg-normalized local and edge tests. Thus raw
tests need no Boolean premise; on bits these are exactly the source Boolean
inequalities. Applying this evidence at the actual decoded labels proves
that the SAME numerical strong code is a weak admissible code.

Actual generated codes, tagged returned codes, bounded coded existence and
success transfer from strong to weak. Existence after adding constraints is
not inferred. Only fixed instance/test syntax is external; data, codes,
levels and candidate labels remain numerical object variables.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CodedChainRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain (start)
open LeanProofs.IPRA.Foundations.CodedViableChain (admissibleCode viableStart codeBound)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem up_two {m : ℕ} (σ : Fin (n+2) → PTm m) : Syn.up σ 2 = Syn.shift (σ 1) := Syn.up_succ σ 1
@[simp] theorem up_shift {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift,Syn.shift_subst]
  simp

def strong (I : Instance) (G : PTm 3) (T : PTm 4) : Instance :=
  { G := G, T := T, B := I.B, hz := I.hz }

def localComparison (I : Instance) (G : PTm 3) (i a p : PTm n) : Fm PTm n :=
  le (sg ((strong I G I.T).g i a p)) (sg (I.g i a p))
def edgeComparison (I : Instance) (T : PTm 4) (i a b p : PTm n) : Fm PTm n :=
  le (sg ((strong I I.G T).t i a b p)) (sg (I.t i a b p))

def localEvidence (I : Instance) (G : PTm 3) (p : PTm n) : Fm PTm n := .all
  (le (var 0) (I.h (Syn.shift p)) ⟶ .all
    (lt (var 0) (I.bd (var 1) (Syn.shift (Syn.shift p))) ⟶
      localComparison I G (var 1) (var 0) (Syn.shift (Syn.shift p))))
def edgeEvidence (I : Instance) (T : PTm 4) (p : PTm n) : Fm PTm n := .all
  (lt (var 0) (I.h (Syn.shift p)) ⟶ .all
    (lt (var 0) (I.bd (var 1) (Syn.shift (Syn.shift p))) ⟶ .all
      (lt (var 0) (I.bd (succ (var 2)) (Syn.shift (Syn.shift (Syn.shift p)))) ⟶
        edgeComparison I T (var 2) (var 1) (var 0) (Syn.shift (Syn.shift (Syn.shift p))))))
def evidence (I : Instance) (G : PTm 3) (T : PTm 4) (p : PTm n) : Fm PTm n :=
  localEvidence I G p ⋏ edgeEvidence I T p

ipra_subst localComparison [sg]
ipra_subst edgeComparison [sg]
ipra_subst localEvidence [Syn.subst_shift, Syn.shift_subst]
ipra_subst edgeEvidence [Syn.subst_shift, Syn.shift_subst]
ipra_subst evidence

/-- The only Boolean normalization used in refinement is derived from raw
nonzeroness. No bit/value property of G or T is supplied. -/
theorem nonzero_of_sg_le {a b : PTm n} (hab : Γ ⊢[PRAAx] le (sg a) (sg b))
    (ha : Γ ⊢[PRAAx] neg (a ≐ zero)) : Γ ⊢[PRAAx] neg (b ≐ zero) := by
  refine .impI ?_
  have impossible := le_congr (FiniteGluing.sg_of_ne ha.wk) (BoundedFormulas.sg_of_zero Prf.hyp0) hab.wk
  exact BoundedReflection.one_ne_zero _ ((monus_zero one).eqSymm.eqTrans impossible)

theorem local_evidence_at (I : Instance) (G : PTm 3) (p i a : PTm n)
    (h : Γ ⊢[PRAAx] localEvidence I G p) (hi : Γ ⊢[PRAAx] le i (I.h p))
    (ha : Γ ⊢[PRAAx] lt a (I.bd i p)) : Γ ⊢[PRAAx] localComparison I G i a p := by
  have level : Γ ⊢[PRAAx] le i (I.h p) ⟶ .all
      (lt (var 0) (I.bd (Syn.shift i) (Syn.shift p)) ⟶ localComparison I G (Syn.shift i) (var 0) (Syn.shift p)) := by
    simpa [localEvidence] using h.allE i
  have candidate : Γ ⊢[PRAAx] lt a (I.bd i p) ⟶ localComparison I G i a p := by
    simpa using (Prf.impE level hi).allE a
  exact .impE candidate ha

theorem edge_evidence_at (I : Instance) (T : PTm 4) (p i a b : PTm n)
    (h : Γ ⊢[PRAAx] edgeEvidence I T p) (hi : Γ ⊢[PRAAx] lt i (I.h p))
    (ha : Γ ⊢[PRAAx] lt a (I.bd i p)) (hb : Γ ⊢[PRAAx] lt b (I.bd (succ i) p)) :
    Γ ⊢[PRAAx] edgeComparison I T i a b p := by
  have level : Γ ⊢[PRAAx] lt i (I.h p) ⟶ .all
      (lt (var 0) (I.bd (Syn.shift i) (Syn.shift p)) ⟶ .all
        (lt (var 0) (I.bd (succ (Syn.shift (Syn.shift i))) (Syn.shift (Syn.shift p))) ⟶
          edgeComparison I T (Syn.shift (Syn.shift i)) (var 1) (var 0) (Syn.shift (Syn.shift p)))) := by
    simpa [edgeEvidence] using h.allE i
  have first : Γ ⊢[PRAAx] lt a (I.bd i p) ⟶ .all
      (lt (var 0) (I.bd (succ (Syn.shift i)) (Syn.shift p)) ⟶
        edgeComparison I T (Syn.shift i) (Syn.shift a) (var 0) (Syn.shift p)) := by
    simpa using (Prf.impE level hi).allE a
  have second : Γ ⊢[PRAAx] lt b (I.bd (succ i) p) ⟶ edgeComparison I T i a b p := by
    simpa using (Prf.impE first ha).allE b
  exact .impE second hb

/-- The SAME arbitrary numerical code passes all weaker checks. -/
theorem refine_code (I : Instance) (G : PTm 3) (T : PTm 4) (S p : PTm n)
    (hEvidence : Γ ⊢[PRAAx] evidence I G T p)
    (hCode : Γ ⊢[PRAAx] admissibleCode (strong I G T) S p) : Γ ⊢[PRAAx] admissibleCode I S p := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] evidence I G T (Syn.shift p) := by
    simpa only [Fm.shift,subst_evidence,Syn.shift] using hEvidence.shift
  have hc : Γ.map Fm.shift ⊢[PRAAx] admissibleCode (strong I G T) (Syn.shift S) (Syn.shift p) := by
    simpa only [Fm.shift,CodedViableChain.subst_admissibleCode,Syn.shift] using hCode.shift
  refine .andI (Prf.andE₁ hCode) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    have node := CodedViableChain.local_at (Γ := le (var 0) (I.h (Syn.shift p)) :: Γ.map Fm.shift)
      (strong I G T) (Syn.shift S) (Syn.shift p) (var 0) hc.wk Prf.hyp0
    exact .andI (Prf.andE₁ node) (nonzero_of_sg_le
      (local_evidence_at I G _ _ _ (Prf.andE₁ hs).wk Prf.hyp0 (Prf.andE₁ node)) (Prf.andE₂ node))
  · refine .allI (.impI ?_)
    have current := CodedViableChain.local_at (Γ := lt (var 0) (I.h (Syn.shift p)) :: Γ.map Fm.shift)
      (strong I G T) (Syn.shift S) (Syn.shift p) (var 0) hc.wk (le_of_lt Prf.hyp0)
    have next := CodedViableChain.local_at (Γ := lt (var 0) (I.h (Syn.shift p)) :: Γ.map Fm.shift)
      (strong I G T) (Syn.shift S) (Syn.shift p) (succ (var 0)) hc.wk Prf.hyp0
    exact nonzero_of_sg_le
      (edge_evidence_at I T _ _ _ _ (Prf.andE₂ hs).wk Prf.hyp0 (Prf.andE₁ current) (Prf.andE₁ next))
      (CodedViableChain.edge_at (strong I G T) _ _ _ hc.wk Prf.hyp0)

theorem codeBound_same (I : Instance) (G : PTm 3) (T : PTm 4) (p : PTm n) :
    codeBound (strong I G T) p = codeBound I p := rfl

theorem produced_refinement (I : Instance) (G : PTm 3) (T : PTm 4) (s : PTm 1) (p : PTm n)
    (hEvidence : Γ ⊢[PRAAx] evidence I G T p)
    (hStart : Γ ⊢[PRAAx] viableStart (strong I G T) (start s p) p) : Γ ⊢[PRAAx]
    admissibleCode I (CodedViableChain.chainCode (strong I G T) s p) p :=
  refine_code I G T _ p hEvidence (CodedViableChain.produced_admissible _ _ _ hStart)

theorem returned_refinement (I : Instance) (G : PTm 3) (T : PTm 4) (p : PTm n)
    (hEvidence : Γ ⊢[PRAAx] evidence I G T p)
    (hFlag : Γ ⊢[PRAAx] ViableChainSelection.flag (strong I G T) p ≐ one) : Γ ⊢[PRAAx]
    admissibleCode I (sndT (ap1 (ViableChainSelection.outputF (strong I G T)) p)) p :=
  refine_code I G T _ p hEvidence (ViableChainSelection.returned_admissible _ _ hFlag)

theorem existence_refinement (I : Instance) (G : PTm 3) (T : PTm 4) (p : PTm n)
    (hEvidence : Γ ⊢[PRAAx] evidence I G T p)
    (hExists : Γ ⊢[PRAAx] ViableChainSelection.hasChain (strong I G T) p) :
    Γ ⊢[PRAAx] ViableChainSelection.hasChain I p := by
  refine .exE hExists ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] evidence I G T (Syn.shift p) := by
    simpa only [Fm.shift,subst_evidence,Syn.shift] using hEvidence.shift
  let Δ := (lt (var 0) (codeBound (strong I G T) (Syn.shift p)) ⋏
    admissibleCode (strong I G T) (var 0) (Syn.shift p)) :: Γ.map Fm.shift
  have output : Δ ⊢[PRAAx] ViableChainSelection.hasChain I (Syn.shift p) := by
    apply Prf.exI (t := var 0)
    simpa [ViableChainSelection.hasChain,codeBound_same] using .andI (Prf.andE₁ (Prf.hyp0 (Γ := Γ.map Fm.shift)))
      (refine_code I G T (var 0) (Syn.shift p) hs.wk (Prf.andE₂ (Prf.hyp0 (Γ := Γ.map Fm.shift))))
  simpa only [Δ,Fm.shift,ViableChainSelection.subst_hasChain,Syn.shift] using output

theorem success_refinement (I : Instance) (G : PTm 3) (T : PTm 4) (p : PTm n)
    (hEvidence : Γ ⊢[PRAAx] evidence I G T p)
    (hFlag : Γ ⊢[PRAAx] ViableChainSelection.flag (strong I G T) p ≐ one) :
    Γ ⊢[PRAAx] ViableChainSelection.flag I p ≐ one :=
  ViableChainSelection.chain_implies_success I _ p (returned_refinement I G T p hEvidence hFlag)

theorem bounded_evidence_refinement_closed (I : Instance) (G : PTm 3) (T : PTm 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (evidence I G T (var 0) ⟶ admissibleCode (strong I G T) (var 1) (var 0) ⟶ admissibleCode I (var 1) (var 0)) :=
  closeUniv 2 (.impI (.impI (refine_code I G T _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_produced_chain_refinement_closed (I : Instance) (G : PTm 3) (T : PTm 4) (s : PTm 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (evidence I G T (var 0) ⟶ viableStart (strong I G T) (start s (var 0)) (var 0) ⟶
        admissibleCode I (CodedViableChain.chainCode (strong I G T) s (var 0)) (var 0)) :=
  closeUniv 1 (.impI (.impI (produced_refinement I G T s _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_chain_refinement_closed (I : Instance) (G : PTm 3) (T : PTm 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (evidence I G T (var 0) ⟶ ViableChainSelection.flag (strong I G T) (var 0) ≐ one ⟶
        admissibleCode I (sndT (ap1 (ViableChainSelection.outputF (strong I G T)) (var 0))) (var 0)) :=
  closeUniv 1 (.impI (.impI (returned_refinement I G T _ Prf.hyp1 Prf.hyp0)))
theorem bounded_chain_existence_refinement_closed (I : Instance) (G : PTm 3) (T : PTm 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (evidence I G T (var 0) ⟶ ViableChainSelection.hasChain (strong I G T) (var 0) ⟶
        ViableChainSelection.hasChain I (var 0)) :=
  closeUniv 1 (.impI (.impI (existence_refinement I G T _ Prf.hyp1 Prf.hyp0)))
theorem initial_success_refinement_closed (I : Instance) (G : PTm 3) (T : PTm 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (evidence I G T (var 0) ⟶ ViableChainSelection.flag (strong I G T) (var 0) ≐ one ⟶
        ViableChainSelection.flag I (var 0) ≐ one) :=
  closeUniv 1 (.impI (.impI (success_refinement I G T _ Prf.hyp1 Prf.hyp0)))

/-! ## A genuine internal bounded collection of requirements

The fixed term r(p) supplies the NUMERICAL requirement count. The families
G(j,i,a,p) and T(j,i,a,b,p) are fixed finite syntax, not an interpreter for
arbitrary programs. Their normalized products are actual allB recursors.
-/

def localRequirement (G : PTm 4) (j i a p : PTm n) : PTm n := Syn.subst ![j,i,a,p] G
def edgeRequirement (T : PTm 5) (j i a b p : PTm n) : PTm n := Syn.subst ![j,i,a,b,p] T
def localRequirementBody (G : PTm 4) : PTm 2 :=
  localRequirement G (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def edgeRequirementBody (T : PTm 5) : PTm 2 :=
  edgeRequirement T (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
def localFold (G : PTm 4) (r : PTm 1) (i a p : PTm n) : PTm n :=
  BoundedReflection.allB (localRequirementBody G) (inst1 r p) (pairT i (pairT a p))
def edgeFold (T : PTm 5) (r : PTm 1) (i a b p : PTm n) : PTm n :=
  BoundedReflection.allB (edgeRequirementBody T) (inst1 r p) (pairT i (pairT a (pairT b p)))
def conjoined (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) : Instance :=
  strong I (localFold G r (var 0) (var 1) (var 2)) (edgeFold T r (var 0) (var 1) (var 2) (var 3))

@[simp] theorem subst_localRequirement {m : ℕ} (σ : Fin n → PTm m) (G : PTm 4) (j i a p : PTm n) :
    Syn.subst σ (localRequirement G j i a p) = localRequirement G (Syn.subst σ j)
      (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by
  simp only [localRequirement,Syn.subst_subst]
  congr 1
  funext k
  fin_cases k <;> rfl
@[simp] theorem subst_edgeRequirement {m : ℕ} (σ : Fin n → PTm m) (T : PTm 5) (j i a b p : PTm n) :
    Syn.subst σ (edgeRequirement T j i a b p) = edgeRequirement T (Syn.subst σ j)
      (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) := by
  simp only [edgeRequirement,Syn.subst_subst]
  congr 1
  funext k
  fin_cases k <;> rfl
@[simp] theorem subst_localFold {m : ℕ} (σ : Fin n → PTm m) (G : PTm 4) (r : PTm 1) (i a p : PTm n) :
    Syn.subst σ (localFold G r i a p) = localFold G r (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by
  simp [localFold]
ipra_subst edgeFold

theorem local_requirement_congr (G : PTm 4) {j j' i i' a a' p p' : PTm n}
    (hj : Γ ⊢[PRAAx] j ≐ j') (hi : Γ ⊢[PRAAx] i ≐ i')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx]
    localRequirement G j i a p ≐ localRequirement G j' i' a' p' :=
  Prf.eqCongr G (fun k => by fin_cases k; exact hj; exact hi; exact ha; exact hp)
theorem edge_requirement_congr (T : PTm 5) {j j' i i' a a' b b' p p' : PTm n}
    (hj : Γ ⊢[PRAAx] j ≐ j') (hi : Γ ⊢[PRAAx] i ≐ i')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx]
    edgeRequirement T j i a b p ≐ edgeRequirement T j' i' a' b' p' :=
  Prf.eqCongr T (fun k => by fin_cases k; exact hj; exact hi; exact ha; exact hb; exact hp)

theorem local_requirement_at (G : PTm 4) (j i a p : PTm n) : Γ ⊢[PRAAx]
    inst2 (localRequirementBody G) j (pairT i (pairT a p)) ≐ localRequirement G j i a p := by
  have tail := snd_pair (Γ := Γ) i (pairT a p)
  simpa only [localRequirementBody,inst2,subst_localRequirement,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    local_requirement_congr G (.eqRefl j) (fst_pair i (pairT a p))
      ((congrFst tail).eqTrans (fst_pair a p)) ((congrSnd tail).eqTrans (snd_pair a p))
theorem edge_requirement_at (T : PTm 5) (j i a b p : PTm n) : Γ ⊢[PRAAx]
    inst2 (edgeRequirementBody T) j (pairT i (pairT a (pairT b p))) ≐ edgeRequirement T j i a b p := by
  have tail := snd_pair (Γ := Γ) i (pairT a (pairT b p))
  have last := (congrSnd tail).eqTrans (snd_pair a (pairT b p))
  simpa only [edgeRequirementBody,inst2,subst_edgeRequirement,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    edge_requirement_congr T (.eqRefl j) (fst_pair i (pairT a (pairT b p)))
      ((congrFst tail).eqTrans (fst_pair a (pairT b p)))
      ((congrFst last).eqTrans (fst_pair b p)) ((congrSnd last).eqTrans (snd_pair b p))

theorem conjoined_g (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) (i a p : PTm n) :
    (conjoined I G T r).g i a p = localFold G r i a p := by simp [conjoined,strong,Instance.g]
theorem conjoined_t (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) (i a b p : PTm n) :
    (conjoined I G T r).t i a b p = edgeFold T r i a b p := by simp [conjoined,strong,Instance.t]

theorem local_fold_bit (G : PTm 4) (r : PTm 1) (i a p : PTm n) : Γ ⊢[PRAAx]
    (localFold G r i a p ≐ zero) ⋎ (localFold G r i a p ≐ one) := BoundedReflection.all_cases _ _ _
theorem edge_fold_bit (T : PTm 5) (r : PTm 1) (i a b p : PTm n) : Γ ⊢[PRAAx]
    (edgeFold T r i a b p ≐ zero) ⋎ (edgeFold T r i a b p ≐ one) := BoundedReflection.all_cases _ _ _

theorem local_fold_at (G : PTm 4) (r : PTm 1) (p i a j : PTm n)
    (h : Γ ⊢[PRAAx] neg (localFold G r i a p ≐ zero)) (hj : Γ ⊢[PRAAx] lt j (inst1 r p)) :
    Γ ⊢[PRAAx] neg (localRequirement G j i a p ≐ zero) :=
  CodedViableChain.nonzero_of_eq (local_requirement_at G j i a p).eqSymm
    (BoundedReflection.all_elim _ (FiniteGluing.one_of_ne (local_fold_bit G r i a p) h) hj)
theorem edge_fold_at (T : PTm 5) (r : PTm 1) (p i a b j : PTm n)
    (h : Γ ⊢[PRAAx] neg (edgeFold T r i a b p ≐ zero)) (hj : Γ ⊢[PRAAx] lt j (inst1 r p)) :
    Γ ⊢[PRAAx] neg (edgeRequirement T j i a b p ≐ zero) :=
  CodedViableChain.nonzero_of_eq (edge_requirement_at T j i a b p).eqSymm
    (BoundedReflection.all_elim _ (FiniteGluing.one_of_ne (edge_fold_bit T r i a b p) h) hj)

theorem local_fold_empty (G : PTm 4) (r : PTm 1) (i a p : PTm n) (hr : Γ ⊢[PRAAx] inst1 r p ≐ zero) :
    Γ ⊢[PRAAx] localFold G r i a p ≐ one :=
  (congrAp2 (prodF (BoundedReflection.sgB (localRequirementBody G))) hr (.eqRefl _)).eqTrans
    (BoundedReflection.allB_zero _ _)
theorem edge_fold_empty (T : PTm 5) (r : PTm 1) (i a b p : PTm n) (hr : Γ ⊢[PRAAx] inst1 r p ≐ zero) :
    Γ ⊢[PRAAx] edgeFold T r i a b p ≐ one :=
  (congrAp2 (prodF (BoundedReflection.sgB (edgeRequirementBody T))) hr (.eqRefl _)).eqTrans
    (BoundedReflection.allB_zero _ _)

theorem conjoined_code_local (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) (S p i j : PTm n)
    (h : Γ ⊢[PRAAx] admissibleCode (conjoined I G T r) S p)
    (hi : Γ ⊢[PRAAx] le i (I.h p)) (hj : Γ ⊢[PRAAx] lt j (inst1 r p)) : Γ ⊢[PRAAx]
    lt (entry S i) (I.bd i p) ⋏ neg (localRequirement G j i (entry S i) p ≐ zero) := by
  have node := CodedViableChain.local_at (conjoined I G T r) S p i h hi
  have passes : Γ ⊢[PRAAx] neg (localFold G r i (entry S i) p ≐ zero) := by
    simpa only [conjoined_g] using Prf.andE₂ node
  exact .andI (Prf.andE₁ node) (local_fold_at G r p i _ j passes hj)
theorem conjoined_code_edge (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) (S p i j : PTm n)
    (h : Γ ⊢[PRAAx] admissibleCode (conjoined I G T r) S p)
    (hi : Γ ⊢[PRAAx] lt i (I.h p)) (hj : Γ ⊢[PRAAx] lt j (inst1 r p)) : Γ ⊢[PRAAx]
    neg (edgeRequirement T j i (entry S i) (entry S (succ i)) p ≐ zero) := by
  have passes : Γ ⊢[PRAAx] neg (edgeFold T r i (entry S i) (entry S (succ i)) p ≐ zero) := by
    simpa only [conjoined_t] using CodedViableChain.edge_at (conjoined I G T r) S p i h hi
  exact edge_fold_at T r p i _ _ j passes hj

def localFoldF (G : PTm 4) (r : PTm 1) : PR 3 := PTm.toPR (localFold G r (var 0) (var 1) (var 2))
def edgeFoldF (T : PTm 5) (r : PTm 1) : PR 4 := PTm.toPR (edgeFold T r (var 0) (var 1) (var 2) (var 3))
theorem local_fold_program_at (G : PTm 4) (r : PTm 1) (i a p : PTm n) : Γ ⊢[PRAAx]
    ap3 (localFoldF G r) i a p ≐ localFold G r i a p := by
  simpa [localFoldF,ap3] using toPR_eq (Γ := Γ) (localFold G r (var 0) (var 1) (var 2)) ![i,a,p]
theorem edge_fold_program_at (T : PTm 5) (r : PTm 1) (i a b p : PTm n) : Γ ⊢[PRAAx]
    PTm.app (edgeFoldF T r) ![i,a,b,p] ≐ edgeFold T r i a b p := by
  simpa [edgeFoldF] using toPR_eq (Γ := Γ) (edgeFold T r (var 0) (var 1) (var 2) (var 3)) ![i,a,b,p]

theorem internal_requirement_local_closed (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (admissibleCode (conjoined I G T r) (var 1) (var 0) ⟶ le (var 2) (I.h (var 0)) ⟶
        lt (var 3) (inst1 r (var 0)) ⟶
          (lt (entry (var 1) (var 2)) (I.bd (var 2) (var 0)) ⋏
            neg (localRequirement G (var 3) (var 2) (entry (var 1) (var 2)) (var 0) ≐ zero))) :=
  closeUniv 4 (.impI (.impI (.impI (conjoined_code_local I G T r _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem internal_requirement_edge_closed (I : Instance) (G : PTm 4) (T : PTm 5) (r : PTm 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (admissibleCode (conjoined I G T r) (var 1) (var 0) ⟶ lt (var 2) (I.h (var 0)) ⟶
        lt (var 3) (inst1 r (var 0)) ⟶
          neg (edgeRequirement T (var 3) (var 2) (entry (var 1) (var 2)) (entry (var 1) (succ (var 2))) (var 0) ≐ zero)) :=
  closeUniv 4 (.impI (.impI (.impI (conjoined_code_edge I G T r _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem finite_conjunction_programs_closed (G : PTm 4) (T : PTm 5) (r : PTm 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (ap3 (localFoldF G r) (var 1) (var 2) (var 0) ≐ localFold G r (var 1) (var 2) (var 0) ⋏
        PTm.app (edgeFoldF T r) ![var 1,var 2,var 3,var 0] ≐ edgeFold T r (var 1) (var 2) (var 3) (var 0)) :=
  closeUniv 4 (.andI (local_fold_program_at G r _ _ _) (edge_fold_program_at T r _ _ _ _))

end LeanProofs.IPRA.Foundations.CodedChainRefinement
