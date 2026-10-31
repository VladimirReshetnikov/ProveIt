import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRASeqSWitnessBound
import DiophantineConsistency.PRAPpow2WitnessBound
/-! A polynomial model-uniform witness bound for Foundation exponentialDef.
    The swapped expDef, bit membership, fixpoint and refutation bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExponentialWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem seqS_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) (w : V)
    (hw : (ω #1).val e Empty.elim + (ω #2).val e Empty.elim + 2*(ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ Exponential.Seqₛ.def.val).Evalb e →
      (bnd (ω ▹ Exponential.Seqₛ.def.val)).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  intro h
  let g : Fin 3 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0,g 1,g 2] = g := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hs : Fin.snoc g (g 1+g 2+2*g 0+1) = ![g 0,g 1,g 2,g 1+g 2+2*g 0+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hw' : g 1+g 2+2*g 0+1 ≤ w := hw
  have hb := PRASeqSWitnessBound.seqS_bound (g 0) (g 1) (g 2) (by simpa [hv] using h)
  have hb' : (bnd Exponential.Seqₛ.def.val).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono Exponential.Seqₛ.def.val g (Empty.elim : Empty → V) hw'
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural Exponential.Seqₛ.def.val ω e w).mpr hb'

theorem ppow2_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) (w : V)
    (hw : 2 * (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ ppow2Def.val).Evalb e →
      (bnd (ω ▹ ppow2Def.val)).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  intro h
  let g : Fin 1 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0] = g := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hs : Fin.snoc g (2 * g 0+1) = ![g 0,2 * g 0+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hw' : 2 * g 0+1 ≤ w := hw
  have hb := PRAPpow2WitnessBound.ppow2_bound (g 0) (by simpa [hv] using h)
  have hb' : (bnd ppow2Def.val).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono ppow2Def.val g (Empty.elim : Empty → V) hw'
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural ppow2Def.val ω e w).mpr hb'

attribute [local irreducible] extDef ppow2Def Exponential.Seqₛ.def

theorem exponential_bound_of_common (x y w : V)
    (h4 : y^4+1 ≤ w) (h2 : y^2+1 ≤ w)
    (hp : 2*(y^2)+1 ≤ w) (hs : y^4+y^4+2*y+1 ≤ w) :
    exponentialDef.val.Evalb ![x,y] →
      (bnd exponentialDef.val).Evalb ![x,y,w] := by
  intro h
  simp [exponentialDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open] at h ⊢
  rcases h with hzero | ⟨A,hA,B,hB,⟨he1,he2⟩,hseq,u,hu,hne,hpow,he3,he4⟩
  · exact Or.inl hzero
  · right
    have hA0 : A ≤ y^4 := lt_succ_iff_le.mp hA
    have hB0 : B ≤ y^4 := lt_succ_iff_le.mp hB
    have hu0 : u ≤ y^2 := lt_succ_iff_le.mp hu
    have hAw : A+1 ≤ w := le_trans (by simpa [add_comm] using add_le_add_right hA0 1) h4
    have hBw : B+1 ≤ w := le_trans (by simpa [add_comm] using add_le_add_right hB0 1) h4
    have hseq0 : A+B ≤ y^4+y^4 := add_le_add hA0 hB0
    have hseqw : A+B+2*y+1 ≤ w := le_trans (by
      have hq : A+B+2*y ≤ y^4+y^4+2*y := by simpa [add_comm] using add_le_add_right hseq0 (2*y)
      simpa [add_comm] using add_le_add_right hq 1) hs
    have hp0 : 2*u ≤ 2*(y^2) := mul_le_mul_left hu0
    have hpw : 2*u+1 ≤ w := le_trans (by simpa [add_comm] using add_le_add_right hp0 1) hp
    refine ⟨A,lt_of_lt_of_le hA h4,hA,B,lt_of_lt_of_le hB h4,hB,?_,?_,u,lt_of_lt_of_le hu h2,hu,hne,?_,?_,?_⟩
    · constructor
      · let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![Semiterm.numeral 1,Semiterm.numeral 4,#1]
        have hf : (ω ▹ extDef.val).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he1
        have hw : (ω #2).val ![B,A,x,y] Empty.elim + 1 ≤ w := hAw
        have hb := PRASeqSWitnessBound.ext_rew_bound_at ω ![B,A,x,y] w hw hf
        have hh : Fin.snoc ![B,A,x,y] w = ![B,A,x,y,w] := by simp
        rw [hh] at hb
        exact hb
      · let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![Semiterm.numeral 2,Semiterm.numeral 4,#0]
        have hf : (ω ▹ extDef.val).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he2
        have hw : (ω #2).val ![B,A,x,y] Empty.elim + 1 ≤ w := hBw
        have hb := PRASeqSWitnessBound.ext_rew_bound_at ω ![B,A,x,y] w hw hf
        have hh : Fin.snoc ![B,A,x,y] w = ![B,A,x,y,w] := by simp
        rw [hh] at hb
        exact hb
    · let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#3,#1,#0]
      have hf : (ω ▹ Exponential.Seqₛ.def.val).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using hseq
      have hw : (ω #1).val ![B,A,x,y] Empty.elim + (ω #2).val ![B,A,x,y] Empty.elim + 2*(ω #0).val ![B,A,x,y] Empty.elim + 1 ≤ w := hseqw
      have hb := seqS_rew_bound_at ω ![B,A,x,y] w hw hf
      have hh : Fin.snoc ![B,A,x,y] w = ![B,A,x,y,w] := by simp
      rw [hh] at hb
      exact hb
    · let ω : Rew ℒₒᵣ Empty 1 Empty 5 := Rew.subst ![#0]
      have hf : (ω ▹ ppow2Def.val).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using hpow
      have hw : 2*(ω #0).val ![u,B,A,x,y] Empty.elim+1 ≤ w := hpw
      have hb := ppow2_rew_bound_at ω ![u,B,A,x,y] w hw hf
      have hh : Fin.snoc ![u,B,A,x,y] w = ![u,B,A,x,y,w] := by simp
      rw [hh] at hb
      exact hb
    · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#3,#0,#2]
      have hf : (ω ▹ extDef.val).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he3
      have hw : (ω #2).val ![u,B,A,x,y] Empty.elim+1 ≤ w := hAw
      have hb := PRASeqSWitnessBound.ext_rew_bound_at ω ![u,B,A,x,y] w hw hf
      have hh : Fin.snoc ![u,B,A,x,y] w = ![u,B,A,x,y,w] := by simp
      rw [hh] at hb
      exact hb
    · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#4,#0,#1]
      have hf : (ω ▹ extDef.val).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he4
      have hw : (ω #2).val ![u,B,A,x,y] Empty.elim+1 ≤ w := hBw
      have hb := PRASeqSWitnessBound.ext_rew_bound_at ω ![u,B,A,x,y] w hw hf
      have hh : Fin.snoc ![u,B,A,x,y] w = ![u,B,A,x,y,w] := by simp
      rw [hh] at hb
      exact hb
def exponentialMajorant (y : V) : V :=
  (y^4+1)+(y^2+1)+(2*(y^2)+1)+(y^4+y^4+2*y+1)

theorem exponential_bound (x y : V) : exponentialDef.val.Evalb ![x,y] →
    (bnd exponentialDef.val).Evalb ![x,y,exponentialMajorant y] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := y^4+1
  let B := y^2+1
  let C := 2*(y^2)+1
  let D := y^4+y^4+2*y+1
  have hA : A ≤ A+B+C+D := le_trans (le_trans le_self_add le_self_add) le_self_add
  have hB : B ≤ A+B+C+D := le_trans (le_trans le_add_self le_self_add) le_self_add
  have hC : C ≤ A+B+C+D := le_trans le_add_self le_self_add
  have hD : D ≤ A+B+C+D := le_add_self
  exact exponential_bound_of_common x y (exponentialMajorant y) hA hB hC hD
def actualExponential : ArithmeticSemisentence 2 := exponentialDef.val

def boundedExponential : ArithmeticSemisentence 3 := bnd actualExponential

def exponentialBoundBody : ArithmeticSemisentence 2 :=
  “x y. !actualExponential x y → !boundedExponential x y ((y⁴+1)+(y²+1)+(2*y²+1)+(y⁴+y⁴+2*y+1))”

theorem exponentialBoundBody_model (e : Fin 2 → V) : exponentialBoundBody.Eval e Empty.elim := by
  simp [exponentialBoundBody, boundedExponential, Semiformula.eval_substs]
  exact exponential_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def exponentialBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding exponentialBoundBody

theorem candidate_proves_exponential_bound : PRA ⊢ exponentialBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact exponentialBoundBody_model e
end DiophantineConsistency.PRAExponentialWitnessBound
