import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRALenbitWitnessBound
import DiophantineConsistency.PRABndRewriting
/-! Bind the concrete `lenbitDef` majorant into Foundation's actual
`bitDef` membership graph. A bounded inlined `expDef` witness remains an
explicit premise; no full refutation bound certificate is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABitWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction PRALenbitWitnessBound PRABndRewriting
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
/-- The actual argument substitution of `lenbitDef` inside `bitDef`
retains the y+1 majorant. -/
theorem lenbit_in_bit_bound (x i y : V) :
    (Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ lenbitDef.val).Evalb ![x,i,y] →
    (bnd (Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ lenbitDef.val)).Evalb ![x,i,y,y+1] := by
  intro h
  have hn := PRABndRewriting.natural lenbitDef.val
    (Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3)) ![x,i,y] (y+1)
  have hv : (fun j => ((Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3)) #j).val ![x,i,y] Empty.elim) = ![x,y] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![x,i,y] (y+1) = ![x,i,y,y+1] := by simp
  have hs' : Fin.snoc ![x,y] (y+1) = ![x,y,y+1] := by simp
  rw [hv,hs,hs'] at hn
  have h0 : lenbitDef.val.Evalb ![x,y] := by
    simp only [Semiformula.eval_rew] at h
    have hb : (Semiterm.val ![x,i,y] Empty.elim ∘
        (Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3)) ∘ Semiterm.bvar) = ![x,y] := hv
    have hf : (Semiterm.val ![x,i,y] Empty.elim ∘
        (Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3)) ∘ Semiterm.fvar) =
        (Empty.elim : Empty → V) := Subsingleton.elim _ _
    rw [hb,hf] at h
    exact h
  exact hn.mpr (lenbit_bound x y h0)
def expInsideBit : ArithmeticSemisentence 3 :=
  Rew.subst (![#0,#1] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ expDef.val

def lenbitInsideBit : ArithmeticSemisentence 3 :=
  Rew.subst (![#0,#2] : Fin 2 → ArithmeticSemiterm Empty 3) ▹ lenbitDef.val

/-- A known membership witness, its lenbit graph and separately bounded
exponential graph suffice for the bounded actual bit graph. -/
theorem bit_bnd_of_witness (x y w z : V) (hw : y+1 ≤ w) (hz : z ≤ y)
    (hexp : (bnd expInsideBit).Evalb ![z,x,y,w])
    (hlen : lenbitInsideBit.Evalb ![z,x,y]) :
    (bnd bitDef.val).Evalb ![x,y,w] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hb := lenbit_in_bit_bound z x y hlen
  have hbm := eval_bnd_mono lenbitInsideBit ![z,x,y] (Empty.elim : Empty → V) hw (by simpa [lenbitInsideBit] using hb)
  simp [bitDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open]
  exact ⟨z, lt_of_lt_of_le (lt_succ_iff_le.mpr hz) hw,
    lt_succ_iff_le.mpr hz, hexp, by simpa [lenbitInsideBit] using hbm⟩
def bitBoundBody : ArithmeticSemisentence 4 :=
  ((“x y w z. y+1 ≤ w ∧ z ≤ y”) ⋏
    (Rew.subst (![#3,#0,#1,#2] : Fin 4 → ArithmeticSemiterm Empty 4) ▹ bnd expInsideBit) ⋏
    (Rew.subst (![#3,#0,#1] : Fin 3 → ArithmeticSemiterm Empty 4) ▹ lenbitInsideBit)) 🡒
      (Rew.subst (![#0,#1,#2] : Fin 3 → ArithmeticSemiterm Empty 4) ▹ bnd bitDef.val)

theorem bitBoundBody_model (e : Fin 4 → V) : bitBoundBody.Eval e Empty.elim := by
  simp only [bitBoundBody, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and]
  intro ⟨⟨hw,hz⟩,hexp,hlen⟩
  have hw' : e 1+1 ≤ e 2 := by simpa using hw
  have hz' : e 3 ≤ e 1 := by simpa using hz
  simp only [Semiformula.eval_rew] at hexp hlen ⊢
  have he : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#3,#0,#1,#2] : Fin 4 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.bvar) =
      ![e 3,e 0,e 1,e 2] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hl : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#3,#0,#1] : Fin 3 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.bvar) =
      ![e 3,e 0,e 1] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have ht : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#0,#1,#2] : Fin 3 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.bvar) =
      ![e 0,e 1,e 2] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have he' : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#3,#0,#1,#2] : Fin 4 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hl' : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#3,#0,#1] : Fin 3 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have ht' : (Semiterm.val e Empty.elim ∘
      (Rew.subst (![#0,#1,#2] : Fin 3 → ArithmeticSemiterm Empty 4)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  rw [he,he'] at hexp
  rw [hl,hl'] at hlen
  rw [ht,ht']
  exact bit_bnd_of_witness (e 0) (e 1) (e 2) (e 3) hw' hz' hexp hlen
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def bitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding bitBoundBody

/-- Candidate PRA proves the universally closed conditional bit-graph
binding; the bounded exponential conjunct remains in its antecedent. -/
theorem candidate_proves_bitBoundSentence : PRA ⊢ bitBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bitBoundBody_model e
end DiophantineConsistency.PRABitWitnessBound
