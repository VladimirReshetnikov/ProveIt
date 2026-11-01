import DiophantineConsistency.PRAParameterPackingN
/-! Finite iteration of bounded pair packing in every candidate-PRA model. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAParameterPackingIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAParameterPackingN
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
theorem modelPacking_parameters (n : ℕ) (ψ : Semisentence language (4+n)) (a b : M) :
    ∃ t : M, ∀ x y : M, ∀ tail : Fin n → M,
      (packed n ψ).Eval (Fin.append ![x,y,t] tail) Empty.elim ↔
        ψ.Eval (Fin.append ![x,y,a,b] tail) Empty.elim := by
  obtain ⟨t,ht⟩ := modelPacking n ψ a b
  refine ⟨t,fun x y tail => ?_⟩
  let v : Fin (3+n) → M := Fin.append ![x,y,t] tail
  have i0 : (0 : Fin (3+n)) = Fin.castAdd n (0 : Fin 3) := by
    apply Fin.ext
    change 0 % (3+n) = 0
    exact Nat.zero_mod _
  have i1 : (1 : Fin (3+n)) = Fin.castAdd n (1 : Fin 3) := by
    apply Fin.ext
    change 1 % (3+n) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have i2 : (2 : Fin (3+n)) = Fin.castAdd n (2 : Fin 3) := by
    apply Fin.ext
    change 2 % (3+n) = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hv0 : v 0 = x := by simp [v,i0,Fin.append_left]
  have hv1 : v 1 = y := by simp [v,i1,Fin.append_left]
  have hv2 : v 2 = t := by simp [v,i2,Fin.append_left]
  have htail : (fun i => v (Fin.natAdd 3 i)) = tail := by
    funext i
    exact Fin.append_right _ _ i
  have h := ht v hv2
  simpa only [hv0,hv1,htail] using h
end models

def parameterVal {M : Type} (n : ℕ) (x y : M) (p : Fin (n+1) → M) : Fin (3+n) → M :=
  Fin.append ![x,y,p 0] (fun i => p (Fin.succ i))

private theorem eval_cast {M : Type} [Structure language M] {k l : ℕ} (e : k = l)
    (ψ : Semisentence language k) (v : Fin l → M) :
    (cast (congrArg (Semisentence language) e) ψ).Eval v Empty.elim ↔
      ψ.Eval (v ∘ Fin.cast e) Empty.elim := by
  cases e
  rfl

theorem align_eval {M : Type} [Structure language M] (n : ℕ)
    (ψ : Semisentence language (3+(n+1))) (v : Fin (4+n) → M) :
    (align n ψ).Eval v Empty.elim ↔ ψ.Eval (v ∘ Fin.cast (by omega)) Empty.elim := by
  unfold align
  exact eval_cast _ ψ v
theorem parameterVal_step {M : Type} (n : ℕ) (x y : M) (p : Fin (n+2) → M) :
    (Fin.append ![x,y,p 0,p 1] (fun i : Fin n => p (Fin.succ (Fin.succ i))) ∘ Fin.cast (by omega)) =
      parameterVal (n+1) x y p := by
  have left_index (i : Fin 3) :
      (Fin.cast (by omega) (Fin.castAdd (n+1) i) : Fin (4+n)) =
        Fin.castAdd n (Fin.castAdd 1 i) := by
    apply Fin.ext
    rfl
  have first_index : (Fin.cast (by omega) (Fin.natAdd 3 (0 : Fin (n+1))) : Fin (4+n)) =
      Fin.castAdd n (3 : Fin 4) := by
    apply Fin.ext
    rfl
  have tail_index (i : Fin n) :
      (Fin.cast (by omega) (Fin.natAdd 3 (Fin.succ i)) : Fin (4+n)) = Fin.natAdd 4 i := by
    apply Fin.ext
    simp
    omega
  funext i
  induction i using Fin.addCases with
  | left i =>
    simp only [Function.comp_apply, left_index, Fin.append_left, parameterVal]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact Fin.cases rfl (fun l => Fin.elim0 l) k
  | right i =>
    simp only [Function.comp_apply, parameterVal, Fin.append_right]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [first_index, Fin.append_left]
      rfl
    · rw [tail_index, Fin.append_right]
section iteration
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelPackAll : ∀ (n : ℕ) (ψ : Semisentence language (3+n)) (p : Fin (n+1) → M),
    ∃ t : M, ∀ x y : M, (packAll n ψ).Eval ![x,y,t] Empty.elim ↔
      ψ.Eval (parameterVal n x y p) Empty.elim := by
  intro n
  induction n with
  | zero =>
    intro ψ p
    refine ⟨p 0, fun x y => ?_⟩
    have h : parameterVal 0 x y p = ![x,y,p 0] := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · exact Fin.cases rfl (fun l => Fin.elim0 l) k
    rw [h]
    rfl
  | succ n ih =>
    intro ψ p
    let tail : Fin n → M := fun i => p (Fin.succ (Fin.succ i))
    obtain ⟨u,hu⟩ := modelPacking_parameters n (align n ψ) (p 0) (p 1)
    let p' : Fin (n+1) → M := u :> tail
    obtain ⟨t,ht⟩ := ih (packed n (align n ψ)) p'
    refine ⟨t, fun x y => ?_⟩
    have hp0 : p' 0 = u := by
      have h : (0 : Fin (n+1)) = (⟨0, by omega⟩ : Fin (n+1)) := by
        apply Fin.ext
        change 0 % (n+1) = 0
        exact Nat.zero_mod _
      rw [h]
      rfl
    have hpTail : (fun i => p' (Fin.succ i)) = tail := by
      funext i
      rfl
    have hv : parameterVal n x y p' = Fin.append ![x,y,u] tail := by
      simp only [parameterVal,hp0,hpTail]
    have ht' := ht x y
    rw [hv] at ht'
    have hu' := hu x y tail
    have he := align_eval n ψ (Fin.append ![x,y,p 0,p 1] tail)
    rw [show (Fin.append ![x,y,p 0,p 1] tail ∘ Fin.cast (by omega)) =
      parameterVal (n+1) x y p by exact parameterVal_step n x y p] at he
    exact ht'.trans (hu'.trans he)
end iteration
end DiophantineConsistency.PRAParameterPackingIteration
