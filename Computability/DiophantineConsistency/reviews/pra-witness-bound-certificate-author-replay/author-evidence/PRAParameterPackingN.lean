import DiophantineConsistency.PRABoundedPairGraph
import DiophantineConsistency.ParsonsHierarchyMap
set_option autoImplicit false
namespace DiophantineConsistency.PRAParameterPackingN
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

def graph : Semisentence language 3 := Semiformula.lMap embedding pairDef.val

def matrixSub (n : ℕ) : Fin (4+n) → Semiterm language Empty (3+n+1+1) :=
  Fin.append ![#2,#3,#1,#0] (fun i => .bvar (Fin.cast (by omega) (Fin.natAdd 5 i)))

def packed (n : ℕ) (ψ : Semisentence language (4+n)) : Semisentence language (3+n) :=
  ∃⁰[(Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 3, .func oneCode Fin.elim0]])]
  ∃⁰[(Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0, .func addCode ![.bvar 4, .func oneCode Fin.elim0]])]
    ((Rew.embSubsts ![#4,#1,#0] ▹ graph) ⋏
      (Rew.embSubsts (matrixSub n) ▹ ψ))

theorem packed_bounded (n : ℕ) (ψ : Semisentence language (4+n)) (hψ : Hierarchy 𝚺 0 ψ) :
    Hierarchy 𝚺 0 (packed n ψ) := by
  unfold packed
  apply Hierarchy.bexs
  · simp [Semiterm.Positive, Semiterm.bv_func]
    change 0 % (3+n+1) < 3 % (3+n+1)
    simp [Nat.mod_eq_of_lt (show 3 < 3+n+1 by omega)]
  · apply Hierarchy.bexs
    · simp [Semiterm.Positive, Semiterm.bv_func]
      change 0 % (3+n+1+1) < 4 % (3+n+1+1)
      simp [Nat.mod_eq_of_lt (show 4 < 3+n+1+1 by omega)]
    · apply Hierarchy.and
      · exact Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy pairDef.sigma_prop)
      · exact Hierarchy.rew _ hψ
theorem matrixSub_eval {M : Type} [Structure language M] (n : ℕ)
    (u : Fin (3+n+1+1) → M) :
    (Semiterm.val (L := language) u Empty.elim ∘ matrixSub n) =
      Fin.append ![u 2,u 3,u 1,u 0] (fun i => u (Fin.cast (by omega) (Fin.natAdd 5 i))) := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [matrixSub, Fin.append_left]
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [matrixSub, Fin.append_left]
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [matrixSub, Fin.append_left]
        · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
          simp [matrixSub, Fin.append_left]
  | right i => simp [matrixSub, Fin.append_right]
theorem cons_tail {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) (i : Fin n) :
    (b :> a :> v) (Fin.cast (by omega) (Fin.natAdd 5 i)) = v (Fin.natAdd 3 i) := by
  have h : (Fin.cast (by omega) (Fin.natAdd 5 i) : Fin (3+n+1+1)) =
      Fin.succ (Fin.succ (Fin.natAdd 3 i)) := by
    apply Fin.ext
    simp
    omega
  rw [h]
  rfl

theorem cons_two {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) :
    (b :> a :> v) (2 : Fin (3+n+1+1)) = v 0 := by
  have h : (2 : Fin (3+n+1+1)) = Fin.succ (Fin.succ (0 : Fin (3+n))) := by
    apply Fin.ext
    change 2 % (3+n+1+1) = 0 % (3+n) + 2
    simp [Nat.mod_eq_of_lt (show 2 < 3+n+1+1 by omega)]
  rw [h]
  rfl

theorem cons_three {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) :
    (b :> a :> v) (3 : Fin (3+n+1+1)) = v 1 := by
  have h : (3 : Fin (3+n+1+1)) = Fin.succ (Fin.succ (1 : Fin (3+n))) := by
    apply Fin.ext
    change 3 % (3+n+1+1) = 1 % (3+n) + 2
    simp [Nat.mod_eq_of_lt (show 3 < 3+n+1+1 by omega), Nat.mod_eq_of_lt (show 1 < 3+n by omega)]
  rw [h]
  rfl

theorem cons_four {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) :
    (b :> a :> v) (4 : Fin (3+n+1+1)) = v 2 := by
  have h : (4 : Fin (3+n+1+1)) = Fin.succ (Fin.succ (2 : Fin (3+n))) := by
    apply Fin.ext
    change 4 % (3+n+1+1) = 2 % (3+n) + 2
    simp [Nat.mod_eq_of_lt (show 4 < 3+n+1+1 by omega), Nat.mod_eq_of_lt (show 2 < 3+n by omega)]
  rw [h]
  rfl
theorem cons_one {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) :
    (b :> a :> v) (1 : Fin (3+n+1+1)) = a := by
  have h : (1 : Fin (3+n+1+1)) = Fin.succ (0 : Fin (3+n+1)) := by
    apply Fin.ext
    change 1 % (3+n+1+1) = 0 % (3+n+1) + 1
    simp [Nat.mod_eq_of_lt (show 1 < 3+n+1+1 by omega)]
  rw [h]
  rfl

theorem cons_zero {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a b : M) :
    (b :> a :> v) (0 : Fin (3+n+1+1)) = b := by
  have h : (0 : Fin (3+n+1+1)) = (⟨0, by omega⟩ : Fin (3+n+1+1)) := by
    apply Fin.ext
    change 0 % (3+n+1+1) = 0
    exact Nat.zero_mod _
  rw [h]
  rfl

theorem single_three {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a : M) :
    (a :> v) (3 : Fin (3+n+1)) = v 2 := by
  have h : (3 : Fin (3+n+1)) = Fin.succ (2 : Fin (3+n)) := by
    apply Fin.ext
    change 3 % (3+n+1) = 2 % (3+n) + 1
    simp [Nat.mod_eq_of_lt (show 3 < 3+n+1 by omega), Nat.mod_eq_of_lt (show 2 < 3+n by omega)]
  rw [h]
  rfl
theorem single_zero {M : Type} (n : ℕ) (v : Fin (3+n) → M) (a : M) :
    (a :> v) (0 : Fin (3+n+1)) = a := by
  have h : (0 : Fin (3+n+1)) = (⟨0, by omega⟩ : Fin (3+n+1)) := by
    apply Fin.ext
    change 0 % (3+n+1) = 0
    exact Nat.zero_mod _
  rw [h]
  rfl

theorem packed_eval {M : Type} [Structure language M] (n : ℕ)
    (ψ : Semisentence language (4+n)) (v : Fin (3+n) → M) :
    (packed n ψ).Eval v Empty.elim ↔
      ∃ a b : M,
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![a,Structure.func (L := language) addCode ![v 2,Structure.func (L := language) oneCode Fin.elim0]] ∧
        Structure.rel (L := language) Language.ORing.Rel.lt
          ![b,Structure.func (L := language) addCode ![v 2,Structure.func (L := language) oneCode Fin.elim0]] ∧
        graph.Eval ![v 2,a,b] Empty.elim ∧
        ψ.Eval (Fin.append ![v 0,v 1,a,b] (fun i => v (Fin.natAdd 3 i))) Empty.elim := by
  simp only [packed, bexs, Semiformula.eval_ex]
  apply exists_congr
  intro a
  change ((Semiformula.rel (L := language) Language.ORing.Rel.lt
    ![.bvar 0,.func addCode ![.bvar 3,.func oneCode Fin.elim0]]).Eval (a :> v) Empty.elim ∧
    ∃ b : M, (Semiformula.rel (L := language) Language.ORing.Rel.lt
      ![.bvar 0,.func addCode ![.bvar 4,.func oneCode Fin.elim0]]).Eval (b :> a :> v) Empty.elim ∧
    ((Rew.embSubsts ![#4,#1,#0] ▹ graph).Eval (b :> a :> v) Empty.elim) ∧
    ((Rew.embSubsts (matrixSub n) ▹ ψ).Eval (b :> a :> v) Empty.elim)) ↔ _
  have hb1 : (Semiterm.val (L := language) (a :> v) Empty.elim ∘
      ![#0,.func addCode ![#3,.func oneCode Fin.elim0]]) =
      ![a,Structure.func (L := language) addCode ![v 2,Structure.func (L := language) oneCode Fin.elim0]] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact single_zero n v a
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) addCode
        (Semiterm.val (L := language) (a :> v) Empty.elim ∘ ![#3,.func oneCode Fin.elim0]) = _
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k
      · exact single_three n v a
      · refine Fin.cases ?_ (fun m => Fin.elim0 m) l
        change Structure.func (L := language) oneCode (Semiterm.val (L := language) (a :> v) Empty.elim ∘ Fin.elim0) = _
        congr 1
        exact Subsingleton.elim _ _
  have hb2 (b : M) : (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘
      ![#0,.func addCode ![#4,.func oneCode Fin.elim0]]) =
      ![b,Structure.func (L := language) addCode ![v 2,Structure.func (L := language) oneCode Fin.elim0]] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact cons_zero n v a b
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) addCode
        (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘ ![#4,.func oneCode Fin.elim0]) = _
      congr 1
      funext k
      refine Fin.cases ?_ (fun l => ?_) k
      · exact cons_four n v a b
      · refine Fin.cases ?_ (fun m => Fin.elim0 m) l
        change Structure.func (L := language) oneCode (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘ Fin.elim0) = _
        congr 1
        exact Subsingleton.elim _ _
  have hg (b : M) : (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘
      Rew.embSubsts ![#4,#1,#0] ∘ Semiterm.bvar) = ![v 2,a,b] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact cons_four n v a b
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact cons_one n v a b
      · exact Fin.cases (cons_zero n v a b) (fun l => Fin.elim0 l) k
  have hp (b : M) : (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘
      Rew.embSubsts (matrixSub n) ∘ Semiterm.bvar) =
        Fin.append ![v 0,v 1,a,b] (fun i => v (Fin.natAdd 3 i)) := by
    have h := matrixSub_eval n (b :> a :> v)
    simp only [cons_two,cons_three,cons_one,cons_zero,cons_tail] at h
    simpa only [Function.comp_def,Rew.embSubsts_bvar] using h
  have hgfree (b : M) : (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘
      Rew.embSubsts ![#4,#1,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have hpfree (b : M) : (Semiterm.val (L := language) (b :> a :> v) Empty.elim ∘
      Rew.embSubsts (matrixSub n) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp only [Semiformula.eval_rel,Semiformula.eval_rew,hb1,hb2,hg,hp,hgfree,hpfree]
  constructor
  · rintro ⟨ha,b,hb,hg,hψ⟩; exact ⟨b,ha,hb,hg,hψ⟩
  · rintro ⟨b,ha,hb,hg,hψ⟩; exact ⟨ha,b,hb,hg,hψ⟩
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelPacking (n : ℕ) (ψ : Semisentence language (4+n)) (a b : M) :
    ∃ t : M, ∀ v : Fin (3+n) → M, v 2 = t →
      ((packed n ψ).Eval v Empty.elim ↔
        ψ.Eval (Fin.append ![v 0,v 1,a,b] (fun i => v (Fin.natAdd 3 i))) Empty.elim) := by
  obtain ⟨t,hgraph,hunique,ha,hb⟩ := PRABoundedPairGraph.modelPairGraphBounded a b
  refine ⟨t, fun v hv => ?_⟩
  rw [packed_eval, hv]
  constructor
  · rintro ⟨c,d,_,_,hc,hd⟩
    have he := hunique c d hc
    simpa [he.1,he.2] using hd
  · intro h
    exact ⟨a,b,ha,hb,hgraph,h⟩
end models
def align (n : ℕ) (ψ : Semisentence language (3+(n+1))) : Semisentence language (4+n) :=
  cast (congrArg (Semisentence language) (by omega)) ψ

def packAll : (n : ℕ) → Semisentence language (3+n) → Semisentence language 3
  | 0, ψ => ψ
  | n+1, ψ => packAll n (packed n (align n ψ))

private theorem hierarchy_cast {k l : ℕ} (e : k = l) (ψ : Semisentence language k)
    (hψ : Hierarchy 𝚺 0 ψ) : Hierarchy 𝚺 0 (cast (congrArg (Semisentence language) e) ψ) := by
  cases e
  exact hψ

theorem align_bounded (n : ℕ) (ψ : Semisentence language (3+(n+1)))
    (hψ : Hierarchy 𝚺 0 ψ) : Hierarchy 𝚺 0 (align n ψ) := by
  unfold align
  exact hierarchy_cast (by omega) ψ hψ

theorem packAll_bounded : ∀ (n : ℕ) (ψ : Semisentence language (3+n)),
    Hierarchy 𝚺 0 ψ → Hierarchy 𝚺 0 (packAll n ψ) := by
  intro n
  induction n with
  | zero => intro ψ hψ; exact hψ
  | succ n ih =>
    intro ψ hψ
    exact ih _ (packed_bounded n _ (align_bounded n ψ hψ))
end DiophantineConsistency.PRAParameterPackingN
