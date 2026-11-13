module
public import PA196.Arithmetic.CommandStep
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CommandWord
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CommandStep VectorAppend
attribute [local irreducible] stepGraph

/-- Left-to-right execution of an HFS vector of source command atoms. -/
noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “z word initial. z=initial”
  succ := .mkSigma “z previous i word initial. ∃ atom, !nthDef atom word i ∧ !stepGraph z atom previous”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def construction : PR.Construction V blueprint where
  zero := fun p => p 1
  succ := fun p i previous => stepValue (nth (p 0) i) previous
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint,step_graph]

noncomputable def executePrefix (n word initial : V) : V := construction.result ![word,initial] n
noncomputable def prefixGraph : 𝚺ᴬ₁.Semisentence 4 := blueprint.resultDef
@[simp] theorem prefix_zero (word initial : V) : executePrefix 0 word initial=initial := by simp [executePrefix,construction]
@[simp] theorem prefix_succ (n word initial : V) :
    executePrefix (n+1) word initial=stepValue (nth word n) (executePrefix n word initial) := by simp [executePrefix,construction]

theorem prefix_graph (z n word initial : V) :
    prefixGraph.val.Evalb ![z,n,word,initial] ↔ z=executePrefix n word initial := by
  simpa [prefixGraph,executePrefix] using (construction (V := V)).result_defined_iff ![z,n,word,initial]
instance prefix_defined : 𝚺ᴬ₁-Function₃ (executePrefix : V → V → V → V) via prefixGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2,v 3] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases he with rfl|rfl|rfl|rfl <;> rfl
  rw [hv]
  exact prefix_graph _ _ _ _
instance prefix_definable : 𝚺ᴬ₁-Function₃ (executePrefix : V → V → V → V) := prefix_defined.to_definable

attribute [local irreducible] prefixGraph
noncomputable def wordValue (word initial : V) : V := executePrefix (len word) word initial
noncomputable def wordGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “z word initial. ∃ n, !lenDef n word ∧ !prefixGraph z n word initial”
theorem word_graph (z word initial : V) : wordGraph.val.Evalb ![z,word,initial] ↔ z=wordValue word initial := by
  simp [wordGraph,prefix_graph,wordValue]
instance word_defined : 𝚺ᴬ₁-Function₂ (wordValue : V → V → V) via wordGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl|rfl|rfl <;> rfl
  rw [hv]
  exact word_graph _ _ _
instance word_definable : 𝚺ᴬ₁-Function₂ (wordValue : V → V → V) := word_defined.to_definable

theorem prefix_halted (n word : V) : executePrefix n word 0=0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [ih]

@[simp] theorem word_zero (initial : V) : wordValue 0 initial=initial := by simp [wordValue]
@[simp] theorem word_halted (word : V) : wordValue word 0=0 := prefix_halted _ _

theorem prefix_cons (n atom word initial : V) :
    executePrefix (n+1) (atom ∷ word) initial=executePrefix n word (stepValue atom initial) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    simpa using prefix_succ (0 : V) (atom ∷ word) initial
  case succ n ih => simp only [prefix_succ,nth_adjoin_succ,ih]

@[simp] theorem word_cons (atom word initial : V) :
    wordValue (atom ∷ word) initial=wordValue word (stepValue atom initial) := by
  simp only [wordValue,len_adjoin,prefix_cons]

theorem prefix_append_left (n xs ys initial : V) (hn : n≤len xs) :
    executePrefix n (append xs ys) initial=executePrefix n xs initial := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    have hlt : n<len xs := succ_le_iff_lt.mp hn
    rw [prefix_succ,prefix_succ,nth_append_left xs ys hlt,ih (le_of_lt hlt)]

theorem prefix_append_right (n xs ys initial : V) :
    executePrefix (len xs+n) (append xs ys) initial=executePrefix n ys (executePrefix (len xs) xs initial) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using prefix_append_left (len xs) xs ys initial (by rfl)
  case succ n ih =>
    rw [show len xs+(n+1)=(len xs+n)+1 by ac_rfl,prefix_succ,ih,prefix_succ,nth_append_right]

theorem word_append (xs ys initial : V) :
    wordValue (append xs ys) initial=wordValue ys (wordValue xs initial) := by
  simp only [wordValue,len_append,prefix_append_right]

theorem word_total_unique (word initial : V) : ∃! z,wordGraph.val.Evalb ![z,word,initial] :=
  ⟨wordValue word initial,(word_graph _ _ _).mpr rfl,fun _ hz => (word_graph _ _ _).mp hz⟩

#print axioms word_graph
#print axioms prefix_cons
#print axioms word_append
end PA196.Arithmetic.CommandWord

