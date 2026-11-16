module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeAtoms
@[expose] public section

/-! Model-valued binder parameters and conservative source-code reserve.
This supplies the changing parameter operation for a future UformulaRec1
Construction, not that Construction itself. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def parameters (b f lo z : V) : V := b ∷ (f ∷ (lo ∷ (z ∷ 0)))

noncomputable def parametersGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out b f lo z. ∃ zs los fs, !adjoinDef zs z 0 ∧ !adjoinDef los lo zs ∧
    !adjoinDef fs f los ∧ !adjoinDef out b fs”

theorem parameters_graph (out b f lo z : V) :
    parametersGraph.val.Evalb ![out,b,f,lo,z] ↔ out=parameters b f lo z := by
  simp [parametersGraph,parameters]

@[simp] theorem parameters_bound (b f lo z : V) : nth (parameters b f lo z) 0=b := by
  simp [parameters]
@[simp] theorem parameters_free (b f lo z : V) : nth (parameters b f lo z) 1=f := by
  simp [parameters]
@[simp] theorem parameters_allocator (b f lo z : V) : nth (parameters b f lo z) 2=lo := by
  simp [parameters]
@[simp] theorem parameters_reserve (b f lo z : V) : nth (parameters b f lo z) 3=z := by
  have h3 : (3:V)=2+1 := two_add_one_eq_three.symm
  simp [parameters,h3]

/-- Total on all parameter codes; short vectors use Foundation's default nth
value zero. No malformed parameter is asserted to satisfy the guard. -/
noncomputable def advance (param : V) : V :=
  parameters (nth param 2 ∷ nth param 0) (nth param 1) (nth param 2+1) (nth param 3)

noncomputable def advanceGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f lo z bs,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef lo param 2 ∧
    !nthDef z param 3 ∧ !adjoinDef bs lo b ∧ !parametersGraph out bs f (lo+1) z”

theorem advance_graph (out param : V) :
    advanceGraph.val.Evalb ![out,param] ↔ out=advance param := by
  simp [advanceGraph,parameters_graph,advance,Matrix.comp_vecCons'']

instance advance_defined : 𝚺ᴬ₁-Function₁ (advance : V → V) via advanceGraph :=
  .mk fun v => by
    simp [advanceGraph,parameters_graph,advance,Matrix.comp_vecCons'']

instance advance_definable : 𝚺ᴬ₁-Function₁ (advance : V → V) :=
  advance_defined.to_definable

theorem advance_total_unique (param : V) :
    ∃! out, advanceGraph.val.Evalb ![out,param] := by
  refine ⟨advance param,(advance_graph _ _).mpr rfl,?_⟩
  intro out h
  exact (advance_graph _ _).mp h

@[simp] theorem advance_parameters (b f lo z : V) :
    advance (parameters b f lo z)=parameters (lo ∷ b) f (lo+1) z := by
  simp [advance]

theorem advance_zero : advance (0:V)=parameters (0 ∷ 0) 0 1 0 := by
  simp [advance]

/-- The parameter change is independent of the singleton-child index, satisfying
UformulaRec1's required monotonicity without changing allocation by index. -/
theorem advance_index_monotone (param i j : V) (_h : i≤j) :
    (fun _ : V => advance param) i ≤ (fun _ : V => advance param) j := le_rfl

/-- The native equality reserve remains beyond the entire conservative budget. -/
def Guard (b f lo z p : V) : Prop := EnvironmentsValid b f lo z ∧ lo+p≤z

noncomputable def guardGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “b f lo z p. !environmentsGraph b f lo z ∧ lo+p≤z”

theorem guard_graph (b f lo z p : V) :
    guardGraph.val.Evalb ![b,f,lo,z,p] ↔ Guard b f lo z p := by
  simp [guardGraph,Guard,environments_graph,Matrix.comp_vecCons'']

theorem environments_adjoin {b f lo z : V} (h : EnvironmentsValid b f lo z)
    (hr : lo+1≤z) : EnvironmentsValid (lo ∷ b) f (lo+1) z := by
  refine ⟨lt_trans h.1 (by simp),hr,?_,?_⟩
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp
    · have hb : i<len b := by simpa using hi
      simpa using lt_trans (h.2.2.1 i hb) (show lo<lo+1 by simp)
  · intro i hi
    exact lt_trans (h.2.2.2 i hi) (by simp)

theorem binder_label_zero (b f lo : V) :
    VariableLabel lo (qqBvar 0) (lo ∷ b) f := by
  simpa using label_bvar (lo ∷ b) f 0 (by simp)

theorem binder_label_succ (b f lo i : V) (hi : i<len b) :
    VariableLabel (nth b i) (qqBvar (i+1)) (lo ∷ b) f := by
  simpa using label_bvar (lo ∷ b) f (i+1) (by simpa using hi)

/-- Every genuine child descent pays for one fresh binder. -/
theorem guard_binder_child {b f lo z p q : V}
    (h : Guard b f lo z p) (hq : q<p) : Guard (lo ∷ b) f (lo+1) z q := by
  have hqp : q+1≤p := lt_iff_succ_le.mp hq
  have hbudget : (lo+1)+q≤z := by
    calc
      (lo+1)+q = lo+(q+1) := by rw [Arithmetic.add_assoc, Arithmetic.add_comm 1 q]
      _ ≤ lo+p := add_le_add (le_refl lo) hqp
      _ ≤ z := h.2
  have hr : lo+1≤z := le_trans (by simp) hbudget
  exact ⟨environments_adjoin h.1 hr,hbudget⟩

theorem guard_all {b f lo z p : V} (h : Guard b f lo z (qqAll p)) :
    Guard (lo ∷ b) f (lo+1) z p := guard_binder_child h (lt_forall p)

theorem guard_exs {b f lo z p : V} (h : Guard b f lo z (qqExs p)) :
    Guard (lo ∷ b) f (lo+1) z p := guard_binder_child h (lt_exists p)

/-- Binary recursion does not allocate a binder. -/
theorem guard_child {b f lo z p q : V} (h : Guard b f lo z p) (hq : q≤p) :
    Guard b f lo z q := ⟨h.1,le_trans (add_le_add (le_refl lo) hq) h.2⟩

#print axioms parameters_graph
#print axioms advance_graph
#print axioms advance_defined
#print axioms binder_label_zero
#print axioms binder_label_succ
#print axioms advance_total_unique
#print axioms advance_parameters
#print axioms advance_zero
#print axioms advance_index_monotone
#print axioms guard_graph
#print axioms environments_adjoin
#print axioms guard_binder_child
#print axioms guard_all
#print axioms guard_exs
#print axioms guard_child
end M6.PA.RelationalSource.Numeric
