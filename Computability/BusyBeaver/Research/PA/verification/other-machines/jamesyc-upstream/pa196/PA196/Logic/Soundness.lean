module
public import PA196.Logic.FiniteModel
@[expose] public section

/-! Soundness of every exact PA196 rule in a concrete model.
The headline theorem `derivation_one_false` has no consistency or semantic
premise. Its proof is external; it does not assert a PA proof of consistency.
-/
namespace PA196.Logic

def completeBundle (a b c : Nat) :=
  wa (wex c (wa (separation a b c) (point a b c)))
    (wa (eqVac a b c) (memVac a b c))

theorem completeBundle_valid (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b)
    (env : Nat → HF) : evalCode (completeBundle a b c) env := by
  simp only [completeBundle,separation,point,eqVac,memVac,evalCode_and,
    evalCode_ex,evalCode_all,evalCode_imp,evalCode_eq,evalCode_mem]
  simp only [assign_same,assign_ne env ha.symm,assign_ne env hb.symm]
  simp only [assign_comm env hb,evalCode_fresh]
  simp only [assign_same,assign_ne (assign env b _) ha.symm]
  simp only [forall_const,imp_self,and_true]
  have hp := HF.pointedSeparation (fun x => evalCode c (assign env b x)) (env a) (env b)
  rcases hp with ⟨s,hs,hpoint⟩
  refine ⟨s,fun x => ⟨?_,(hs x).2⟩,?_⟩
  · intro hx hprop
    by_cases hab : a = b
    · subst a
      have hself : x.mem x := by simpa using hx
      exact False.elim (HF.not_self x hself)
    · have hxa : (env a).mem x := by simpa [assign,hab] using hx
      exact (hs x).1 hxa hprop
  · simpa only [assign_restore] using hpoint

theorem bundle_valid (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b)
    (env : Nat → HF) : evalCode (bundle a b c) env := by
  have hh := completeBundle_valid a b c ha hb env
  simp only [completeBundle,evalCode_and,evalCode_ex] at hh
  obtain ⟨⟨s,hS,hP⟩,hE,hM⟩ := hh
  simp only [bundle,evalCode_neg,evalCode_imp]
  intro hg
  have hQ := hg hE hM
  have hQ' : ∀ s, evalCode (separation a b c) (assign env c s) →
      ¬ evalCode (point a b c) (assign env c s) := by
    simpa only [qGate,evalCode_all,evalCode_imp,evalCode_neg] using hQ
  exact hQ' s hS hP

theorem head1_valid (d h : Nat) (env : Nat → HF) : evalCode (head1 d h) env := by
  simp only [head1,evalCode_imp,evalCode_ex,evalCode_all]
  rintro ⟨x,hx⟩
  simpa only [assign_overwrite,assign_restore] using hx (env d)

theorem head2_valid (d a h : Nat) (env : Nat → HF) : evalCode (head2 d a h) env := by
  simp only [head2,evalCode_imp,evalCode_all]
  by_cases hda : d = a
  · subst a
    exact id
  · intro hh x y
    rw [← assign_comm env hda]
    exact hh y x

theorem head3_valid (h d a : Nat) (env : Nat → HF) : evalCode (head3 h d a) env := by
  simp only [head3,evalCode_imp,evalCode_mem,evalCode_eq]
  intro hm he
  exact he ▸ hm

theorem head4_valid (h d a : Nat) (env : Nat → HF) : evalCode (head4 h d a) env := by
  simp only [head4,evalCode_imp,evalCode_mem,evalCode_eq]
  intro he hm
  exact he ▸ hm

theorem head5_valid (d h : Nat) (env : Nat → HF) : evalCode (head5 d h) env := by
  simp only [head5,evalCode_ex,evalCode_eq]
  refine ⟨env h,?_⟩
  by_cases hhd : h = d <;> simp [assign,hhd]

theorem head6_valid (d a h : Nat) (env : Nat → HF) : evalCode (head6 d a h) env := by
  simp only [head6,evalCode_imp,evalCode_all]
  intro ha hi x
  exact hi x (ha x)

theorem rho8_valid (a b c u : Nat) (env : Nat → HF) : evalCode (rho8 a b c u) env := by
  classical
  simp only [rho8,evalCode_imp]
  intro h hac _
  apply Classical.byContradiction
  intro hc
  exact hc (hac (h (fun hct => False.elim (hc hct))))

/-- Induction on the actual finite proof tree, with no additional logical rules. -/
theorem derivation_sound {n : Nat} (d : Derivation n) (env : Nat → HF) : evalCode n env := by
  induction d generalizing env with
  | mp da dab iha ihab => exact (evalCode_imp _ _ env).mp (ihab env) (iha env)
  | all a d ih =>
    rw [evalCode_all]
    intro x
    exact ih (assign env a x)
  | h1 d h => exact head1_valid d h env
  | h2 d a h => exact head2_valid d a h env
  | h3 h d a => exact head3_valid h d a env
  | h4 h d a => exact head4_valid h d a env
  | h5 d h => exact head5_valid d h env
  | h6 d a h => exact head6_valid d a h env
  | r8 a b c u _ => exact rho8_valid a b c u env
  | gate a b c ha hb => exact bundle_valid a b c ha hb env

theorem derivation_one_false (d : Derivation 1) : False :=
  evalCode_one (fun _ => .node []) (derivation_sound d (fun _ => .node []))

theorem not_refutable : ¬ Nonempty (Derivation 1) := fun ⟨d⟩ => derivation_one_false d

#print axioms bundle_valid
#print axioms derivation_sound
#print axioms derivation_one_false
#print axioms not_refutable
end PA196.Logic
