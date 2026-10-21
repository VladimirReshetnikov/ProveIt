import Init

/-!
A logical obstruction for the high-binder-vacuity proposal.

Every object below is independent of the machine and of set-theoretic axioms.
`Provable` is deliberately stronger than the retained logical subsystem:
it permits every helper binder above both atomic indices, and membership
vacuity at every binder above both indices (not merely above their sum).
The counterexample therefore also rules out recovery in the narrower system.

Predicates on worlds serve as formulas. A syntactic calculus maps to this
one by structural interpretation. No claim is made about seed-K bundles.
-/

namespace TailQuantifiers

abbrev World := Nat → Bool
abbrev Formula := World → Prop
def Valid (A : Formula) : Prop := ∀ e, A e
def imp (A B : Formula) : Formula := fun e => A e → B e
def bot : Formula := fun _ => False
def top : Formula := fun _ => True
def neg (A : Formula) : Formula := imp A bot
def eqAt (a b : Nat) : Formula := fun e => e a = e b
def relAt (a b : Nat) : Formula := fun e => e a = false ∧ e b = true
def Agree (i : Nat) (e f : World) : Prop := ∀ k, k < i → e k = f k
def allAt (i : Nat) (A : Formula) : Formula :=
  fun e => ∀ f, Agree i e f → A f
def exAt (i : Nat) (A : Formula) : Formula :=
  fun e => ∃ f, Agree i e f ∧ A f

theorem agree_symm {i : Nat} {e f : World} (h : Agree i e f) : Agree i f e :=
  fun k hk => (h k hk).symm

theorem ex_duality (i : Nat) (A : Formula) (e : World) :
    exAt i A e ↔ neg (allAt i (neg A)) e := by
  classical
  constructor
  · intro h hn
    exact h.elim (fun f hf => hn f hf.1 hf.2)
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h (fun f hf hA => hn ⟨f, hf, hA⟩)

theorem truth_valid : Valid top := fun _ => True.intro
theorem mp_valid {A B : Formula} (hA : Valid A) (hAB : Valid (imp A B)) :
    Valid B := fun e => hAB e (hA e)
theorem gen_valid (i : Nat) {A : Formula} (hA : Valid A) : Valid (allAt i A) :=
  fun _ f _ => hA f
theorem efq_valid (A : Formula) : Valid (imp bot A) := fun _ h => h.elim

theorem rho1_valid (i j : Nat) : Valid (exAt i (eqAt i j)) := by
  intro e
  by_cases hji : j < i
  · let f : World := fun k => if k = i then e j else e k
    refine ⟨f, ?_, ?_⟩
    · intro k hk
      simp [f, Nat.ne_of_lt hk]
    · simp [eqAt, f]
  · let f : World := fun k => if k < i then e k else false
    refine ⟨f, ?_, ?_⟩
    · intro k hk
      simp [f, hk]
    · simp [eqAt, f, hji]

theorem rho2_valid (i : Nat) (A B : Formula) :
    Valid (imp (allAt i (imp A B)) (imp (allAt i A) (allAt i B))) :=
  fun _ hAB hA f hf => hAB f hf (hA f hf)

theorem rho3_valid (a b c : Nat) :
    Valid (imp (eqAt a b) (imp (relAt c a) (relAt c b))) := by
  intro e hab hca
  exact ⟨hca.1, hab ▸ hca.2⟩

theorem rho4_valid (i j : Nat) (A : Formula) :
    Valid (imp (allAt i (allAt j A)) (allAt j (allAt i A))) := by
  intro e h f hef g hfg
  let u : World := fun k => if k < i then e k else g k
  refine h u ?_ g ?_
  · intro k hk
    simp [u, hk]
  · intro k hk
    by_cases hki : k < i
    · simp [u, hki]
      exact (hef k hk).trans (hfg k hki)
    · simp [u, hki]

theorem rho5_valid (a b c : Nat) :
    Valid (imp (eqAt c a) (imp (relAt c b) (relAt a b))) := by
  intro e hca hcb
  exact ⟨hca ▸ hcb.1, hcb.2⟩

theorem rho6_valid (i : Nat) (A : Formula) :
    Valid (imp (exAt i (allAt i A)) A) := by
  intro e h
  exact h.elim (fun f hf => hf.2 e (agree_symm hf.1))

theorem merged_equality_valid (a b c r : Nat) (ha : a < r) (hb : b < r) :
    Valid (imp (eqAt c a) (imp (eqAt c b) (allAt r (eqAt a b)))) := by
  intro e hca hcb f hef
  exact (hef a ha).symm.trans (hca.symm.trans (hcb.trans (hef b hb)))

theorem rho8_valid (A B C U : Formula) :
    Valid (imp (imp (imp C U) A) (imp (imp A C) (imp B C))) := by
  classical
  intro e h hAC _
  by_cases hC : C e
  · exact hC
  · exact hAC (h (fun hC' => (hC hC').elim))

theorem high_vacuity_valid (a b c : Nat) (ha : a < c) (hb : b < c) :
    Valid (imp (relAt a b) (allAt c (relAt a b))) := by
  intro e hab f hef
  exact ⟨(hef a ha).symm.trans hab.1, (hef b hb).symm.trans hab.2⟩

theorem irreflexive_falsity (a : Nat) : Valid (neg (relAt a a)) := by
  intro e h
  have hbad : false = true := h.1.symm.trans h.2
  cases hbad

inductive Provable : Formula → Prop where
  | truth : Provable top
  | mp {A B : Formula} : Provable A → Provable (imp A B) → Provable B
  | gen (i : Nat) {A : Formula} : Provable A → Provable (allAt i A)
  | efq (A : Formula) : Provable (imp bot A)
  | r1 (i j : Nat) : Provable (exAt i (eqAt i j))
  | r2 (i : Nat) (A B : Formula) :
      Provable (imp (allAt i (imp A B)) (imp (allAt i A) (allAt i B)))
  | r3 (a b c : Nat) : Provable (imp (eqAt a b) (imp (relAt c a) (relAt c b)))
  | r4 (i j : Nat) (A : Formula) :
      Provable (imp (allAt i (allAt j A)) (allAt j (allAt i A)))
  | r5 (a b c : Nat) : Provable (imp (eqAt c a) (imp (relAt c b) (relAt a b)))
  | r6 (i : Nat) (A : Formula) : Provable (imp (exAt i (allAt i A)) A)
  | rG (a b c r : Nat) (ha : a < r) (hb : b < r) :
      Provable (imp (eqAt c a) (imp (eqAt c b) (allAt r (eqAt a b))))
  | r8 (A B C U : Formula) :
      Provable (imp (imp (imp C U) A) (imp (imp A C) (imp B C)))
  | vac (a b c : Nat) (ha : a < c) (hb : b < c) :
      Provable (imp (relAt a b) (allAt c (relAt a b)))

theorem sound {A : Formula} (h : Provable A) : Valid A := by
  induction h with
  | truth => exact truth_valid
  | mp _ _ ihA ihAB => exact mp_valid ihA ihAB
  | gen i _ ih => exact gen_valid i ih
  | efq A => exact efq_valid A
  | r1 i j => exact rho1_valid i j
  | r2 i A B => exact rho2_valid i A B
  | r3 a b c => exact rho3_valid a b c
  | r4 i j A => exact rho4_valid i j A
  | r5 a b c => exact rho5_valid a b c
  | r6 i A => exact rho6_valid i A
  | rG a b c r ha hb => exact merged_equality_valid a b c r ha hb
  | r8 A B C U => exact rho8_valid A B C U
  | vac a b c ha hb => exact high_vacuity_valid a b c ha hb

theorem not_valid_missing_vacuity :
    ¬ Valid (imp (relAt 2 3) (allAt 1 (relAt 2 3))) := by
  intro h
  let e : World := fun k => if k = 3 then true else false
  let f : World := fun _ => false
  have he : relAt 2 3 e := ⟨rfl, rfl⟩
  have hef : Agree 1 e f := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k => exact False.elim ((Nat.not_lt_of_ge
        (Nat.succ_le_succ (Nat.zero_le k))) hk)
  have hfalse := (h e he f hef).2
  cases hfalse

theorem not_provable_missing_vacuity :
    ¬ Provable (imp (relAt 2 3) (allAt 1 (relAt 2 3))) :=
  fun h => not_valid_missing_vacuity (sound h)

#print axioms sound
#print axioms not_valid_missing_vacuity
#print axioms not_provable_missing_vacuity

end TailQuantifiers
