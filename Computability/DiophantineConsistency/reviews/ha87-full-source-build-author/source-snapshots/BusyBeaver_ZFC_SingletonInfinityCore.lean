import FirstOrder.Fol

/-!
The noncircular singleton index for an ordinary-Infinity construction.

This first checkpoint follows the least-singleton-closed-set cut in
`ZF/stdzf/coq/Std_setinf.v:or_to_zf_core`, upstream
297ab8df7e5de329605c3875b4934643b371a5e3, used by the attributed Mira-Cult /
Jeff verification through `S_ax.v:S_inf` and `S_main.v:ZF_to_S0`.

The base below has only Extensionality, Pairing and actual first-order
Separation. It does not contain Infinity or Separation for arbitrary semantic
predicates. A literal ZMem formula cuts the least singleton-closed index out
of an already supplied singleton-closed container. The resulting index has
set induction and formula induction. At an empty root, singleton injectivity
and exclusion of the root from the successor range give the elementary
inductive-structure conditions needed by the separate finite-attempt graph
argument. This checkpoint does not prove ordinary `Inf_form` or construct a
full `ZFAxioms` value; no internal omega or recursion theorem is assumed.
-/

namespace SetTheory.BusyBeaver.ZFC.SingletonInfinity

open Form

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The small base required by the least singleton-closed index cut. -/
structure Base (mem : V → V → Prop) : Prop where
  ext : ∀ a b, (∀ z, mem z a ↔ mem z b) → a = b
  pair : ∀ a b, ∃ p, ∀ z, mem z p ↔ z = a ∨ z = b
  sep : ∀ (phi : Form) (env : Nat → V) (a : V),
    ∃ b, ∀ z, mem z b ↔ mem z a ∧ Sat mem (scons z env) phi

noncomputable def singleton (B : Base mem) (a : V) : V := (B.pair a a).choose

theorem singleton_spec (B : Base mem) (a z : V) :
    mem z (singleton B a) ↔ z = a := by
  simpa only [singleton, or_self] using (B.pair a a).choose_spec z

theorem singleton_unique (B : Base mem) (a s : V)
    (hs : ∀ z, mem z s ↔ z = a) : s = singleton B a :=
  B.ext s (singleton B a) (fun z => (hs z).trans (singleton_spec B a z).symm)

theorem singleton_injective (B : Base mem) : Function.Injective (singleton B) := by
  intro a b hab
  exact (singleton_spec B b a).mp (hab ▸ (singleton_spec B a a).mpr rfl)

theorem empty_not_singleton (B : Base mem) (e : V) (he : ∀ z, ¬ mem z e) (a : V) :
    singleton B a ≠ e :=
  fun h => he a (h ▸ (singleton_spec B a a).mpr rfl)

def Closed (B : Base mem) (X : V) : Prop :=
  ∀ x, mem x X → mem (singleton B x) X

theorem closed_of_exact_singletons (B : Base mem) (X : V)
    (h : ∀ x, mem x X → ∃ s, mem s X ∧ ∀ z, mem z s ↔ z = x) : Closed B X := by
  intro x hx
  obtain ⟨s, hsX, hs⟩ := h x hx
  simpa only [singleton_unique B x s hs] using hsX

def LeastMember (B : Base mem) (e z : V) : Prop :=
  ∀ X, mem e X → Closed B X → mem z X

/-- The source is slot i, and the exact singleton is slot j. -/
def singForm (i j : Nat) : Form :=
  fAll (fIff (fMem 0 (j + 1)) (fEq 0 (i + 1)))

theorem sat_singForm (B : Base mem) (env : Nat → V) (i j : Nat) :
    Sat mem env (singForm i j) ↔ env j = singleton B (env i) := by
  change (∀ z, Sat mem (scons z env)
    (fIff (fMem 0 (j + 1)) (fEq 0 (i + 1)))) ↔ _
  exact ⟨fun hs => B.ext _ _ fun z => ((Sat_fIff (mem := mem)).mp (hs z)).trans
      (singleton_spec B (env i) z).symm,
    fun hs z => (Sat_fIff (mem := mem)).mpr (show mem z (env j) ↔ z = env i by
      rw [hs]; exact singleton_spec B (env i) z)⟩

def closedForm (i : Nat) : Form :=
  fAll (fImp (fMem 0 (i + 1))
    (fEx (fAnd (fMem 0 (i + 2)) (singForm 1 0))))

theorem sat_closedForm (B : Base mem) (env : Nat → V) (i : Nat) :
    Sat mem env (closedForm i) ↔ Closed B (env i) := by
  change (∀ x, mem x (env i) → ∃ s, mem s (env i) ∧
    Sat mem (scons s (scons x env)) (singForm 1 0)) ↔ _
  refine ⟨fun hc x hx => ?_,
    fun hc x hx => ⟨singleton B x, hc x hx, (sat_singForm B _ 1 0).mpr rfl⟩⟩
  obtain ⟨s, hs, hSing⟩ := hc x hx
  have heq : s = singleton B x := (sat_singForm B _ 1 0).mp hSing
  simpa only [heq] using hs

/-- Membership in every singleton-closed set containing the distinguished root. -/
def zMemForm (z e : Nat) : Form :=
  fAll (fImp (fAnd (fMem (e + 1) 0) (closedForm 0)) (fMem (z + 1) 0))

theorem sat_zMemForm (B : Base mem) (env : Nat → V) (z e : Nat) :
    Sat mem env (zMemForm z e) ↔ LeastMember B (env e) (env z) := by
  change (∀ X, mem (env e) X ∧ Sat mem (scons X env) (closedForm 0) →
    mem (env z) X) ↔ _
  exact ⟨fun h X he hc => h X ⟨he, (sat_closedForm B _ 0).mpr hc⟩,
    fun h X hx => h X hx.1 ((sat_closedForm B _ 0).mp hx.2)⟩

/-- Induction here quantifies over represented sets; it is not unrestricted
induction over external semantic predicates. -/
structure Index (B : Base mem) (e N : V) : Prop where
  zero_mem : mem e N
  closed : Closed B N
  least : ∀ X, mem e X → Closed B X → ∀ z, mem z N → mem z X

/-- One actual ZMem Separation instance supplies the singleton index. -/
theorem index_of_container (B : Base mem) (e Y : V) (heY : mem e Y)
    (hY : Closed B Y) : ∃ N, Index B e N := by
  obtain ⟨N, hN⟩ := B.sep (zMemForm 0 1) (fun _ => e) Y
  have hSpec (z : V) : mem z N ↔ mem z Y ∧ LeastMember B e z :=
    (hN z).trans (and_congr Iff.rfl (sat_zMemForm B _ 0 1))
  refine ⟨N, (hSpec e).mpr ⟨heY, fun _ he _ => he⟩, fun z hz => ?_,
    fun X heX hX z hz => ((hSpec z).mp hz).2 X heX hX⟩
  obtain ⟨hzY, hzLeast⟩ := (hSpec z).mp hz
  exact (hSpec (singleton B z)).mpr ⟨hY z hzY, fun X heX hX => hX z (hzLeast X heX hX)⟩

/-- Formula induction uses the actual source formula's Separation instance. -/
theorem index_formula_induction (B : Base mem) {e N : V} (hN : Index B e N)
    (phi : Form) (env : Nat → V) (hZero : Sat mem (scons e env) phi)
    (hStep : ∀ x, mem x N → Sat mem (scons x env) phi →
      Sat mem (scons (singleton B x) env) phi) :
    ∀ x, mem x N → Sat mem (scons x env) phi := by
  obtain ⟨X, hX⟩ := B.sep phi env N
  have heX : mem e X := (hX e).mpr ⟨hN.zero_mem, hZero⟩
  have hcX : Closed B X := by
    intro x hx
    obtain ⟨hxN, hPhi⟩ := (hX x).mp hx
    exact (hX (singleton B x)).mpr ⟨hN.closed x hxN, hStep x hxN hPhi⟩
  exact fun x hx => ((hX x).mp (hN.least X heX hcX x hx)).2

end SetTheory.BusyBeaver.ZFC.SingletonInfinity
