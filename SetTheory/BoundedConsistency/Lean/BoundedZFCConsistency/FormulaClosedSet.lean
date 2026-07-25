import BoundedZFCConsistency.CodePredicate

/-!
# A formula-closed set exists in every model of ZF

`BoundedZFCConsistency.CodePredicate` defines `IsFormCodeSem` as the
intersection of all formula-closed sets and proves both of its induction
principles relative to the hypothesis `FormulaClosed H C0` — with no closed set
at all the intersection is vacuous and no induction principle can hold.  This
module discharges that hypothesis: in every model of `ZFAxioms` some set is
formula-closed, so the induction principles hold outright.

## The reduction

The eight closure clauses are not proved separately.  Every code the table in
`CodePredicate` asks for is a Kuratowski pair whose first component is an
internal numeral and whose second component is either a member of the set or a
Kuratowski pair of two members, so a single pair of conditions implies all
eight:

```text
Sub mem (omegaV H) C   and   a, b ∈ C → ⟨a, b⟩ ∈ C
```

`formulaClosed_of_pairClosed` records that reduction, and the rest of the
module constructs one pairing-closed superset of the internal omega.

## Why the existing closure theorem does not apply directly

`ZF.Zf.ClosureFO_of_ZF` closes a seed under a definable *set-like* relation,
and such a relation takes one input and one output: from `v` in the closure it
admits every `u` with `R u v`.  Kuratowski pairing is genuinely binary, and no
unary relation can force `⟨a, b⟩` into a set from `a` and `b` separately, since
the single witness `v` never sees both arguments at once.

What the existing theorem *does* supply is a set `w` closed under the unary
operation `pairStep`, one step of the pairing construction:

```text
pairStep v  =  v ∪ { ⟨a, b⟩ : a, b ∈ v }
```

`pairStep` is a genuine internal operation — its pair image is two applications
of Replacement followed by a Union — and it is inflationary and monotone.  So
`w` contains `omegaV H` and is closed under `pairStep`, but it is only *some*
such set: nothing says its elements are the iterates `pairStep^k (omegaV H)`,
and the union of an arbitrary pairing-closed-under-`pairStep` set need not be
pairing-closed, because two of its elements need not lie below a common one.

## Cutting the iterates out by intersection

The missing directedness is recovered without any recursion theorem, by the
same intersection presentation that `CodePredicate` uses for the code predicate
itself.  Call `D` **step-closed** when `omegaV H ∈ D` and `D` is closed under
`pairStep`, and put

```text
stepClosure H w  =  { p ∈ w : p belongs to every step-closed set }
```

Separation supplies it, and it is itself step-closed, so it is the least
step-closed set: `stepClosure_ind` is an induction principle for it, relative
only to definability of the property, exactly as `omega_ind` is for the
internal omega.  Two instances of that principle finish the construction:

* every element of `stepClosure H w` contains `omegaV H`;
* any two elements of `stepClosure H w` lie below a common element of it.

The second is the directedness that the ambient `w` lacked.  Its union is then
a pairing-closed superset of the internal omega, and `exists_formulaClosed`
follows from the reduction.

The construction uses neither Powerset nor Regularity, matching the six
axioms bundled in `ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section FormulaClosedSet

variable {V : Type u} {mem : V → V → Prop}

/-! ## The reduction to closure under Kuratowski pairing

Each of the eight clauses of `FormulaClosed` asks for a pair whose components
are already available: the tag is an internal numeral, hence a member of the
internal omega, and the payload is a member of the set or a pair of two such.
The atomic clauses additionally use that the internal omega is included in the
set, and the falsity clause uses that the empty set is an internal natural. -/

/-- **The reduction.**  A superset of the internal omega closed under
Kuratowski pairing is formula-closed.  This is the only interface between the
coding table of `CodePredicate` and the construction below, and it is stated
publicly because any other construction of a formula-closed set can use it
too. -/
theorem formulaClosed_of_pairClosed (H : ZFAxioms mem) {C : V}
    (hom : Sub mem (omegaV H) C)
    (hpair : ∀ a b, mem a C → mem b C → mem (kpair H a b) C) :
    FormulaClosed H C :=
  have hnat : ∀ t : Nat, mem (natV H t) C := fun t => hom _ (natV_mem_omega H t)
  ⟨fun a b ha hb => hpair _ _ (hnat 0) (hpair a b (hom a ha) (hom b hb)),
   fun a b ha hb => hpair _ _ (hnat 1) (hpair a b (hom a ha) (hom b hb)),
   hpair _ _ (hnat 2) (hom _ (vempty_in_omega H)),
   fun a b ha hb => hpair _ _ (hnat 3) (hpair a b ha hb),
   fun a b ha hb => hpair _ _ (hnat 4) (hpair a b ha hb),
   fun a b ha hb => hpair _ _ (hnat 5) (hpair a b ha hb),
   fun _ ha => hpair _ _ (hnat 6) ha,
   fun _ ha => hpair _ _ (hnat 7) ha⟩

/-! ## The pair image of a set

`{ ⟨a, b⟩ : a, b ∈ v }` is built as the union of the row images
`{ ⟨a, b⟩ : b ∈ v }`, each of which is an instance of Replacement along the
graph of `fun b => kpair H a b`, and the rows are collected by a second
Replacement along `fun a => kpImg H a v`.  Both graph formulas carry their
parameter in slot `2`, the first free slot of a `relOf` environment. -/

/-- The graph of `fun x => kpair H a x`, with `a` as the parameter in slot
`2`. -/
def psiKpF : Form := fKPairF 0 2 1

theorem psiKpF_rel (H : ZFAxioms mem) (a y x : V) :
    relOf mem psiKpF (fun _ => a) y x ↔ y = kpair H a x := by
  unfold relOf psiKpF
  exact fKPairF_spec H (scons y (scons x (fun _ => a))) 0 2 1

theorem psiKpF_functional (H : ZFAxioms mem) (a : V) :
    Functional (relOf mem psiKpF (fun _ => a)) := by
  intro x y1 y2 h1 h2
  rw [psiKpF_rel H a y1 x] at h1
  rw [psiKpF_rel H a y2 x] at h2
  rw [h1, h2]

/-- `kpImg H a v = { ⟨a, b⟩ : b ∈ v }`, one row of the pair image. -/
noncomputable def kpImg (H : ZFAxioms mem) (a v : V) : V :=
  (H.repl psiKpF (fun _ => a) (psiKpF_functional H a) v).choose

theorem kpImg_spec (H : ZFAxioms mem) (a v y : V) :
    mem y (kpImg H a v) ↔ ∃ b, mem b v ∧ y = kpair H a b := by
  unfold kpImg
  rw [(H.repl psiKpF (fun _ => a) (psiKpF_functional H a) v).choose_spec y]
  constructor
  · rintro ⟨b, hb, hrel⟩
    exact ⟨b, hb, (psiKpF_rel H a y b).mp hrel⟩
  · rintro ⟨b, hb, hy⟩
    exact ⟨b, hb, (psiKpF_rel H a y b).mpr hy⟩

/-- The graph of `fun x => kpImg H x v`, with `v` as the parameter in slot `2`.

| de Bruijn slot | contents                  |
| -------------- | ------------------------- |
| `0`            | the candidate row         |
| `1`            | the first component `x`   |
| `2`            | the parameter `v`         |
-/
def psiPImgF : Form :=
  fSetByF 0 (fEx (fAnd (fMem 0 4) (fKPairF 1 3 0)))

theorem psiPImgF_rel (H : ZFAxioms mem) (v y x : V) :
    relOf mem psiPImgF (fun _ => v) y x ↔ y = kpImg H x v := by
  unfold relOf psiPImgF
  refine fSetByF_spec H (scons y (scons x (fun _ => v))) 0
    (fEx (fAnd (fMem 0 4) (fKPairF 1 3 0))) (kpImg H x v) (fun u => ?_)
  rw [kpImg_spec H x v u]
  constructor
  · rintro ⟨b, hb, hk⟩
    exact ⟨b, hb,
      (fKPairF_spec H
        (scons b (scons u (scons y (scons x (fun _ => v))))) 1 3 0).mp hk⟩
  · rintro ⟨b, hb, hu⟩
    exact ⟨b, hb,
      (fKPairF_spec H
        (scons b (scons u (scons y (scons x (fun _ => v))))) 1 3 0).mpr hu⟩

theorem psiPImgF_functional (H : ZFAxioms mem) (v : V) :
    Functional (relOf mem psiPImgF (fun _ => v)) := by
  intro x y1 y2 h1 h2
  rw [psiPImgF_rel H v y1 x] at h1
  rw [psiPImgF_rel H v y2 x] at h2
  rw [h1, h2]

/-- `pairImg H v = { ⟨a, b⟩ : a, b ∈ v }`. -/
noncomputable def pairImg (H : ZFAxioms mem) (v : V) : V :=
  vunion H (H.repl psiPImgF (fun _ => v) (psiPImgF_functional H v) v).choose

theorem pairImg_spec (H : ZFAxioms mem) (v u : V) :
    mem u (pairImg H v) ↔ ∃ a b, mem a v ∧ mem b v ∧ u = kpair H a b := by
  unfold pairImg
  rw [vunion_spec H _ u]
  constructor
  · rintro ⟨t, hut, ht⟩
    obtain ⟨a, ha, hrel⟩ :=
      ((H.repl psiPImgF (fun _ => v) (psiPImgF_functional H v) v).choose_spec
        t).mp ht
    have hta : t = kpImg H a v := (psiPImgF_rel H v t a).mp hrel
    rw [hta] at hut
    obtain ⟨b, hb, hu⟩ := (kpImg_spec H a v u).mp hut
    exact ⟨a, b, ha, hb, hu⟩
  · rintro ⟨a, b, ha, hb, hu⟩
    refine ⟨kpImg H a v, (kpImg_spec H a v u).mpr ⟨b, hb, hu⟩, ?_⟩
    refine ((H.repl psiPImgF (fun _ => v) (psiPImgF_functional H v)
      v).choose_spec (kpImg H a v)).mpr ⟨a, ha, ?_⟩
    exact (psiPImgF_rel H v (kpImg H a v) a).mpr rfl

/-! ## One step of the pairing construction -/

/-- `pairStep H v = v ∪ { ⟨a, b⟩ : a, b ∈ v }`.  Inflationary and monotone, and
it adds the pair of any two members: those three facts are everything the
construction below uses. -/
noncomputable def pairStep (H : ZFAxioms mem) (v : V) : V :=
  vcup H v (pairImg H v)

theorem pairStep_spec (H : ZFAxioms mem) (v u : V) :
    mem u (pairStep H v) ↔
      (mem u v ∨ ∃ a b, mem a v ∧ mem b v ∧ u = kpair H a b) := by
  unfold pairStep
  rw [vcup_spec H v (pairImg H v) u, pairImg_spec H v u]

theorem pairStep_infl (H : ZFAxioms mem) (v : V) : Sub mem v (pairStep H v) :=
  fun x hx => (pairStep_spec H v x).mpr (Or.inl hx)

theorem pairStep_mono (H : ZFAxioms mem) {v v' : V} (h : Sub mem v v') :
    Sub mem (pairStep H v) (pairStep H v') := by
  intro x hx
  rcases (pairStep_spec H v x).mp hx with hx | ⟨a, b, ha, hb, hab⟩
  · exact (pairStep_spec H v' x).mpr (Or.inl (h x hx))
  · exact (pairStep_spec H v' x).mpr (Or.inr ⟨a, b, h a ha, h b hb, hab⟩)

theorem kpair_mem_pairStep (H : ZFAxioms mem) {v a b : V}
    (ha : mem a v) (hb : mem b v) : mem (kpair H a b) (pairStep H v) :=
  (pairStep_spec H v _).mpr (Or.inr ⟨a, b, ha, hb, rfl⟩)

/-- "slot `i` = `pairStep` (slot `j`)".

| de Bruijn slot | contents                             |
| -------------- | ------------------------------------ |
| `0`            | the candidate member `x`             |
| `1`            | the first component `a` (inner)      |
| `2`            | the second component `b` (innermost) |
| `m+1`          | the caller's slot `m`                |
-/
def fPairStepF (i j : Nat) : Form :=
  fSetByF i (fOr (fMem 0 (j+1))
    (fEx (fAnd (fMem 0 (j+2)) (fEx (fAnd (fMem 0 (j+3)) (fKPairF 2 1 0))))))

theorem fPairStepF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j : Nat) :
    Sat mem ee (fPairStepF i j) ↔ ee i = pairStep H (ee j) := by
  unfold fPairStepF
  refine fSetByF_spec H ee i _ (pairStep H (ee j)) (fun x => ?_)
  rw [pairStep_spec H (ee j) x]
  constructor
  · rintro (hx | ⟨a, ha, b, hb, hk⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨a, b, ha, hb,
        (fKPairF_spec H (scons b (scons a (scons x ee))) 2 1 0).mp hk⟩
  · rintro (hx | ⟨a, b, ha, hb, hk⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨a, ha, b, hb,
        (fKPairF_spec H (scons b (scons a (scons x ee))) 2 1 0).mpr hk⟩

/-- The graph of `pairStep`, as a relation formula in the two distinguished
slots.  It has no parameters, so its environment is irrelevant. -/
def psiStepF : Form := fPairStepF 0 1

theorem psiStepF_rel (H : ZFAxioms mem) (e : Nat → V) (u v : V) :
    relOf mem psiStepF e u v ↔ u = pairStep H v :=
  fPairStepF_spec H (scons u (scons v e)) 0 1

/-- A functional relation is set-like: the predecessors of `v` are contained in
the singleton of `pairStep H v`. -/
theorem psiStepF_setLike (H : ZFAxioms mem) (e : Nat → V) :
    SetLike mem (relOf mem psiStepF e) := by
  intro v
  exact ⟨vsingle H (pairStep H v), fun z hz =>
    (vsingle_spec H (pairStep H v) z).mpr ((psiStepF_rel H e z v).mp hz)⟩

/-- **The ambient set.**  Closure under a definable set-like relation, applied
to the graph of `pairStep` and the seed `{omegaV H}`.  Nothing is claimed about
which sets belong to `w`; only that the internal omega does and that `w` is
closed under the step. -/
theorem exists_pairStepClosed (H : ZFAxioms mem) :
    ∃ w, mem (omegaV H) w ∧ ∀ v, mem v w → mem (pairStep H v) w := by
  obtain ⟨w, hs, hcl⟩ :=
    ClosureFO_of_ZF H psiStepF (fun _ => vempty H)
      (psiStepF_setLike H (fun _ => vempty H)) (vsingle H (omegaV H))
  refine ⟨w, hs _ ((vsingle_spec H (omegaV H) (omegaV H)).mpr rfl),
    fun v hv => ?_⟩
  exact hcl (pairStep H v) v
    ((psiStepF_rel H (fun _ => vempty H) (pairStep H v) v).mpr rfl) hv

/-! ## The least step-closed set inside the ambient one

The elements of `w` are unconstrained, so the intersection presentation is used
again: `stepClosure H w` collects the elements of `w` that belong to every
step-closed set.  It is itself step-closed, hence least, and least is exactly
what an induction principle needs. -/

/-- A set contains the internal omega as a member and is closed under
`pairStep`. -/
def StepClosed (H : ZFAxioms mem) (D : V) : Prop :=
  mem (omegaV H) D ∧ ∀ v, mem v D → mem (pairStep H v) D

/-- "slot `c` is step-closed", with the internal omega supplied in slot `om`.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the member `v`, then its step |
| `m+1`          | the caller's slot `m`       |
-/
def fStepClosedF (c om : Nat) : Form :=
  fAnd (fMem om c)
    (fAll (fImp (fMem 0 (c+1)) (fEx (fAnd (fPairStepF 0 1) (fMem 0 (c+2))))))

theorem fStepClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (c om : Nat)
    (hom : ee om = omegaV H) :
    Sat mem ee (fStepClosedF c om) ↔ StepClosed H (ee c) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← hom]; exact h1, fun v hv => ?_⟩
    obtain ⟨z, hz, hzc⟩ := h2 v hv
    have hz' : z = pairStep H v :=
      (fPairStepF_spec H (scons z (scons v ee)) 0 1).mp hz
    rw [← hz']
    exact hzc
  · rintro ⟨h1, h2⟩
    refine ⟨show mem (ee om) (ee c) by rw [hom]; exact h1, fun v hv => ?_⟩
    exact ⟨pairStep H v,
      (fPairStepF_spec H (scons (pairStep H v) (scons v ee)) 0 1).mpr rfl,
      h2 v hv⟩

/-- The elements of `w` that lie in every step-closed set. -/
noncomputable def stepClosure (H : ZFAxioms mem) (w : V) : V :=
  sepD H (fAll (fImp (fStepClosedF 0 2) (fMem 1 0))) (fun _ => omegaV H) w

theorem stepClosure_spec (H : ZFAxioms mem) (w p : V) :
    mem p (stepClosure H w) ↔
      (mem p w ∧ ∀ D, StepClosed H D → mem p D) := by
  unfold stepClosure
  rw [sepD_spec H (fAll (fImp (fStepClosedF 0 2) (fMem 1 0)))
      (fun _ => omegaV H) w p]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun D hD => ?_⟩
    exact h D ((fStepClosedF_spec H
      (scons D (scons p (fun _ => omegaV H))) 0 2 rfl).mpr hD)
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun D hD => ?_⟩
    exact h D ((fStepClosedF_spec H
      (scons D (scons p (fun _ => omegaV H))) 0 2 rfl).mp hD)

theorem omega_mem_stepClosure (H : ZFAxioms mem) {w : V}
    (hw : mem (omegaV H) w) : mem (omegaV H) (stepClosure H w) :=
  (stepClosure_spec H w (omegaV H)).mpr ⟨hw, fun _ hD => hD.1⟩

theorem stepClosure_step (H : ZFAxioms mem) {w : V}
    (hstep : ∀ v, mem v w → mem (pairStep H v) w)
    {p : V} (hp : mem p (stepClosure H w)) :
    mem (pairStep H p) (stepClosure H w) := by
  obtain ⟨hpw, hall⟩ := (stepClosure_spec H w p).mp hp
  exact (stepClosure_spec H w (pairStep H p)).mpr
    ⟨hstep p hpw, fun D hD => hD.2 p (hall D hD)⟩

/-- **Induction along the step.**  A definable property that holds of the
internal omega and is preserved by `pairStep` holds of every element of
`stepClosure H w`, because the subset it carves out is again step-closed.  The
step hypothesis may use that its argument is already in the closure. -/
theorem stepClosure_ind (H : ZFAxioms mem) {w : V}
    (hw : mem (omegaV H) w) (hstep : ∀ v, mem v w → mem (pairStep H v) w)
    (P : V → Prop) (phi : Form) (e : Nat → V)
    (hdef : ∀ y, P y ↔ Sat mem (scons y e) phi)
    (hbase : P (omegaV H))
    (hind : ∀ v, mem v (stepClosure H w) → P v → P (pairStep H v)) :
    ∀ p, mem p (stepClosure H w) → P p := by
  intro p hp
  have hD : ∀ y, mem y (sepD H phi e (stepClosure H w)) ↔
      (mem y (stepClosure H w) ∧ P y) := by
    intro y
    rw [sepD_spec H phi e (stepClosure H w) y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hdef y).mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hdef y).mp h2⟩
  have hclosed : StepClosed H (sepD H phi e (stepClosure H w)) := by
    refine ⟨(hD _).mpr ⟨omega_mem_stepClosure H hw, hbase⟩, fun v hv => ?_⟩
    obtain ⟨hvK, hvP⟩ := (hD v).mp hv
    exact (hD _).mpr ⟨stepClosure_step H hstep hvK, hind v hvK hvP⟩
  exact ((hD p).mp (((stepClosure_spec H w p).mp hp).2 _ hclosed)).2

/-- Every element of the closure includes the internal omega: the seed does,
and `pairStep` is inflationary. -/
theorem stepClosure_omega_sub (H : ZFAxioms mem) {w : V}
    (hw : mem (omegaV H) w) (hstep : ∀ v, mem v w → mem (pairStep H v) w) :
    ∀ p, mem p (stepClosure H w) → Sub mem (omegaV H) p := by
  refine stepClosure_ind H hw hstep (fun p => Sub mem (omegaV H) p)
    (fAll (fImp (fMem 0 2) (fMem 0 1))) (fun _ => omegaV H)
    (fun _ => Iff.rfl) (fun _ hx => hx) (fun v _ hv => ?_)
  exact fun x hx => pairStep_infl H v x (hv x hx)

/-- **Directedness.**  Any two elements of the closure lie below a common
element of it.  This is the property the ambient `w` cannot supply and the one
that makes the union pairing-closed: the induction step replaces a bound `q`
for the smaller pair by `pairStep H q`, which dominates the stepped element by
monotonicity and the other by inflationarity. -/
theorem stepClosure_directed (H : ZFAxioms mem) {w : V}
    (hw : mem (omegaV H) w) (hstep : ∀ v, mem v w → mem (pairStep H v) w) :
    ∀ p, mem p (stepClosure H w) → ∀ p', mem p' (stepClosure H w) →
      ∃ q, mem q (stepClosure H w) ∧ Sub mem p q ∧ Sub mem p' q := by
  refine stepClosure_ind H hw hstep
    (fun p => ∀ p', mem p' (stepClosure H w) →
      ∃ q, mem q (stepClosure H w) ∧ Sub mem p q ∧ Sub mem p' q)
    (fAll (fImp (fMem 0 2)
      (fEx (fAnd (fMem 0 3)
        (fAnd (fAll (fImp (fMem 0 3) (fMem 0 1)))
              (fAll (fImp (fMem 0 2) (fMem 0 1))))))))
    (fun _ => stepClosure H w) (fun _ => Iff.rfl) ?_ ?_
  · intro p' hp'
    exact ⟨p', hp', stepClosure_omega_sub H hw hstep p' hp', fun _ hx => hx⟩
  · intro v _ IH p' hp'
    obtain ⟨q, hq, hvq, hp'q⟩ := IH p' hp'
    exact ⟨pairStep H q, stepClosure_step H hstep hq, pairStep_mono H hvq,
      fun x hx => pairStep_infl H q x (hp'q x hx)⟩

/-! ## The pairing-closed superset, and the formula-closed set -/

/-- **A pairing-closed superset of the internal omega exists.**  It is the
union of the least step-closed set: the internal omega is one of its elements,
and two members come from two elements, hence from a common one by
directedness, so their pair lies in the step of that element. -/
theorem exists_pairClosed (H : ZFAxioms mem) :
    ∃ C, Sub mem (omegaV H) C ∧
      ∀ a b, mem a C → mem b C → mem (kpair H a b) C := by
  obtain ⟨w, hw, hstep⟩ := exists_pairStepClosed H
  refine ⟨vunion H (stepClosure H w), ?_, ?_⟩
  · intro x hx
    exact (vunion_spec H (stepClosure H w) x).mpr
      ⟨omegaV H, hx, omega_mem_stepClosure H hw⟩
  · intro a b ha hb
    obtain ⟨p, hap, hp⟩ := (vunion_spec H (stepClosure H w) a).mp ha
    obtain ⟨p', hbp', hp'⟩ := (vunion_spec H (stepClosure H w) b).mp hb
    obtain ⟨q, hq, hpq, hp'q⟩ := stepClosure_directed H hw hstep p hp p' hp'
    exact (vunion_spec H (stepClosure H w) (kpair H a b)).mpr
      ⟨pairStep H q, kpair_mem_pairStep H (hpq a hap) (hp'q b hbp'),
       stepClosure_step H hstep hq⟩

/-- **Every model of the ZF axioms has a formula-closed set.**  This discharges
the hypothesis carried by both induction principles of
`BoundedZFCConsistency.CodePredicate`, and with it the last obstacle to reading
`IsFormCodeSem` as a genuine predicate: the intersection defining it is now
taken over a nonempty class, so it is not vacuously universal. -/
theorem exists_formulaClosed (H : ZFAxioms mem) : ∃ C, FormulaClosed H C := by
  obtain ⟨C, hom, hpair⟩ := exists_pairClosed H
  exact ⟨C, formulaClosed_of_pairClosed H hom hpair⟩

/-! ## The induction principles, unconditionally

The two principles of `CodePredicate` are restated with their existence
hypothesis discharged.  Nothing else changes: the definability hypothesis
remains, because Separation carves out subsets by a `Form` with parameters and
not by an arbitrary Lean predicate. -/

/-- **Induction on formula codes, as a definable schema**, with no hypothesis
beyond definability of the property. -/
theorem isFormCodeSem_ind_form' (H : ZFAxioms mem) (phi : Form) (e : Nat → V)
    (hMemAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      Sat mem (scons (kpair H (natV H 0) (kpair H a b)) e) phi)
    (hEqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      Sat mem (scons (kpair H (natV H 1) (kpair H a b)) e) phi)
    (hBot : Sat mem (scons (kpair H (natV H 2) (vempty H)) e) phi)
    (hImp : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 3) (kpair H a b)) e) phi)
    (hAnd : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 4) (kpair H a b)) e) phi)
    (hOr : ∀ a b, Sat mem (scons a e) phi → Sat mem (scons b e) phi →
      Sat mem (scons (kpair H (natV H 5) (kpair H a b)) e) phi)
    (hAll : ∀ a, Sat mem (scons a e) phi →
      Sat mem (scons (kpair H (natV H 6) a) e) phi)
    (hEx : ∀ a, Sat mem (scons a e) phi →
      Sat mem (scons (kpair H (natV H 7) a) e) phi) :
    ∀ x, IsFormCodeSem H x → Sat mem (scons x e) phi := by
  obtain ⟨C0, hC0⟩ := exists_formulaClosed H
  exact isFormCodeSem_ind_form H phi e hC0 hMemAtom hEqAtom hBot hImp hAnd hOr
    hAll hEx

/-- **Induction on formula codes** for a `Prop`-valued predicate presented with
a witness of its definability, with no hypothesis beyond that witness. -/
theorem isFormCodeSem_ind' (H : ZFAxioms mem) (P : V → Prop)
    (phi : Form) (e : Nat → V)
    (hdef : ∀ y, P y ↔ Sat mem (scons y e) phi)
    (hMemAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 0) (kpair H a b)))
    (hEqAtom : ∀ a b, mem a (omegaV H) → mem b (omegaV H) →
      P (kpair H (natV H 1) (kpair H a b)))
    (hBot : P (kpair H (natV H 2) (vempty H)))
    (hImp : ∀ a b, P a → P b → P (kpair H (natV H 3) (kpair H a b)))
    (hAnd : ∀ a b, P a → P b → P (kpair H (natV H 4) (kpair H a b)))
    (hOr : ∀ a b, P a → P b → P (kpair H (natV H 5) (kpair H a b)))
    (hAll : ∀ a, P a → P (kpair H (natV H 6) a))
    (hEx : ∀ a, P a → P (kpair H (natV H 7) a)) :
    ∀ x, IsFormCodeSem H x → P x := by
  obtain ⟨C0, hC0⟩ := exists_formulaClosed H
  exact isFormCodeSem_ind H P phi e hdef hC0 hMemAtom hEqAtom hBot hImp hAnd hOr
    hAll hEx

end FormulaClosedSet

end BoundedZFCConsistency
end LeanProofs
