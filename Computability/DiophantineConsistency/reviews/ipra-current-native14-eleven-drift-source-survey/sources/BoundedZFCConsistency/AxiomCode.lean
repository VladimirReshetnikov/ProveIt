import BoundedZFCConsistency.CodedRank

/-!
# Codes of the ZFC axioms, and the sentence `Con_n(ZFC)`

`BoundedZFCConsistency.CodedRank` assembles a bounded-consistency sentence over
the *empty* context, `logicConForm n`, and says so: what it expresses is bounded
consistency of pure first-order logic, and it is provable outright from internal
soundness.  The gap between it and the target is exactly one missing predicate —
"codes a ZFC axiom" — because `Con_n(ZFC)` quantifies over coded derivations
whose context consists of codes of ZFC axioms.

This file supplies that predicate and writes the real sentence.

**How `conZFCForm n` differs from `logicConForm n`.**  Both say "no coded
derivation of the falsity code is bounded, at every occurrence, by the numeral of
`n`".  `logicConForm n` pins the derivation's context to `ctxNil`, so it rules
out only derivations from no assumptions.  `conZFCForm n` instead quantifies over
*every* context code `g` and requires each member of `g` to satisfy the internal
axiom-code predicate.  The empty context satisfies that requirement vacuously, so
`conZFCForm n` implies `logicConForm n`; the converse fails, and the extra
content is precisely the content of bounded consistency of ZFC.  Nothing here
proves `conZFCForm n`; what is proved is its arbitrary-model characterization and
its reduction, through Gödel completeness, to a single semantic obligation.

Neither Powerset nor Regularity is used.

## The schema renamings, internally

`ZF.Zf` places a schema's formula under fresh binders by renaming it along one of
four external index maps, `rsep`, `rf1`, `rf2`, `ri`.  All four have the same
shape: two explicit initial values followed by a constant shift.  Writing

```text
twoMapN a0 a1 k  =  0 ↦ a0,  1 ↦ a1,  n+2 ↦ n+k
```

one has `rsep = twoMapN 0 3 4`, `rf1 = twoMapN 1 2 3`, `rf2 = twoMapN 0 2 3` and
`ri = twoMapN 1 0 4`, so a single internal construction

```text
twoMapV H a0 a1 k  =  econs a0 (econs a1 (succVals^k idMap))
```

covers all four.  It is a variable map, it computes the external map on numerals,
and it is the *unique* variable map with its three defining equations — which is
what makes it describable by a `Form` even though it is a model-dependent set.

## Template codes

The code of a schema instance is the code of a fixed formula with one — or, for
Replacement, three — subcodes plugged in.  Rather than assemble each such code by
a chain of ten or twenty existentials, the plugging is made a primitive.

A **template** is an ordinary `Form` in which the self-membership atom `fMem k k`
is read as a marker for the `k`-th plugged code.  No axiom of ZF or ZFC contains
a self-membership atom, so `markerFree` holds of all of them and the template
reading agrees with `formCode` there.  `tmplCode H sub t` is the code of the
template `t` with `sub k` at marker `k`, and `fTmplCodeF q i t` is its
object-language rendering, with `q k` the slot holding `sub k`.  One recursion
and one satisfaction spec then serve every schema, and the assembled formulas
below need only name the renamed subcodes.

The Separation and Replacement skeletons are `SepSkel` and `ReplSkel`, and
`sepCodeV`/`replCodeV` are the resulting internal constructors:

```text
sepCodeV  H p = tmplCode H (fun _ => renameV H (rsepV H) p) SepSkel
replCodeV H p = tmplCode H (replSubV (renameV H (rf1V H) p)
                                     (renameV H (rf2V H) p)
                                     (renameV H (riV  H) p)) ReplSkel
```

Both agree with quotation — `sepCodeV H (formCode H phi) = formCode H
(Sep_form phi)` — and both preserve codehood.

## The axiom-code predicate is properly larger than the quotations

`IsZFCAxiomCode H c` recognizes the seven fixed axioms by equality with their
quotations and the two schemas by an existential over a formula *code*.  Only one
direction of agreement with the external axiom set is available:

```text
ZFCax f  →  IsZFCAxiomCode H (formCode H f)
```

The converse is **false** in nonstandard models and is deliberately not
attempted.  The existential ranges over the internal code predicate, which — as
`BoundedZFCConsistency.CodePredicate` records — has code-like elements that quote
no external formula, since its atomic clauses quantify over the model's own
omega.  A nonstandard `p` yields an internal Separation instance code that is not
the quotation of any external Separation instance, so the internal axiom set is
properly larger than the image of the external one.  That is the intended
behaviour: the eventual argument runs *inside* the model, where the larger set is
what internal soundness has to be applied to, and a sentence that quantified only
over quotations would not be expressible as a `Form` at all.

## De Bruijn bookkeeping

Every macro carries a table of the slots it introduces.  Slot arguments named
`_i` are ABSOLUTE positions at the use site; each binder shifts the caller's
slots by one and the call sites account for the shift explicitly.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

/- The assembled formulas of this file are large terms, and the elaborator
recurses through them when it checks a definitional unfolding. -/
set_option maxRecDepth 8000

/- `sealF g` is `closeN (bound g) g`, so reducing it evaluates `bound` over the
whole of the formula being closed.  Nothing here needs to see through the closure
operator, and every fact used about it is stated for an arbitrary formula. -/
attribute [local irreducible] SetTheory.sealF

universe u

section AxiomCode

variable {V : Type u} {mem : V → V → Prop}

/-! ## Iterated internal successor

The four schema renamings shift by three or four, so the internal maps and their
object-language descriptions need a `k`-fold successor with `k` external. -/

/-- The `k`-fold internal successor of `x`, with `k` a metatheoretic natural. -/
noncomputable def vsuccIter (H : ZFAxioms mem) : Nat → V → V
  | 0, x => x
  | k+1, x => vsucc H (vsuccIter H k x)

theorem vsuccIter_zero (H : ZFAxioms mem) (x : V) : vsuccIter H 0 x = x := rfl

theorem vsuccIter_succ (H : ZFAxioms mem) (k : Nat) (x : V) :
    vsuccIter H (k+1) x = vsucc H (vsuccIter H k x) := rfl

theorem vsuccIter_mem_omega (H : ZFAxioms mem) (k : Nat) {n : V}
    (hn : mem n (omegaV H)) : mem (vsuccIter H k n) (omegaV H) := by
  induction k with
  | zero => exact hn
  | succ k ih => exact omega_succ H _ ih

/-- On numerals the iterated successor is external addition. -/
theorem vsuccIter_natV (H : ZFAxioms mem) (k m : Nat) :
    vsuccIter H k (natV H m) = natV H (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih => show vsucc H (vsuccIter H k (natV H m)) = natV H (m + k + 1)
                 rw [ih, natV_succ]

/-- "slot `i` is the `k`-fold successor of slot `j`".

| de Bruijn slot | contents                       |
| -------------- | ------------------------------ |
| `0`            | the `(k-1)`-fold successor     |
| `m+1`          | the caller's slot `m`          |
-/
def fSuccIterF : Nat → Nat → Nat → Form
  | i, j, 0 => fEq i j
  | i, j, k+1 => fEx (fAnd (fSuccIterF 0 (j+1) k) (fSuccF (i+1) 0))

theorem fSuccIterF_spec (H : ZFAxioms mem) :
    ∀ (k i j : Nat) (ee : Nat → V),
      Sat mem ee (fSuccIterF i j k) ↔ ee i = vsuccIter H k (ee j) := by
  intro k
  induction k with
  | zero => intro i j ee; exact Iff.rfl
  | succ k ih =>
      intro i j ee
      constructor
      · rintro ⟨d, hd, hs⟩
        have hd' : d = vsuccIter H k (ee j) := (ih 0 (j+1) (scons d ee)).mp hd
        have hs' : ee i = vsucc H d := (fSuccF_spec H (scons d ee) (i+1) 0).mp hs
        rw [hs', hd', vsuccIter_succ]
      · intro h
        refine ⟨vsuccIter H k (ee j), (ih 0 (j+1) _).mpr rfl, ?_⟩
        exact (fSuccF_spec H (scons (vsuccIter H k (ee j)) ee) (i+1) 0).mpr h

/-! ## Iterated successor of a variable map -/

/-- The `k`-fold pointwise successor of a variable map. -/
noncomputable def succIterVals (H : ZFAxioms mem) : Nat → V → V
  | 0, r => r
  | k+1, r => succVals H (succIterVals H k r)

theorem succIterVals_isVarMap (H : ZFAxioms mem) (k : Nat) {r : V}
    (hr : IsVarMap H r) : IsVarMap H (succIterVals H k r) := by
  induction k with
  | zero => exact hr
  | succ k ih => exact succVals_isVarMap H ih

theorem succIterVals_apply (H : ZFAxioms mem) (k : Nat) {r : V}
    (hr : IsVarMap H r) {n : V} (hn : mem n (omegaV H)) :
    applyV H (succIterVals H k r) n = vsuccIter H k (applyV H r n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show applyV H (succVals H (succIterVals H k r)) n = _
      rw [succVals_apply H (succIterVals_isVarMap H k hr) hn, ih]
      rfl

/-! ## The two-value shift maps

All four schema renamings are of the form "two explicit initial values, then a
constant shift", so one construction covers them.  The internal map is built
from `econs`, the iterated pointwise successor and the identity map. -/

/-- The external index map `0 ↦ a0`, `1 ↦ a1`, `n+2 ↦ n+k`. -/
def twoMapN (a0 a1 k : Nat) : Nat → Nat
  | 0 => a0
  | 1 => a1
  | n+2 => n + k

/-- The internal counterpart of `twoMapN a0 a1 k`. -/
noncomputable def twoMapV (H : ZFAxioms mem) (a0 a1 k : Nat) : V :=
  econs H (natV H a0) (econs H (natV H a1) (succIterVals H k (idMap H)))

/-- The tail of `twoMapV`, named because every application equation goes through
it. -/
noncomputable def twoMapTailV (H : ZFAxioms mem) (a1 k : Nat) : V :=
  econs H (natV H a1) (succIterVals H k (idMap H))

theorem twoMapTailV_isVarMap (H : ZFAxioms mem) (a1 k : Nat) :
    IsVarMap H (twoMapTailV H a1 k) :=
  econs_isEnvOn H (succIterVals_isVarMap H k (idMap_isVarMap H))
    (natV_mem_omega H a1)

theorem twoMapV_eq (H : ZFAxioms mem) (a0 a1 k : Nat) :
    twoMapV H a0 a1 k = econs H (natV H a0) (twoMapTailV H a1 k) := rfl

theorem twoMapV_isVarMap (H : ZFAxioms mem) (a0 a1 k : Nat) :
    IsVarMap H (twoMapV H a0 a1 k) :=
  econs_isEnvOn H (twoMapTailV_isVarMap H a1 k) (natV_mem_omega H a0)

theorem twoMapV_zero (H : ZFAxioms mem) (a0 a1 k : Nat) :
    applyV H (twoMapV H a0 a1 k) (vempty H) = natV H a0 :=
  econs_zero H (twoMapTailV_isVarMap H a1 k).1.1 (natV H a0)

theorem twoMapV_one (H : ZFAxioms mem) (a0 a1 k : Nat) :
    applyV H (twoMapV H a0 a1 k) (vsucc H (vempty H)) = natV H a1 := by
  rw [twoMapV_eq,
    econs_succ H (twoMapTailV_isVarMap H a1 k) (natV H a0) (vempty_in_omega H)]
  exact econs_zero H (succIterVals_isVarMap H k (idMap_isVarMap H)).1.1 _

theorem twoMapV_succ_succ (H : ZFAxioms mem) (a0 a1 k : Nat) {n : V}
    (hn : mem n (omegaV H)) :
    applyV H (twoMapV H a0 a1 k) (vsucc H (vsucc H n)) = vsuccIter H k n := by
  rw [twoMapV_eq,
    econs_succ H (twoMapTailV_isVarMap H a1 k) (natV H a0) (omega_succ H n hn),
    twoMapTailV,
    econs_succ H (succIterVals_isVarMap H k (idMap_isVarMap H)) (natV H a1) hn,
    succIterVals_apply H k (idMap_isVarMap H) hn, idMap_apply H hn]

/-- **The internal map computes the external one on numerals.** -/
theorem twoMapV_agreesWith (H : ZFAxioms mem) (a0 a1 k : Nat) :
    AgreesWith H (twoMapV H a0 a1 k) (twoMapN a0 a1 k) := by
  intro m
  match m with
  | 0 => exact twoMapV_zero H a0 a1 k
  | 1 => exact twoMapV_one H a0 a1 k
  | j+2 =>
      show applyV H (twoMapV H a0 a1 k) (vsucc H (vsucc H (natV H j)))
        = natV H (j + k)
      rw [twoMapV_succ_succ H a0 a1 k (natV_mem_omega H j), vsuccIter_natV]

/-! ### The defining equations, and uniqueness

The internal map is a model-dependent set, so a `Form` cannot name it; it has to
be *described*.  Three graph conditions suffice, because a variable map is an
internal function on the internal omega and every internal natural is zero, one,
or a double successor. -/

/-- The three defining graph conditions of `twoMapV H a0 a1 k`. -/
def IsTwoMap (H : ZFAxioms mem) (r : V) (a0 a1 k : Nat) : Prop :=
  IsVarMap H r ∧
    mem (kpair H (natV H 0) (natV H a0)) r ∧
    mem (kpair H (natV H 1) (natV H a1)) r ∧
    ∀ n, mem n (omegaV H) →
      mem (kpair H (vsuccIter H 2 n) (vsuccIter H k n)) r

theorem isTwoMap_twoMapV (H : ZFAxioms mem) (a0 a1 k : Nat) :
    IsTwoMap H (twoMapV H a0 a1 k) a0 a1 k := by
  refine ⟨twoMapV_isVarMap H a0 a1 k, ?_, ?_, ?_⟩
  · have h := isVarMap_mem H (twoMapV_isVarMap H a0 a1 k)
      (natV_mem_omega H (0 : Nat))
    rw [show natV H (0 : Nat) = vempty H from rfl, twoMapV_zero] at h
    exact h
  · have h := isVarMap_mem H (twoMapV_isVarMap H a0 a1 k)
      (natV_mem_omega H (1 : Nat))
    rw [show natV H (1 : Nat) = vsucc H (vempty H) from rfl, twoMapV_one] at h
    exact h
  · intro n hn
    have h := isVarMap_mem H (twoMapV_isVarMap H a0 a1 k)
      (omega_succ H _ (omega_succ H n hn))
    rw [twoMapV_succ_succ H a0 a1 k hn] at h
    exact h

/-- **The description is exact.**  Uniqueness is internal function
extensionality together with two applications of "zero or successor". -/
theorem isTwoMap_unique (H : ZFAxioms mem) {r : V} {a0 a1 k : Nat}
    (h : IsTwoMap H r a0 a1 k) : r = twoMapV H a0 a1 k := by
  obtain ⟨hv, h0, h1, hs⟩ := h
  refine funOn_ext H hv.1 (twoMapV_isVarMap H a0 a1 k).1 (fun x hx => ?_)
  rcases nat_zero_or_succ H x hx with rfl | ⟨m, hm, rfl⟩
  · rw [twoMapV_zero]
    exact applyV_eq H hv.1.1 h0
  · rcases nat_zero_or_succ H m hm with rfl | ⟨n, hn, rfl⟩
    · rw [twoMapV_one]
      exact applyV_eq H hv.1.1 h1
    · rw [twoMapV_succ_succ H a0 a1 k hn]
      exact applyV_eq H hv.1.1 (hs n hn)

theorem isTwoMap_iff (H : ZFAxioms mem) (r : V) (a0 a1 k : Nat) :
    IsTwoMap H r a0 a1 k ↔ r = twoMapV H a0 a1 k :=
  ⟨isTwoMap_unique H, fun h => by rw [h]; exact isTwoMap_twoMapV H a0 a1 k⟩

/-- "slot `r_i` is the internal map `0 ↦ a0`, `1 ↦ a1`, `n+2 ↦ n+k`".

| de Bruijn slot | contents                                     |
| -------------- | -------------------------------------------- |
| `0`            | the value, then the double successor's value |
| `1`            | the index, then the double successor         |
| `2`            | the internal natural `n`, in the last clause |
| `m+2`, `m+3`   | the caller's slot `m`                        |
-/
def fTwoMapF (r_i a0 a1 k : Nat) : Form :=
  fAnd (fVarMapF r_i)
    (fAnd (fEx (fEx (fAnd (fNumF 1 0)
            (fAnd (fNumF 0 a0) (fPairMemF 1 0 (r_i+2))))))
      (fAnd (fEx (fEx (fAnd (fNumF 1 1)
              (fAnd (fNumF 0 a1) (fPairMemF 1 0 (r_i+2))))))
        (fAll (fImp (fNatF 0)
          (fEx (fEx (fAnd (fSuccIterF 1 2 2)
            (fAnd (fSuccIterF 0 2 k) (fPairMemF 1 0 (r_i+3))))))))))

theorem fTwoMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i a0 a1 k : Nat) :
    Sat mem ee (fTwoMapF r_i a0 a1 k) ↔ IsTwoMap H (ee r_i) a0 a1 k := by
  unfold IsTwoMap
  constructor
  · rintro ⟨hv, ⟨x, y, hx1, hx2, hx3⟩, ⟨u, w, hu1, hu2, hu3⟩, hlast⟩
    refine ⟨(fVarMapF_spec H ee r_i).mp hv, ?_, ?_, ?_⟩
    · have e1 : x = natV H 0 := (fNumF_spec H 0 1 (scons y (scons x ee))).mp hx1
      have e2 : y = natV H a0 :=
        (fNumF_spec H a0 0 (scons y (scons x ee))).mp hx2
      have e3 := (fPairMemF_spec H (scons y (scons x ee)) 1 0 (r_i+2)).mp hx3
      rw [e1, e2] at e3
      exact e3
    · have e1 : u = natV H 1 := (fNumF_spec H 1 1 (scons w (scons u ee))).mp hu1
      have e2 : w = natV H a1 :=
        (fNumF_spec H a1 0 (scons w (scons u ee))).mp hu2
      have e3 := (fPairMemF_spec H (scons w (scons u ee)) 1 0 (r_i+2)).mp hu3
      rw [e1, e2] at e3
      exact e3
    · intro n hn
      obtain ⟨x', y', hx', hy', hp'⟩ :=
        hlast n ((fNatF_spec H (scons n ee) 0).mpr hn)
      have e1 : x' = vsuccIter H 2 n :=
        (fSuccIterF_spec H 2 1 2 (scons y' (scons x' (scons n ee)))).mp hx'
      have e2 : y' = vsuccIter H k n :=
        (fSuccIterF_spec H k 0 2 (scons y' (scons x' (scons n ee)))).mp hy'
      have e3 :=
        (fPairMemF_spec H (scons y' (scons x' (scons n ee))) 1 0 (r_i+3)).mp hp'
      rw [e1, e2] at e3
      exact e3
  · rintro ⟨hv, h0, h1, hs⟩
    refine ⟨(fVarMapF_spec H ee r_i).mpr hv, ⟨natV H 0, natV H a0, ?_, ?_, ?_⟩,
      ⟨natV H 1, natV H a1, ?_, ?_, ?_⟩, ?_⟩
    · exact (fNumF_spec H 0 1 _).mpr rfl
    · exact (fNumF_spec H a0 0 _).mpr rfl
    · exact (fPairMemF_spec H _ 1 0 (r_i+2)).mpr h0
    · exact (fNumF_spec H 1 1 _).mpr rfl
    · exact (fNumF_spec H a1 0 _).mpr rfl
    · exact (fPairMemF_spec H _ 1 0 (r_i+2)).mpr h1
    · intro n hn
      have hn' : mem n (omegaV H) := (fNatF_spec H (scons n ee) 0).mp hn
      refine ⟨vsuccIter H 2 n, vsuccIter H k n, ?_, ?_, ?_⟩
      · exact (fSuccIterF_spec H 2 1 2 _).mpr rfl
      · exact (fSuccIterF_spec H k 0 2 _).mpr rfl
      · exact (fPairMemF_spec H _ 1 0 (r_i+3)).mpr (hs n hn')

/-! ## The four schema renamings, internally

`rsep`, `rf1`, `rf2` and `ri` of `ZF.Zf` are all instances of `twoMapN`, so their
internal counterparts are instances of `twoMapV` and inherit everything above,
including the object-language description. -/

theorem rsep_eq : rsep = twoMapN 0 3 4 := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

theorem rf1_eq : rf1 = twoMapN 1 2 3 := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

theorem rf2_eq : rf2 = twoMapN 0 2 3 := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

theorem ri_eq : ri = twoMapN 1 0 4 := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | j+2 => rfl

/-- The internal counterpart of the Separation renaming `rsep`. -/
noncomputable def rsepV (H : ZFAxioms mem) : V := twoMapV H 0 3 4

/-- The internal counterpart of the first functionality renaming `rf1`. -/
noncomputable def rf1V (H : ZFAxioms mem) : V := twoMapV H 1 2 3

/-- The internal counterpart of the second functionality renaming `rf2`. -/
noncomputable def rf2V (H : ZFAxioms mem) : V := twoMapV H 0 2 3

/-- The internal counterpart of the image renaming `ri`. -/
noncomputable def riV (H : ZFAxioms mem) : V := twoMapV H 1 0 4

theorem rsepV_isVarMap (H : ZFAxioms mem) : IsVarMap H (rsepV H) :=
  twoMapV_isVarMap H 0 3 4

theorem rf1V_isVarMap (H : ZFAxioms mem) : IsVarMap H (rf1V H) :=
  twoMapV_isVarMap H 1 2 3

theorem rf2V_isVarMap (H : ZFAxioms mem) : IsVarMap H (rf2V H) :=
  twoMapV_isVarMap H 0 2 3

theorem riV_isVarMap (H : ZFAxioms mem) : IsVarMap H (riV H) :=
  twoMapV_isVarMap H 1 0 4

theorem rsepV_agreesWith (H : ZFAxioms mem) : AgreesWith H (rsepV H) rsep := by
  rw [rsep_eq]; exact twoMapV_agreesWith H 0 3 4

theorem rf1V_agreesWith (H : ZFAxioms mem) : AgreesWith H (rf1V H) rf1 := by
  rw [rf1_eq]; exact twoMapV_agreesWith H 1 2 3

theorem rf2V_agreesWith (H : ZFAxioms mem) : AgreesWith H (rf2V H) rf2 := by
  rw [rf2_eq]; exact twoMapV_agreesWith H 0 2 3

theorem riV_agreesWith (H : ZFAxioms mem) : AgreesWith H (riV H) ri := by
  rw [ri_eq]; exact twoMapV_agreesWith H 1 0 4

/-! ### Agreement with quotation

Internal renaming along each of the four maps sends the code of an external
formula to the code of its external renaming. -/

theorem renameV_rsepV_formCode (H : ZFAxioms mem) (phi : Form) :
    renameV H (rsepV H) (formCode H phi) = formCode H (rename rsep phi) :=
  renameV_formCode H rsep (rsepV_isVarMap H) (rsepV_agreesWith H) phi

theorem renameV_rf1V_formCode (H : ZFAxioms mem) (phi : Form) :
    renameV H (rf1V H) (formCode H phi) = formCode H (rename rf1 phi) :=
  renameV_formCode H rf1 (rf1V_isVarMap H) (rf1V_agreesWith H) phi

theorem renameV_rf2V_formCode (H : ZFAxioms mem) (phi : Form) :
    renameV H (rf2V H) (formCode H phi) = formCode H (rename rf2 phi) :=
  renameV_formCode H rf2 (rf2V_isVarMap H) (rf2V_agreesWith H) phi

theorem renameV_riV_formCode (H : ZFAxioms mem) (phi : Form) :
    renameV H (riV H) (formCode H phi) = formCode H (rename ri phi) :=
  renameV_formCode H ri (riV_isVarMap H) (riV_agreesWith H) phi

/-! ### The four maps as `Form`s -/

/-- "slot `r_i` is the internal Separation renaming". -/
def fRsepMapF (r_i : Nat) : Form := fTwoMapF r_i 0 3 4

/-- "slot `r_i` is the internal first functionality renaming". -/
def fRf1MapF (r_i : Nat) : Form := fTwoMapF r_i 1 2 3

/-- "slot `r_i` is the internal second functionality renaming". -/
def fRf2MapF (r_i : Nat) : Form := fTwoMapF r_i 0 2 3

/-- "slot `r_i` is the internal image renaming". -/
def fRiMapF (r_i : Nat) : Form := fTwoMapF r_i 1 0 4

theorem fRsepMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fRsepMapF r_i) ↔ ee r_i = rsepV H :=
  (fTwoMapF_spec H ee r_i 0 3 4).trans (isTwoMap_iff H (ee r_i) 0 3 4)

theorem fRf1MapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fRf1MapF r_i) ↔ ee r_i = rf1V H :=
  (fTwoMapF_spec H ee r_i 1 2 3).trans (isTwoMap_iff H (ee r_i) 1 2 3)

theorem fRf2MapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fRf2MapF r_i) ↔ ee r_i = rf2V H :=
  (fTwoMapF_spec H ee r_i 0 2 3).trans (isTwoMap_iff H (ee r_i) 0 2 3)

theorem fRiMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (r_i : Nat) :
    Sat mem ee (fRiMapF r_i) ↔ ee r_i = riV H :=
  (fTwoMapF_spec H ee r_i 1 0 4).trans (isTwoMap_iff H (ee r_i) 1 0 4)

/-! ## Template codes

A template is a `Form` whose self-membership atoms `fMem k k` are markers for
plugged-in codes.  No ZF or ZFC axiom contains such an atom, so on the axioms the
template code is the ordinary code. -/

/-- The code of a template, with `sub k` plugged in at the marker `fMem k k`. -/
noncomputable def tmplCode (H : ZFAxioms mem) (sub : Nat → V) : Form → V
  | fMem i j =>
      if i = j then sub i else kpair H (natV H 0) (kpair H (natV H i) (natV H j))
  | fEq i j => kpair H (natV H 1) (kpair H (natV H i) (natV H j))
  | fBot => kpair H (natV H 2) (vempty H)
  | fImp a b =>
      kpair H (natV H 3) (kpair H (tmplCode H sub a) (tmplCode H sub b))
  | fAnd a b =>
      kpair H (natV H 4) (kpair H (tmplCode H sub a) (tmplCode H sub b))
  | fOr a b =>
      kpair H (natV H 5) (kpair H (tmplCode H sub a) (tmplCode H sub b))
  | fAll a => kpair H (natV H 6) (tmplCode H sub a)
  | fEx a => kpair H (natV H 7) (tmplCode H sub a)

/-- A formula with no self-membership atom, hence no marker. -/
def markerFree : Form → Bool
  | fMem i j => !(i == j)
  | fEq _ _ => true
  | fBot => true
  | fImp a b => markerFree a && markerFree b
  | fAnd a b => markerFree a && markerFree b
  | fOr a b => markerFree a && markerFree b
  | fAll a => markerFree a
  | fEx a => markerFree a

/-- On a marker-free formula the template code is the ordinary code, whatever
the substitution. -/
theorem tmplCode_eq_formCode (H : ZFAxioms mem) (sub : Nat → V) :
    ∀ phi : Form, markerFree phi = true → tmplCode H sub phi = formCode H phi := by
  intro phi
  induction phi with
  | fMem i j =>
      intro h
      have hij : ¬ i = j := by
        simp only [markerFree, Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq] at h
        exact h
      show (if i = j then _ else _) = _
      rw [if_neg hij]
      rfl
  | fEq i j => intro _; rfl
  | fBot => intro _; rfl
  | fImp a b iha ihb =>
      intro h
      have h' : markerFree a = true ∧ markerFree b = true := by
        simp only [markerFree, Bool.and_eq_true] at h; exact h
      show kpair H (natV H 3) (kpair H (tmplCode H sub a) (tmplCode H sub b)) = _
      rw [iha h'.1, ihb h'.2]
      rfl
  | fAnd a b iha ihb =>
      intro h
      have h' : markerFree a = true ∧ markerFree b = true := by
        simp only [markerFree, Bool.and_eq_true] at h; exact h
      show kpair H (natV H 4) (kpair H (tmplCode H sub a) (tmplCode H sub b)) = _
      rw [iha h'.1, ihb h'.2]
      rfl
  | fOr a b iha ihb =>
      intro h
      have h' : markerFree a = true ∧ markerFree b = true := by
        simp only [markerFree, Bool.and_eq_true] at h; exact h
      show kpair H (natV H 5) (kpair H (tmplCode H sub a) (tmplCode H sub b)) = _
      rw [iha h'.1, ihb h'.2]
      rfl
  | fAll a ih =>
      intro h
      show kpair H (natV H 6) (tmplCode H sub a) = _
      rw [ih h]
      rfl
  | fEx a ih =>
      intro h
      show kpair H (natV H 7) (tmplCode H sub a) = _
      rw [ih h]
      rfl

/-- "slot `i` is the code of the template `t`, with the code in slot `q k`
plugged in at the marker `fMem k k`".

Each binder shifts the caller's slots by one, so the recursive calls shift `q`
explicitly.

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the second subcode, or the body |
| `1`            | the first subcode               |
| `m+1`, `m+2`   | the caller's slot `m`           |
-/
def fTmplCodeF : (Nat → Nat) → Nat → Form → Form
  | q, i, fMem a b =>
      if a = b then fEq i (q a)
      else fEx (fEx (fAnd (fNumF 1 a)
            (fAnd (fNumF 0 b) (fTagPairF (i+2) 0 1 0))))
  | _, i, fEq a b =>
      fEx (fEx (fAnd (fNumF 1 a) (fAnd (fNumF 0 b) (fTagPairF (i+2) 1 1 0))))
  | _, i, fBot => fTaggedEmptyF i 2
  | q, i, fImp a b =>
      fEx (fEx (fAnd (fTmplCodeF (fun m => q m + 2) 1 a)
        (fAnd (fTmplCodeF (fun m => q m + 2) 0 b) (fTagPairF (i+2) 3 1 0))))
  | q, i, fAnd a b =>
      fEx (fEx (fAnd (fTmplCodeF (fun m => q m + 2) 1 a)
        (fAnd (fTmplCodeF (fun m => q m + 2) 0 b) (fTagPairF (i+2) 4 1 0))))
  | q, i, fOr a b =>
      fEx (fEx (fAnd (fTmplCodeF (fun m => q m + 2) 1 a)
        (fAnd (fTmplCodeF (fun m => q m + 2) 0 b) (fTagPairF (i+2) 5 1 0))))
  | q, i, fAll a =>
      fEx (fAnd (fTmplCodeF (fun m => q m + 1) 0 a) (fTagUnF (i+1) 6 0))
  | q, i, fEx a =>
      fEx (fAnd (fTmplCodeF (fun m => q m + 1) 0 a) (fTagUnF (i+1) 7 0))

theorem fTmplCodeF_spec (H : ZFAxioms mem) :
    ∀ (t : Form) (q : Nat → Nat) (i : Nat) (ee : Nat → V),
      Sat mem ee (fTmplCodeF q i t) ↔ ee i = tmplCode H (fun m => ee (q m)) t := by
  intro t
  induction t with
  | fMem a b =>
      intro q i ee
      by_cases hab : a = b
      · show Sat mem ee (if a = b then fEq i (q a) else _) ↔
          ee i = (if a = b then _ else _)
        rw [if_pos hab, if_pos hab]
        exact Iff.rfl
      · show Sat mem ee (if a = b then _ else _) ↔ ee i = (if a = b then _ else _)
        rw [if_neg hab, if_neg hab]
        constructor
        · rintro ⟨x, y, hx, hy, hi⟩
          have hx' : x = natV H a := (fNumF_spec H a 1 (scons y (scons x ee))).mp hx
          have hy' : y = natV H b := (fNumF_spec H b 0 (scons y (scons x ee))).mp hy
          have hi' := (fTagPairF_spec H (scons y (scons x ee)) (i+2) 0 1 0).mp hi
          rw [hx', hy'] at hi'
          exact hi'
        · intro h
          refine ⟨natV H a, natV H b, (fNumF_spec H a 1 _).mpr rfl,
            (fNumF_spec H b 0 _).mpr rfl, ?_⟩
          exact (fTagPairF_spec H _ (i+2) 0 1 0).mpr h
  | fEq a b =>
      intro q i ee
      constructor
      · rintro ⟨x, y, hx, hy, hi⟩
        have hx' : x = natV H a := (fNumF_spec H a 1 (scons y (scons x ee))).mp hx
        have hy' : y = natV H b := (fNumF_spec H b 0 (scons y (scons x ee))).mp hy
        have hi' := (fTagPairF_spec H (scons y (scons x ee)) (i+2) 1 1 0).mp hi
        rw [hx', hy'] at hi'
        exact hi'
      · intro h
        refine ⟨natV H a, natV H b, (fNumF_spec H a 1 _).mpr rfl,
          (fNumF_spec H b 0 _).mpr rfl, ?_⟩
        exact (fTagPairF_spec H _ (i+2) 1 1 0).mpr h
  | fBot => intro q i ee; exact fTaggedEmptyF_spec H ee i 2
  | fImp a b iha ihb =>
      intro q i ee
      constructor
      · rintro ⟨x, y, hx, hy, hi⟩
        have hx' := (iha (fun m => q m + 2) 1 (scons y (scons x ee))).mp hx
        have hy' := (ihb (fun m => q m + 2) 0 (scons y (scons x ee))).mp hy
        have hi' := (fTagPairF_spec H (scons y (scons x ee)) (i+2) 3 1 0).mp hi
        rw [hx', hy'] at hi'
        exact hi'
      · intro h
        refine ⟨tmplCode H (fun m => ee (q m)) a, tmplCode H (fun m => ee (q m)) b,
          (iha (fun m => q m + 2) 1 _).mpr rfl,
          (ihb (fun m => q m + 2) 0 _).mpr rfl, ?_⟩
        exact (fTagPairF_spec H _ (i+2) 3 1 0).mpr h
  | fAnd a b iha ihb =>
      intro q i ee
      constructor
      · rintro ⟨x, y, hx, hy, hi⟩
        have hx' := (iha (fun m => q m + 2) 1 (scons y (scons x ee))).mp hx
        have hy' := (ihb (fun m => q m + 2) 0 (scons y (scons x ee))).mp hy
        have hi' := (fTagPairF_spec H (scons y (scons x ee)) (i+2) 4 1 0).mp hi
        rw [hx', hy'] at hi'
        exact hi'
      · intro h
        refine ⟨tmplCode H (fun m => ee (q m)) a, tmplCode H (fun m => ee (q m)) b,
          (iha (fun m => q m + 2) 1 _).mpr rfl,
          (ihb (fun m => q m + 2) 0 _).mpr rfl, ?_⟩
        exact (fTagPairF_spec H _ (i+2) 4 1 0).mpr h
  | fOr a b iha ihb =>
      intro q i ee
      constructor
      · rintro ⟨x, y, hx, hy, hi⟩
        have hx' := (iha (fun m => q m + 2) 1 (scons y (scons x ee))).mp hx
        have hy' := (ihb (fun m => q m + 2) 0 (scons y (scons x ee))).mp hy
        have hi' := (fTagPairF_spec H (scons y (scons x ee)) (i+2) 5 1 0).mp hi
        rw [hx', hy'] at hi'
        exact hi'
      · intro h
        refine ⟨tmplCode H (fun m => ee (q m)) a, tmplCode H (fun m => ee (q m)) b,
          (iha (fun m => q m + 2) 1 _).mpr rfl,
          (ihb (fun m => q m + 2) 0 _).mpr rfl, ?_⟩
        exact (fTagPairF_spec H _ (i+2) 5 1 0).mpr h
  | fAll a ih =>
      intro q i ee
      constructor
      · rintro ⟨x, hx, hi⟩
        have hx' := (ih (fun m => q m + 1) 0 (scons x ee)).mp hx
        have hi' := (fTagUnF_spec H (scons x ee) (i+1) 6 0).mp hi
        rw [hx'] at hi'
        exact hi'
      · intro h
        refine ⟨tmplCode H (fun m => ee (q m)) a,
          (ih (fun m => q m + 1) 0 _).mpr rfl, ?_⟩
        exact (fTagUnF_spec H _ (i+1) 6 0).mpr h
  | fEx a ih =>
      intro q i ee
      constructor
      · rintro ⟨x, hx, hi⟩
        have hx' := (ih (fun m => q m + 1) 0 (scons x ee)).mp hx
        have hi' := (fTagUnF_spec H (scons x ee) (i+1) 7 0).mp hi
        rw [hx'] at hi'
        exact hi'
      · intro h
        refine ⟨tmplCode H (fun m => ee (q m)) a,
          (ih (fun m => q m + 1) 0 _).mpr rfl, ?_⟩
        exact (fTagUnF_spec H _ (i+1) 7 0).mpr h

/-- "slot `i` is the code of the fixed external formula `phi`".  The substitution
is irrelevant, since the spec is stated only for marker-free `phi`. -/
def fCodeOfF (i : Nat) (phi : Form) : Form := fTmplCodeF (fun _ => 0) i phi

theorem fCodeOfF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) (phi : Form)
    (h : markerFree phi = true) :
    Sat mem ee (fCodeOfF i phi) ↔ ee i = formCode H phi := by
  rw [fCodeOfF, fTmplCodeF_spec H phi (fun _ => 0) i ee,
    tmplCode_eq_formCode H (fun m => ee ((fun _ => 0) m)) phi h]

/-! ## Internal code constructors

Named so that the schema-code equations below stay readable.  Each is the
constructor's tagged Kuratowski shape, and each preserves codehood. -/

/-- The internal implication constructor on codes. -/
noncomputable def impCodeV (H : ZFAxioms mem) (a b : V) : V :=
  kpair H (natV H 3) (kpair H a b)

/-- The internal conjunction constructor on codes. -/
noncomputable def andCodeV (H : ZFAxioms mem) (a b : V) : V :=
  kpair H (natV H 4) (kpair H a b)

/-- The internal biconditional, a conjunction of two implications, matching the
derived connective `fIff`. -/
noncomputable def iffCodeV (H : ZFAxioms mem) (a b : V) : V :=
  andCodeV H (impCodeV H a b) (impCodeV H b a)

/-- The internal universal constructor on codes. -/
noncomputable def allCodeV (H : ZFAxioms mem) (a : V) : V :=
  kpair H (natV H 6) a

/-- The internal existential constructor on codes. -/
noncomputable def exCodeV (H : ZFAxioms mem) (a : V) : V :=
  kpair H (natV H 7) a

theorem impCodeV_isFormCodeSem (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (impCodeV H a b) := isFormCodeSem_imp H ha hb

theorem andCodeV_isFormCodeSem (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (andCodeV H a b) := isFormCodeSem_and H ha hb

theorem iffCodeV_isFormCodeSem (H : ZFAxioms mem) {a b : V}
    (ha : IsFormCodeSem H a) (hb : IsFormCodeSem H b) :
    IsFormCodeSem H (iffCodeV H a b) :=
  andCodeV_isFormCodeSem H (impCodeV_isFormCodeSem H ha hb)
    (impCodeV_isFormCodeSem H hb ha)

theorem allCodeV_isFormCodeSem (H : ZFAxioms mem) {a : V}
    (ha : IsFormCodeSem H a) : IsFormCodeSem H (allCodeV H a) :=
  isFormCodeSem_all H ha

theorem exCodeV_isFormCodeSem (H : ZFAxioms mem) {a : V}
    (ha : IsFormCodeSem H a) : IsFormCodeSem H (exCodeV H a) :=
  isFormCodeSem_ex H ha

/-! ## The Separation and Replacement instance codes

The skeletons are the schema formulas of `ZF.Zf` with the renamed instance
replaced by a marker: `fMem 0 0` in `SepSkel`, and `fMem 0 0`, `fMem 1 1`,
`fMem 2 2` in `ReplSkel` for the three renamings `rf1`, `rf2`, `ri`. -/

/-- The Separation schema with the renamed instance replaced by marker `0`. -/
def SepSkel : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fAnd (fMem 0 2) (fMem 0 0)))))

/-- The functionality clause with markers `0` and `1`. -/
def FuncSkel : Form :=
  fAll (fAll (fAll (fImp (fAnd (fMem 0 0) (fMem 1 1)) (fEq 1 0))))

/-- The image clause with marker `2`. -/
def ImageSkel : Form :=
  fAll (fEx (fAll (fIff (fMem 0 1) (fEx (fAnd (fMem 0 3) (fMem 2 2))))))

/-- The Replacement schema with the three renamed instances replaced by
markers. -/
def ReplSkel : Form := fImp FuncSkel ImageSkel

/-- The substitution used by `replCodeV`: the three renamings of one code. -/
def replSubV (q1 q2 q3 : V) : Nat → V
  | 0 => q1
  | 1 => q2
  | _ => q3

/-- The slots the three renamed codes occupy inside `fReplCodeF`. -/
def replSlots : Nat → Nat
  | 0 => 4
  | 1 => 2
  | _ => 0

/-- The Separation instance code built from an already renamed subcode. -/
noncomputable def sepCodeVOf (H : ZFAxioms mem) (q : V) : V :=
  tmplCode H (fun _ => q) SepSkel

/-- The Replacement instance code built from three already renamed subcodes. -/
noncomputable def replCodeVOf (H : ZFAxioms mem) (q1 q2 q3 : V) : V :=
  tmplCode H (replSubV q1 q2 q3) ReplSkel

/-- **The internal Separation instance code.** -/
noncomputable def sepCodeV (H : ZFAxioms mem) (p : V) : V :=
  sepCodeVOf H (renameV H (rsepV H) p)

/-- **The internal Replacement instance code.** -/
noncomputable def replCodeV (H : ZFAxioms mem) (p : V) : V :=
  replCodeVOf H (renameV H (rf1V H) p) (renameV H (rf2V H) p)
    (renameV H (riV H) p)

theorem sepCodeVOf_eq (H : ZFAxioms mem) (q : V) :
    sepCodeVOf H q =
      allCodeV H (exCodeV H (allCodeV H
        (iffCodeV H (formCode H (fMem 0 1))
          (andCodeV H (formCode H (fMem 0 2)) q)))) := rfl

theorem replCodeVOf_eq (H : ZFAxioms mem) (q1 q2 q3 : V) :
    replCodeVOf H q1 q2 q3 =
      impCodeV H
        (allCodeV H (allCodeV H (allCodeV H
          (impCodeV H (andCodeV H q1 q2) (formCode H (fEq 1 0))))))
        (allCodeV H (exCodeV H (allCodeV H
          (iffCodeV H (formCode H (fMem 0 1))
            (exCodeV H (andCodeV H (formCode H (fMem 0 3)) q3)))))) := rfl

/-! ### Quotation agreement -/

/-- **The internal Separation constructor agrees with quotation.** -/
theorem sepCodeV_formCode (H : ZFAxioms mem) (phi : Form) :
    sepCodeV H (formCode H phi) = formCode H (Sep_form phi) := by
  show sepCodeVOf H (renameV H (rsepV H) (formCode H phi)) = _
  rw [renameV_rsepV_formCode H phi]
  rfl

/-- **The internal Replacement constructor agrees with quotation.** -/
theorem replCodeV_formCode (H : ZFAxioms mem) (psi : Form) :
    replCodeV H (formCode H psi) = formCode H (Repl_form psi) := by
  show replCodeVOf H (renameV H (rf1V H) (formCode H psi))
    (renameV H (rf2V H) (formCode H psi)) (renameV H (riV H) (formCode H psi)) = _
  rw [renameV_rf1V_formCode H psi, renameV_rf2V_formCode H psi,
    renameV_riV_formCode H psi]
  rfl

/-! ### Codehood -/

theorem sepCodeVOf_isFormCodeSem (H : ZFAxioms mem) {q : V}
    (hq : IsFormCodeSem H q) : IsFormCodeSem H (sepCodeVOf H q) := by
  rw [sepCodeVOf_eq]
  exact allCodeV_isFormCodeSem H (exCodeV_isFormCodeSem H
    (allCodeV_isFormCodeSem H (iffCodeV_isFormCodeSem H
      (formCode_isFormCodeSem H (fMem 0 1))
      (andCodeV_isFormCodeSem H (formCode_isFormCodeSem H (fMem 0 2)) hq))))

theorem replCodeVOf_isFormCodeSem (H : ZFAxioms mem) {q1 q2 q3 : V}
    (h1 : IsFormCodeSem H q1) (h2 : IsFormCodeSem H q2)
    (h3 : IsFormCodeSem H q3) : IsFormCodeSem H (replCodeVOf H q1 q2 q3) := by
  rw [replCodeVOf_eq]
  refine impCodeV_isFormCodeSem H ?_ ?_
  · exact allCodeV_isFormCodeSem H (allCodeV_isFormCodeSem H
      (allCodeV_isFormCodeSem H (impCodeV_isFormCodeSem H
        (andCodeV_isFormCodeSem H h1 h2)
        (formCode_isFormCodeSem H (fEq 1 0)))))
  · exact allCodeV_isFormCodeSem H (exCodeV_isFormCodeSem H
      (allCodeV_isFormCodeSem H (iffCodeV_isFormCodeSem H
        (formCode_isFormCodeSem H (fMem 0 1))
        (exCodeV_isFormCodeSem H (andCodeV_isFormCodeSem H
          (formCode_isFormCodeSem H (fMem 0 3)) h3)))))

/-- **The Separation constructor preserves codehood.** -/
theorem sepCodeV_isFormCodeSem (H : ZFAxioms mem) {p : V}
    (hp : IsFormCodeSem H p) : IsFormCodeSem H (sepCodeV H p) :=
  sepCodeVOf_isFormCodeSem H (renameV_isFormCodeSem H hp (rsepV_isVarMap H))

/-- **The Replacement constructor preserves codehood.** -/
theorem replCodeV_isFormCodeSem (H : ZFAxioms mem) {p : V}
    (hp : IsFormCodeSem H p) : IsFormCodeSem H (replCodeV H p) :=
  replCodeVOf_isFormCodeSem H (renameV_isFormCodeSem H hp (rf1V_isVarMap H))
    (renameV_isFormCodeSem H hp (rf2V_isVarMap H))
    (renameV_isFormCodeSem H hp (riV_isVarMap H))

/-! ### The two schema clauses as `Form`s -/

/-- "slot `c_i` is a Separation instance code".

| de Bruijn slot | contents                       |
| -------------- | ------------------------------ |
| `0`            | the renamed instance `q`       |
| `1`            | the internal renaming `rsepV`  |
| `2`            | the instance code `p`          |
| `m+3`          | the caller's slot `m`          |
-/
def fSepCodeF (c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fEx (fAnd (fRsepMapF 0)
      (fEx (fAnd (fRenamesF 1 2 0)
        (fTmplCodeF (fun _ => 0) (c_i+3) SepSkel))))))

theorem fSepCodeF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i : Nat) :
    Sat mem ee (fSepCodeF c_i) ↔
      ∃ p, IsFormCodeSem H p ∧ ee c_i = sepCodeV H p := by
  constructor
  · rintro ⟨p, hp, r, hr, q, hren, htm⟩
    have hp' : IsFormCodeSem H p := (fIsFormCodeF_spec H (scons p ee) 0).mp hp
    have hr' : r = rsepV H :=
      (fRsepMapF_spec H (scons r (scons p ee)) 0).mp hr
    have hren' :=
      (fRenamesF_spec H (scons q (scons r (scons p ee))) 1 2 0).mp hren
    have htm' :=
      (fTmplCodeF_spec H SepSkel (fun _ => 0) (c_i+3)
        (scons q (scons r (scons p ee)))).mp htm
    rw [hr'] at hren'
    refine ⟨p, hp', ?_⟩
    have hq : renameV H (rsepV H) p = q := renameV_eq H hp' hren'
    show ee c_i = sepCodeVOf H (renameV H (rsepV H) p)
    rw [hq]
    exact htm'
  · rintro ⟨p, hp, hc⟩
    refine ⟨p, (fIsFormCodeF_spec H (scons p ee) 0).mpr hp,
      rsepV H, (fRsepMapF_spec H _ 0).mpr rfl,
      renameV H (rsepV H) p, ?_, ?_⟩
    · exact (fRenamesF_spec H _ 1 2 0).mpr
        (renames_renameV H hp (rsepV_isVarMap H))
    · exact (fTmplCodeF_spec H SepSkel (fun _ => 0) (c_i+3) _).mpr hc

/-- "slot `c_i` is a Replacement instance code".

| de Bruijn slot | contents                             |
| -------------- | ------------------------------------ |
| `0`            | the image renaming `q3` of `p`       |
| `1`            | the internal renaming `riV`          |
| `2`            | the second functionality renaming    |
| `3`            | the internal renaming `rf2V`         |
| `4`            | the first functionality renaming     |
| `5`            | the internal renaming `rf1V`         |
| `6`            | the instance code `p`                |
| `m+7`          | the caller's slot `m`                |
-/
def fReplCodeF (c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fEx (fAnd (fRf1MapF 0)
      (fEx (fAnd (fRenamesF 1 2 0)
        (fEx (fAnd (fRf2MapF 0)
          (fEx (fAnd (fRenamesF 1 4 0)
            (fEx (fAnd (fRiMapF 0)
              (fEx (fAnd (fRenamesF 1 6 0)
                (fTmplCodeF replSlots (c_i+7) ReplSkel))))))))))))))

theorem fReplCodeF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i : Nat) :
    Sat mem ee (fReplCodeF c_i) ↔
      ∃ p, IsFormCodeSem H p ∧ ee c_i = replCodeV H p := by
  constructor
  · rintro ⟨p, hp, r1, hr1, q1, hren1, r2, hr2, q2, hren2, r3, hr3, q3, hren3,
      htm⟩
    have hp' : IsFormCodeSem H p := (fIsFormCodeF_spec H (scons p ee) 0).mp hp
    have hr1' : r1 = rf1V H :=
      (fRf1MapF_spec H (scons r1 (scons p ee)) 0).mp hr1
    have hren1' :=
      (fRenamesF_spec H (scons q1 (scons r1 (scons p ee))) 1 2 0).mp hren1
    have hr2' : r2 = rf2V H :=
      (fRf2MapF_spec H (scons r2 (scons q1 (scons r1 (scons p ee)))) 0).mp hr2
    have hren2' :=
      (fRenamesF_spec H
        (scons q2 (scons r2 (scons q1 (scons r1 (scons p ee))))) 1 4 0).mp hren2
    have hr3' : r3 = riV H :=
      (fRiMapF_spec H
        (scons r3 (scons q2 (scons r2 (scons q1 (scons r1 (scons p ee))))))
        0).mp hr3
    have hren3' :=
      (fRenamesF_spec H
        (scons q3 (scons r3 (scons q2 (scons r2 (scons q1
          (scons r1 (scons p ee))))))) 1 6 0).mp hren3
    have htm' :=
      (fTmplCodeF_spec H ReplSkel replSlots (c_i+7)
        (scons q3 (scons r3 (scons q2 (scons r2 (scons q1
          (scons r1 (scons p ee)))))))).mp htm
    rw [hr1'] at hren1'
    rw [hr2'] at hren2'
    rw [hr3'] at hren3'
    have e1 : renameV H (rf1V H) p = q1 := renameV_eq H hp' hren1'
    have e2 : renameV H (rf2V H) p = q2 := renameV_eq H hp' hren2'
    have e3 : renameV H (riV H) p = q3 := renameV_eq H hp' hren3'
    refine ⟨p, hp', ?_⟩
    show ee c_i = replCodeVOf H (renameV H (rf1V H) p) (renameV H (rf2V H) p)
      (renameV H (riV H) p)
    rw [e1, e2, e3]
    have hsub : (fun m => (scons q3 (scons r3 (scons q2 (scons r2 (scons q1
        (scons r1 (scons p ee))))))) (replSlots m)) = replSubV q1 q2 q3 := by
      funext m
      match m with
      | 0 => rfl
      | 1 => rfl
      | _+2 => rfl
    rw [replCodeVOf, ← hsub]
    exact htm'
  · rintro ⟨p, hp, hc⟩
    refine ⟨p, (fIsFormCodeF_spec H (scons p ee) 0).mpr hp,
      rf1V H, (fRf1MapF_spec H _ 0).mpr rfl,
      renameV H (rf1V H) p,
      (fRenamesF_spec H _ 1 2 0).mpr (renames_renameV H hp (rf1V_isVarMap H)),
      rf2V H, (fRf2MapF_spec H _ 0).mpr rfl,
      renameV H (rf2V H) p,
      (fRenamesF_spec H _ 1 4 0).mpr (renames_renameV H hp (rf2V_isVarMap H)),
      riV H, (fRiMapF_spec H _ 0).mpr rfl,
      renameV H (riV H) p,
      (fRenamesF_spec H _ 1 6 0).mpr (renames_renameV H hp (riV_isVarMap H)),
      ?_⟩
    refine (fTmplCodeF_spec H ReplSkel replSlots (c_i+7) _).mpr ?_
    have hsub : (fun m => (scons (renameV H (riV H) p) (scons (riV H)
        (scons (renameV H (rf2V H) p) (scons (rf2V H)
          (scons (renameV H (rf1V H) p) (scons (rf1V H) (scons p ee)))))))
            (replSlots m))
        = replSubV (renameV H (rf1V H) p) (renameV H (rf2V H) p)
            (renameV H (riV H) p) := by
      funext m
      match m with
      | 0 => rfl
      | 1 => rfl
      | _+2 => rfl
    rw [hsub]
    exact hc

/-! ## The axiom-code predicate

The seven fixed axioms are recognized by equality with their quotations; the two
schemas by an existential over an internal formula code.  Only quotation
soundness is available, and the module header says why the converse is false. -/

/-- **"`c` codes a ZFC axiom", internally.** -/
def IsZFCAxiomCode (H : ZFAxioms mem) (c : V) : Prop :=
  c = formCode H Ext_form ∨ c = formCode H Pair_form ∨
  c = formCode H Union_form ∨ c = formCode H Pow_form ∨
  c = formCode H Inf_form ∨ c = formCode H Reg_form ∨
  c = formCode H Choice_form ∨
  (∃ p, IsFormCodeSem H p ∧ c = sepCodeV H p) ∨
  (∃ p, IsFormCodeSem H p ∧ c = replCodeV H p)

/-- `IsZFCAxiomCode` as a `Form`, in the order of the definition. -/
def fZFCAxiomCodeF (c_i : Nat) : Form :=
  fOr (fCodeOfF c_i Ext_form)
   (fOr (fCodeOfF c_i Pair_form)
    (fOr (fCodeOfF c_i Union_form)
     (fOr (fCodeOfF c_i Pow_form)
      (fOr (fCodeOfF c_i Inf_form)
       (fOr (fCodeOfF c_i Reg_form)
        (fOr (fCodeOfF c_i Choice_form)
         (fOr (fSepCodeF c_i) (fReplCodeF c_i))))))))

theorem fZFCAxiomCodeF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i : Nat) :
    Sat mem ee (fZFCAxiomCodeF c_i) ↔ IsZFCAxiomCode H (ee c_i) := by
  unfold IsZFCAxiomCode
  exact or_congr (fCodeOfF_spec H ee c_i Ext_form (by decide))
    (or_congr (fCodeOfF_spec H ee c_i Pair_form (by decide))
      (or_congr (fCodeOfF_spec H ee c_i Union_form (by decide))
        (or_congr (fCodeOfF_spec H ee c_i Pow_form (by decide))
          (or_congr (fCodeOfF_spec H ee c_i Inf_form (by decide))
            (or_congr (fCodeOfF_spec H ee c_i Reg_form (by decide))
              (or_congr (fCodeOfF_spec H ee c_i Choice_form (by decide))
                (or_congr (fSepCodeF_spec H ee c_i)
                  (fReplCodeF_spec H ee c_i))))))))

/-- **Quotation soundness for the axiom-code predicate.**  Every external ZFC
axiom has an internal axiom code.

The converse is *false* in nonstandard models and is not attempted: the two
schema clauses quantify over the internal code predicate, whose extension
properly contains the quotations. -/
theorem isZFCAxiomCode_of_ZFCax (H : ZFAxioms mem) {f : Form} (h : ZFCax f) :
    IsZFCAxiomCode H (formCode H f) := by
  unfold IsZFCAxiomCode
  rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩) | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨formCode H phi, formCode_isFormCodeSem H phi,
        (sepCodeV_formCode H phi).symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨formCode H psi, formCode_isFormCodeSem H psi,
        (replCodeV_formCode H psi).symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

/-! ## Contexts of axiom codes -/

/-- Every member of the coded context is an internal ZFC axiom code. -/
def CtxZFCAxioms (H : ZFAxioms mem) (g : V) : Prop :=
  ∀ x, MemCtx H x g → IsZFCAxiomCode H x

/-- "every member of the context in slot `g_i` is a ZFC axiom code".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the member `x`        |
| `m+1`          | the caller's slot `m` |
-/
def fCtxZFCAxiomsF (g_i : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g_i+1)) (fZFCAxiomCodeF 0))

theorem fCtxZFCAxiomsF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i : Nat) :
    Sat mem ee (fCtxZFCAxiomsF g_i) ↔ CtxZFCAxioms H (ee g_i) := by
  unfold CtxZFCAxioms
  constructor
  · intro h x hx
    exact (fZFCAxiomCodeF_spec H (scons x ee) 0).mp
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mpr hx))
  · intro h x hx
    exact (fZFCAxiomCodeF_spec H (scons x ee) 0).mpr
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mp hx))

/-- The empty context vacuously consists of axiom codes, which is why
`conZFCForm n` implies `logicConForm n`. -/
theorem ctxZFCAxioms_nil (H : ZFAxioms mem) : CtxZFCAxioms H (ctxNil H) :=
  fun x hx => absurd hx (memCtx_nil H x)

/-- A context assembled from external ZFC axioms consists of axiom codes. -/
theorem ctxZFCAxioms_ctxCode (H : ZFAxioms mem) {G : List Form}
    (hG : ∀ x ∈ G, ZFCax x) : CtxZFCAxioms H (ctxCode H G) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (memCtx_ctxCode H G x).mp hx
  exact isZFCAxiomCode_of_ZFCax H (hG a ha)

/-! ## The sentence `Con_n(ZFC)`

For each metatheoretic `n` the sentence says: no set is at once a coded
derivation of the falsity code from a context of ZFC axiom codes and bounded, at
every occurrence, by the numeral of `n`.  The bound is written as the numeral
rather than quantified, which is what keeps the parameter metatheoretic.

Unlike `logicConForm n` of `BoundedZFCConsistency.CodedRank`, the context is
*quantified* and constrained by `fCtxZFCAxiomsF`, not pinned to `ctxNil`. -/

/-- The body of the sentence, with four leading binders.

| de Bruijn slot | contents                      |
| -------------- | ----------------------------- |
| `0`            | the candidate derivation `d`  |
| `1`            | the context code `g`          |
| `2`            | the falsity code              |
| `3`            | the numeral bound             |
-/
def conZFCBodyF (n : Nat) : Form :=
  fAll (fAll (fAll (fAll
    (fImp (fNumF 3 n)
      (fImp (fTaggedEmptyF 2 2)
        (fImp (fCtxZFCAxiomsF 1)
          (fImp (fAnd (fDerivesF 0 1 2) (fDerAllBoundedF 3 0)) fBot)))))))

theorem conZFCBodyF_spec (H : ZFAxioms mem) (n : Nat) (ee : Nat → V) :
    Sat mem ee (conZFCBodyF n) ↔
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := by
  constructor
  · rintro h ⟨d, g, hax, hder, hbnd⟩
    exact h (natV H n) (kpair H (natV H 2) (vempty H)) g d
      ((fNumF_spec H n 3 _).mpr rfl)
      ((fTaggedEmptyF_spec H _ 2 2).mpr rfl)
      ((fCtxZFCAxiomsF_spec H _ 1).mpr hax)
      ⟨(fDerivesF_spec H _ 0 1 2).mpr hder,
        (fDerAllBoundedF_spec H _ 3 0).mpr hbnd⟩
  · intro h b c g d hb hc hax hd
    have hb' : b = natV H n := (fNumF_spec H n 3 _).mp hb
    have hc' : c = kpair H (natV H 2) (vempty H) :=
      (fTaggedEmptyF_spec H _ 2 2).mp hc
    have hax' := (fCtxZFCAxiomsF_spec H _ 1).mp hax
    have hder := (fDerivesF_spec H _ 0 1 2).mp hd.1
    have hbnd := (fDerAllBoundedF_spec H _ 3 0).mp hd.2
    rw [hc'] at hder
    rw [hb'] at hbnd
    exact h ⟨d, g, hax', hder, hbnd⟩

/-- **`Con_n(ZFC)`**, as an object-language sentence: the universal closure of
`conZFCBodyF n`.  Sealing is what makes sentencehood free; the body is closed in
any case, but computing that over a formula of this size is not worth the
elaboration. -/
def conZFCForm (n : Nat) : Form := sealF (conZFCBodyF n)

theorem sentence_conZFCForm (n : Nat) : Sentence (conZFCForm n) :=
  Sentence_seal _

/-- **The arbitrary-model characterization.**  In any model of the `ZFAxioms`
bundle, `Con_n(ZFC)` holds exactly when no coded derivation of falsity from a
context of ZFC axiom codes has all of its occurrences bounded by the numeral of
`n`. -/
theorem sat_conZFCForm_iff (H : ZFAxioms mem) (n : Nat) :
    (∀ e : Nat → V, Sat mem e (conZFCForm n)) ↔
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := by
  have hs := seal_valid (mem := mem) (conZFCBodyF n)
  constructor
  · intro h
    exact (conZFCBodyF_spec H n (fun _ => vempty H)).mp (hs.mp h _)
  · intro h
    exact hs.mpr (fun e => (conZFCBodyF_spec H n e).mpr h)

/-- The new sentence is at least as strong as the one over the empty context:
`ctxNil` is a context of axiom codes. -/
theorem no_bounded_refutation_nil_of_conZFC (H : ZFAxioms mem) (n : Nat)
    (h : ¬ ∃ d g, CtxZFCAxioms H g ∧
      Derives H d g (kpair H (natV H 2) (vempty H)) ∧
      DerAllBounded H (natV H n) d) :
    ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
      DerAllBounded H (natV H n) d := by
  rintro ⟨d, hder, hbnd⟩
  exact h ⟨d, ctxNil H, ctxZFCAxioms_nil H, hder, hbnd⟩

end AxiomCode

/-! ## From models of ZFC to the object-level derivation

The endpoint bridge, in the shape `BoundedZFCConsistency.CodedRank` uses for
`logicConForm`.  `godel_completeness_for_theories` turns truth in every model of
a sentence theory into a derivation from that theory, and `ZFCax_s` is a sentence
theory by `Sentences_ZFC`, so after this the remaining obligation is exactly "no
model of ZFC carries a bounded coded refutation from an axiom-code context" —
which is what the reflection layer will supply, and which nothing here
asserts. -/

section Endpoint

open SetTheory.FirstOrderClassicalCompleteness

/-- If no model of ZFC carries a bounded coded refutation from a context of
axiom codes, then `Con_n(ZFC)` is a semantic consequence of ZFC. -/
theorem conZFCForm_semanticConsequence (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySemanticConsequence ZFCax_s (conZFCForm n) := by
  intro Dom m v hmodel
  exact (sat_conZFCForm_iff (zfAxioms_of_zfcModel v hmodel) n).mpr
    (h Dom m (zfAxioms_of_zfcModel v hmodel)) v

/-- **The endpoint bridge.**  Truth of `Con_n(ZFC)` in every model of ZFC yields
an object-level derivation of it from ZFC. -/
theorem zfcprov_conZFCForm_of_valid (n : Nat)
    (h : TheorySemanticConsequence ZFCax_s (conZFCForm n)) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  godel_completeness_for_theories ZFCax_s (conZFCForm n) Sentences_ZFC h

/-- **The whole remaining obligation of the project, in one statement.**  The
hypothesis is a single semantic claim about arbitrary models of the `ZFAxioms`
bundle; everything between it and `ZFC |- Con_n(ZFC)` is proved. -/
theorem zfcprov_conZFCForm_of_no_bounded_refutation (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm_of_valid n (conZFCForm_semanticConsequence n h)

end Endpoint

end BoundedZFCConsistency
end LeanProofs
