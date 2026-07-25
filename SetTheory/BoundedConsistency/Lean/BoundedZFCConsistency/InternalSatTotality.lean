import BoundedZFCConsistency.InternalSat

/-!
# Totality of satisfaction certificates, and the satisfaction relation

`BoundedZFCConsistency.InternalSat` proves that certificates are *single
valued*: two certificates never assign different bits to the same code under
the same environment.  That leaves `Certifies` a partial assignment.  This
module proves the missing half — **totality** — and therefore turns the
certificate relation into a genuine satisfaction predicate for set-sized
structures inside a model of ZF, with its Tarski clauses available as ordinary
lemmas.

## The obstruction, and how it is met

Totality is proved by `isFormCodeSem_ind'`, so the induction hypothesis is
available only in the form of a property of a code, rendered as a `Form`.  The
quantifier cases need a certificate for the subcode uniformly in `d ∈ A`, and
Replacement collects images along a *definable* map, not along an arbitrary
Lean function.  Choosing one certificate per `d` therefore needs a definable
choice, which is not available.

The property proved by induction avoids the choice entirely by being
**uniform in a whole set of environments**:

```text
TotalOn H A R c :
  ∀ E, (every member of E is an environment) →
    ∃ S, SatClosed H A R S ∧ ∀ e ∈ E, ∃ b, ⟨c, e, b⟩ ∈ S
```

One certificate now serves every environment in `E` at once, so the quantifier
case applies the induction hypothesis *once*, to the set

```text
shiftEnvs H A E = E ∪ { econs H d e : d ∈ A, e ∈ E }
```

and never has to select anything.  That set is produced by the one-step
closure operator `gstep` of `ZF.Zf`, whose set-likeness hypothesis is
discharged by a Replacement image of `A` — the choice of *bound* may be made
by Lean-level case analysis, since a bound need not be definable, only the
relation must be.

## The extension step

Every case then has the same shape: a step-closed set `S` is already given,
and every `e ∈ E` admits a bit locally justified by `S`; the code's own
triples are added.  `exists_extend` performs that once and for all.  The new
triples are carved out **by Separation**, not by Replacement, from the set

```text
tripleBound H c E ⊇ { ⟨c, e, b⟩ : e ∈ E, b ∈ {0, 1} },
```

which exists because the two truth bits are two fixed sets and the Kuratowski
pairs over a set form a set.  The selecting formula is `psiNewF`: it asserts
the *shape* of the element and the local step relation, so the separated set
contains no junk, and re-establishing step-closure for the union is then two
lines.  Since `Justified` mentions the certificate only positively, it is
monotone, which is what makes the union of two step-closed sets step-closed.

## The satisfaction relation

`SatIn H A R c e` says that some certificate assigns the bit one.  Totality
and single-valuedness together make it well behaved: `certifies_bit` states
that the bit assigned by *any* certificate is exactly `vbit` of `SatIn`, which
is the form in which the Tarski clauses are read off the inversion lemmas of
`InternalSat`.  Those clauses — two atomic, falsity, the three Boolean
connectives, and the two quantifiers ranging over `d ∈ A` with `econs` — are
the interface later modules consume.

Nothing here assumes that a code is the quotation of an external formula; the
converse of quotation soundness is false in nonstandard models, and every
statement below is about arbitrary internal codes.

## De Bruijn bookkeeping

Every formula below carries a table of its de Bruijn slots.  Slot arguments
named `_i` are ABSOLUTE positions in the environment at the use site.  The
convention matches `ZF.Zf` and `BoundedZFCConsistency.InternalSat`.

Neither Powerset nor Regularity is used, matching the six axioms bundled in
`ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section InternalSatTotality

variable {V : Type u} {mem : V → V → Prop}

/-! ## The step relation is monotone and two-valued

Both facts are read off the eight clauses.  Monotonicity holds because the
certificate is mentioned only positively — every occurrence is a membership
assertion — which is exactly what fails for satisfaction itself and is why the
whole development goes through certificates.  Two-valuedness holds because
every clause fixes the bit either literally or as a `vbit`. -/

/-- A truth bit is one of the two numerals. -/
theorem vbit_zero_or_one (H : ZFAxioms mem) (p : Prop) :
    vbit H p = natV H 0 ∨ vbit H p = natV H 1 := by
  by_cases hp : p
  · exact Or.inr (vbit_pos H hp)
  · exact Or.inl (vbit_neg H hp)

/-- **A justified bit is `0` or `1`.**  Nothing else can be justified, which is
what lets the quantifier cases decide between the two witnesses. -/
theorem justified_bit (H : ZFAxioms mem) {A R S c e b : V}
    (h : Justified H A R S c e b) : b = natV H 0 ∨ b = natV H 1 := by
  unfold Justified at h
  rcases h with ⟨_, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, hb⟩ | ⟨_, hb⟩ |
    ⟨_, _, _, _, _, _, _, hb⟩ | ⟨_, _, _, _, _, _, _, hb⟩ |
    ⟨_, _, _, _, _, _, _, hb⟩ | ⟨_, _, hcase⟩ | ⟨_, _, hcase⟩
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _
  · exact Or.inl hb
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _
  · rw [hb]; exact vbit_zero_or_one H _
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rcases hcase with ⟨hb, _⟩ | ⟨hb, _⟩
    · exact Or.inl hb
    · exact Or.inr hb

/-- **The step relation is monotone in the certificate.**  Every occurrence of
the certificate in the eight clauses is positive. -/
theorem justified_mono (H : ZFAxioms mem) {A R S S' c e b : V}
    (hsub : ∀ x, mem x S → mem x S') (h : Justified H A R S c e b) :
    Justified H A R S' c e b := by
  unfold Justified at h ⊢
  rcases h with h | h | h | ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩ |
    ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩ | ⟨c1, c2, b1, b2, hc, k1, k2, hb⟩ |
    ⟨c1, hc, hcase⟩ | ⟨c1, hc, hcase⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, c2, b1, b2, hc, hsub _ k1, hsub _ k2, hb⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨c1, hc, ?_⟩))))))
    rcases hcase with ⟨hb, hall⟩ | ⟨hb, d, hd, hdz⟩
    · exact Or.inl ⟨hb, fun d hd => hsub _ (hall d hd)⟩
    · exact Or.inr ⟨hb, d, hd, hsub _ hdz⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨c1, hc, ?_⟩))))))
    rcases hcase with ⟨hb, hall⟩ | ⟨hb, d, hd, hdo⟩
    · exact Or.inl ⟨hb, fun d hd => hsub _ (hall d hd)⟩
    · exact Or.inr ⟨hb, d, hd, hsub _ hdo⟩

/-! ### Step-closed sets

The empty set is step-closed vacuously, and monotonicity makes the union of
two step-closed sets step-closed.  Both are used in every case of the
induction. -/

/-- The empty set is a certificate for nothing. -/
theorem satClosed_empty (H : ZFAxioms mem) (A R : V) :
    SatClosed H A R (vempty H) := by
  intro c e b hmem
  exact absurd hmem (vempty_spec H _)

/-- The union of two step-closed sets is step-closed. -/
theorem satClosed_cup (H : ZFAxioms mem) {A R S1 S2 : V}
    (h1 : SatClosed H A R S1) (h2 : SatClosed H A R S2) :
    SatClosed H A R (vcup H S1 S2) := by
  have hsub1 : ∀ x, mem x S1 → mem x (vcup H S1 S2) :=
    fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inl hx)
  have hsub2 : ∀ x, mem x S2 → mem x (vcup H S1 S2) :=
    fun x hx => (vcup_spec H S1 S2 x).mpr (Or.inr hx)
  intro c e b hmem
  rcases (vcup_spec H S1 S2 _).mp hmem with h | h
  · exact ⟨(h1 c e b h).1, justified_mono H hsub1 (h1 c e b h).2⟩
  · exact ⟨(h2 c e b h).1, justified_mono H hsub2 (h2 c e b h).2⟩

/-! ## The extension step

Given a step-closed `S` and, for every `e` in a set `E` of environments, a bit
locally justified by `S`, the triples for one further code are added.  They
are carved out by Separation from a set large enough to hold them, and the
selecting formula asserts both the shape of the element and the step relation,
so the separated set consists of nothing else. -/

/-- The parameter block of `psiNewF`.

| de Bruijn slot | contents                              |
| -------------- | ------------------------------------- |
| `0`            | the code `c` whose triples are added  |
| `1`            | the set `E` of environments           |
| `2`            | the certificate `S` justifying them   |
| `3`            | the carrier `A`                       |
| `4`            | the relation `R`                      |
-/
noncomputable def envExtend (H : ZFAxioms mem) (A R c E S : V) : Nat → V :=
  scons c (scons E (scons S (scons A (scons R (fun _ => vempty H)))))

/-- "slot `0` is a triple `⟨c, e, b⟩` with `e` in `E` and the triple justified
by `S`" — the Separation formula selecting the newly added triples.

| de Bruijn slot | contents                                        |
| -------------- | ----------------------------------------------- |
| `0`            | the candidate `t`, then `e`, then the bit `b`   |
| `1`            | under one binder: `t`; under two: `e`           |
| `2`            | under two binders: `t`                          |
| `m+1`, `m+3`   | the parameter-block slot `m`                    |
-/
def psiNewF : Form :=
  fEx (fAnd (fMem 0 3)
    (fEx (fAnd (fTripleF 2 3 1 0) (fJustifiedF 3 1 0 5 6 7))))

theorem psiNewF_spec (H : ZFAxioms mem) {A R c E S : V}
    (hE : ∀ e, mem e E → IsEnvOn H A e) (t : V) :
    Sat mem (scons t (envExtend H A R c E S)) psiNewF ↔
      ∃ e, mem e E ∧ ∃ b, t = satTriple H c e b ∧
        Justified H A R S c e b := by
  constructor
  · rintro ⟨e, hmem, b, ht, hj⟩
    have hmem' : mem e E := hmem
    refine ⟨e, hmem', b, ?_, ?_⟩
    · exact (fTripleF_spec H
        (scons b (scons e (scons t (envExtend H A R c E S)))) 2 3 1 0).mp ht
    · exact (fJustifiedF_spec H
        (scons b (scons e (scons t (envExtend H A R c E S))))
        3 1 0 5 6 7 (hE e hmem').1).mp hj
  · rintro ⟨e, hmem, b, ht, hj⟩
    refine ⟨e, hmem, b, ?_, ?_⟩
    · exact (fTripleF_spec H
        (scons b (scons e (scons t (envExtend H A R c E S)))) 2 3 1 0).mpr ht
    · exact (fJustifiedF_spec H
        (scons b (scons e (scons t (envExtend H A R c E S))))
        3 1 0 5 6 7 (hE e hmem).1).mpr hj

/-- The carrier of the bound: the environments, the two truth bits, and the
code. -/
noncomputable def tripleBase (H : ZFAxioms mem) (c E : V) : V :=
  vcup H (vcup H E (vpair H (natV H 0) (natV H 1))) (vsingle H c)

/-- A set containing every triple `⟨c, e, b⟩` with `e ∈ E` and `b` a truth
bit.  Two rounds of the Kuratowski-pair image suffice, because a triple is a
pair of the code with a pair. -/
noncomputable def tripleBound (H : ZFAxioms mem) (c E : V) : V :=
  pairImg H (vcup H (pairImg H (tripleBase H c E)) (tripleBase H c E))

theorem mem_tripleBase_of_mem (H : ZFAxioms mem) {c E x : V} (h : mem x E) :
    mem x (tripleBase H c E) := by
  unfold tripleBase
  exact (vcup_spec H _ _ x).mpr (Or.inl ((vcup_spec H E _ x).mpr (Or.inl h)))

theorem mem_tripleBase_of_bit (H : ZFAxioms mem) {c E x : V}
    (h : x = natV H 0 ∨ x = natV H 1) : mem x (tripleBase H c E) := by
  unfold tripleBase
  exact (vcup_spec H _ _ x).mpr
    (Or.inl ((vcup_spec H E _ x).mpr (Or.inr ((vpair_spec H _ _ x).mpr h))))

theorem mem_tripleBase_code (H : ZFAxioms mem) (c E : V) :
    mem c (tripleBase H c E) := by
  unfold tripleBase
  exact (vcup_spec H _ _ c).mpr (Or.inr ((vsingle_spec H c c).mpr rfl))

theorem satTriple_mem_tripleBound (H : ZFAxioms mem) {c E e b : V}
    (he : mem e E) (hb : b = natV H 0 ∨ b = natV H 1) :
    mem (satTriple H c e b) (tripleBound H c E) := by
  have hpair : mem (kpair H e b)
      (vcup H (pairImg H (tripleBase H c E)) (tripleBase H c E)) :=
    (vcup_spec H _ _ _).mpr (Or.inl ((pairImg_spec H (tripleBase H c E) _).mpr
      ⟨e, b, mem_tripleBase_of_mem H he, mem_tripleBase_of_bit H hb, rfl⟩))
  have hcode : mem c
      (vcup H (pairImg H (tripleBase H c E)) (tripleBase H c E)) :=
    (vcup_spec H _ _ _).mpr (Or.inr (mem_tripleBase_code H c E))
  exact (pairImg_spec H _ _).mpr ⟨c, kpair H e b, hcode, hpair, rfl⟩

/-- The triples added by one extension step. -/
noncomputable def newTriples (H : ZFAxioms mem) (A R c E S : V) : V :=
  sepD H psiNewF (envExtend H A R c E S) (tripleBound H c E)

theorem newTriples_shape (H : ZFAxioms mem) {A R c E S : V}
    (hE : ∀ e, mem e E → IsEnvOn H A e) {t : V}
    (ht : mem t (newTriples H A R c E S)) :
    ∃ e, mem e E ∧ ∃ b, t = satTriple H c e b ∧ Justified H A R S c e b := by
  unfold newTriples at ht
  exact (psiNewF_spec H hE t).mp
    ((sepD_spec H psiNewF (envExtend H A R c E S) (tripleBound H c E) t).mp ht).2

theorem satTriple_mem_newTriples (H : ZFAxioms mem) {A R c E S e b : V}
    (hE : ∀ e, mem e E → IsEnvOn H A e) (he : mem e E)
    (hj : Justified H A R S c e b) :
    mem (satTriple H c e b) (newTriples H A R c E S) := by
  unfold newTriples
  refine (sepD_spec H psiNewF (envExtend H A R c E S) (tripleBound H c E)
    (satTriple H c e b)).mpr ⟨?_, ?_⟩
  · exact satTriple_mem_tripleBound H he (justified_bit H hj)
  · exact (psiNewF_spec H hE (satTriple H c e b)).mpr ⟨e, he, b, rfl, hj⟩

/-- **One extension step.**  If every environment in `E` already has a bit
locally justified by the step-closed set `S`, then a step-closed set recording
those triples exists. -/
theorem exists_extend (H : ZFAxioms mem) {A R c E S : V}
    (hE : ∀ e, mem e E → IsEnvOn H A e) (hS : SatClosed H A R S)
    (hj : ∀ e, mem e E → ∃ b, Justified H A R S c e b) :
    ∃ S', SatClosed H A R S' ∧
      ∀ e, mem e E → ∃ b, mem (satTriple H c e b) S' := by
  refine ⟨vcup H S (newTriples H A R c E S), ?_, ?_⟩
  · have hsub : ∀ x, mem x S → mem x (vcup H S (newTriples H A R c E S)) :=
      fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
    intro c0 e0 b0 hmem
    rcases (vcup_spec H _ _ _).mp hmem with h | h
    · exact ⟨(hS c0 e0 b0 h).1, justified_mono H hsub (hS c0 e0 b0 h).2⟩
    · obtain ⟨e, hmemE, b, ht, hjust⟩ := newTriples_shape H hE h
      obtain ⟨hc, hee, hbb⟩ := satTriple_inj H ht
      refine ⟨?_, ?_⟩
      · rw [hee]; exact hE e hmemE
      · rw [hc, hee, hbb]; exact justified_mono H hsub hjust
  · intro e he
    obtain ⟨b, hb⟩ := hj e he
    exact ⟨b, (vcup_spec H _ _ _).mpr
      (Or.inr (satTriple_mem_newTriples H hE he hb))⟩

/-! ## Shifting a whole set of environments

The quantifier cases apply the induction hypothesis once, to the set of all
one-step shifts of the environments in `E`.  That set is produced by the
one-step closure operator `gstep` of `ZF.Zf`, whose set-likeness hypothesis is
discharged by a Replacement image of the carrier: a *bound* may be chosen by
Lean-level case analysis, since only the relation has to be definable. -/

/-- The graph of `d ↦ econs H d E`, with `E` as the parameter in slot `2`.

| de Bruijn slot | contents             |
| -------------- | -------------------- |
| `0`            | the shifted value    |
| `1`            | the new head `d`     |
| `2`            | the parameter `E`    |
-/
def psiEconsF : Form := fEconsF 0 1 2

theorem psiEconsF_rel (H : ZFAxioms mem) {E : V}
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y')
    (u d : V) :
    relOf mem psiEconsF (fun _ => E) u d ↔ u = econs H d E := by
  unfold relOf psiEconsF
  exact fEconsF_spec H (scons u (scons d (fun _ => E))) 0 1 2 hfun

theorem psiEconsF_functional (H : ZFAxioms mem) {E : V}
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y') :
    Functional (relOf mem psiEconsF (fun _ => E)) := by
  intro d u u' h1 h2
  rw [(psiEconsF_rel H hfun u d).mp h1, (psiEconsF_rel H hfun u' d).mp h2]

/-- The set of shifts of `E` by the elements of `A`. -/
noncomputable def econsImg (H : ZFAxioms mem) (A E : V)
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y') :
    V :=
  (H.repl psiEconsF (fun _ => E) (psiEconsF_functional H hfun) A).choose

theorem econsImg_spec (H : ZFAxioms mem) (A E : V)
    (hfun : ∀ x y y', mem (kpair H x y) E → mem (kpair H x y') E → y = y')
    (u : V) :
    mem u (econsImg H A E hfun) ↔ ∃ d, mem d A ∧ u = econs H d E := by
  unfold econsImg
  rw [(H.repl psiEconsF (fun _ => E) (psiEconsF_functional H hfun)
    A).choose_spec u]
  constructor
  · rintro ⟨d, hd, hrel⟩
    exact ⟨d, hd, (psiEconsF_rel H hfun u d).mp hrel⟩
  · rintro ⟨d, hd, hu⟩
    exact ⟨d, hd, (psiEconsF_rel H hfun u d).mpr hu⟩

/-- "slot `0` is a shift of slot `1` by an element of the carrier, and slot `1`
is an environment".  The guard is not decoration: without it the relation
would have no bound at arguments that are not functions, and set-likeness
would fail.

| de Bruijn slot | contents                            |
| -------------- | ----------------------------------- |
| `0`            | the shifted value `u`, then `d`     |
| `1`            | the argument `e`, then `u`          |
| `2`            | the carrier `A`, then `e`           |
| `3`            | under the binder: the carrier `A`   |
-/
def chiShiftF : Form :=
  fAnd (fEnvOnF 1 2) (fEx (fAnd (fMem 0 3) (fEconsF 1 0 2)))

theorem chiShiftF_rel (H : ZFAxioms mem) (A u e : V) :
    relOf mem chiShiftF (fun _ => A) u e ↔
      (IsEnvOn H A e ∧ ∃ d, mem d A ∧ u = econs H d e) := by
  unfold relOf chiShiftF
  constructor
  · rintro ⟨henv, d, hd, hu⟩
    have henv' : IsEnvOn H A e :=
      (fEnvOnF_spec H (scons u (scons e (fun _ => A))) 1 2).mp henv
    exact ⟨henv', d, hd,
      (fEconsF_spec H (scons d (scons u (scons e (fun _ => A))))
        1 0 2 henv'.1.1).mp hu⟩
  · rintro ⟨henv, d, hd, hu⟩
    exact ⟨(fEnvOnF_spec H (scons u (scons e (fun _ => A))) 1 2).mpr henv,
      d, hd,
      (fEconsF_spec H (scons d (scons u (scons e (fun _ => A))))
        1 0 2 henv.1.1).mpr hu⟩

theorem chiShiftF_setLike (H : ZFAxioms mem) (A : V) :
    SetLike mem (relOf mem chiShiftF (fun _ => A)) := by
  intro e
  by_cases henv : IsEnvOn H A e
  · refine ⟨econsImg H A e henv.1.1, fun u hu => ?_⟩
    obtain ⟨_, d, hd, hue⟩ := (chiShiftF_rel H A u e).mp hu
    exact (econsImg_spec H A e henv.1.1 u).mpr ⟨d, hd, hue⟩
  · exact ⟨vempty H, fun u hu => absurd ((chiShiftF_rel H A u e).mp hu).1 henv⟩

/-- **`E` together with every one-step shift of its members.** -/
noncomputable def shiftEnvs (H : ZFAxioms mem) (A E : V) : V :=
  gstep H chiShiftF (fun _ => A) E

theorem shiftEnvs_spec (H : ZFAxioms mem) (A E u : V) :
    mem u (shiftEnvs H A E) ↔
      (mem u E ∨
        ∃ e, mem e E ∧ IsEnvOn H A e ∧ ∃ d, mem d A ∧ u = econs H d e) := by
  unfold shiftEnvs
  rw [gstep_spec H chiShiftF (fun _ => A) (chiShiftF_setLike H A) E u]
  constructor
  · rintro (h | ⟨v, hv, hrel⟩)
    · exact Or.inl h
    · obtain ⟨henv, d, hd, hu⟩ := (chiShiftF_rel H A u v).mp hrel
      exact Or.inr ⟨v, hv, henv, d, hd, hu⟩
  · rintro (h | ⟨e, he, henv, d, hd, hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, (chiShiftF_rel H A u e).mpr ⟨henv, d, hd, hu⟩⟩

theorem econs_mem_shiftEnvs (H : ZFAxioms mem) {A E e d : V} (he : mem e E)
    (henv : IsEnvOn H A e) (hd : mem d A) :
    mem (econs H d e) (shiftEnvs H A E) :=
  (shiftEnvs_spec H A E _).mpr (Or.inr ⟨e, he, henv, d, hd, rfl⟩)

theorem shiftEnvs_isEnvOn (H : ZFAxioms mem) {A E : V}
    (hE : ∀ e, mem e E → IsEnvOn H A e) :
    ∀ u, mem u (shiftEnvs H A E) → IsEnvOn H A u := by
  intro u hu
  rcases (shiftEnvs_spec H A E u).mp hu with h | ⟨e, _, henv, d, hd, hue⟩
  · exact hE u h
  · rw [hue]
    exact econs_isEnvOn H henv hd

/-! ## Totality, uniformly in a set of environments

The property carried by the induction is uniform in a set `E` of
environments.  That uniformity is what removes the definable choice from the
quantifier cases: the induction hypothesis is applied *once*, to
`shiftEnvs H A E`, instead of once per element of the carrier. -/

/-- One certificate serves every environment in `E`. -/
def TotalOn (H : ZFAxioms mem) (A R c : V) : Prop :=
  ∀ E, (∀ e, mem e E → IsEnvOn H A e) →
    ∃ S, SatClosed H A R S ∧ ∀ e, mem e E → ∃ b, mem (satTriple H c e b) S

/-- `TotalOn` as a `Form`, with the code in slot `0` of the caller.

| de Bruijn slot | contents                                          |
| -------------- | ------------------------------------------------- |
| `0`            | the set `E`, then `S` or the tested `e`, then `b` |
| `1`            | the code `c` under one binder                     |
| `2`            | the carrier `A` under one binder                  |
| `3`            | the relation `R` under one binder                 |
-/
def fTotalOnF : Form :=
  fAll (fImp (fAll (fImp (fMem 0 1) (fEnvOnF 0 3)))
    (fEx (fAnd (fSatClosedF 0 3 4)
      (fAll (fImp (fMem 0 2) (fEx (fTripleMemF 4 1 0 2)))))))

/-- The parameter block of `fTotalOnF`: the carrier, then the relation. -/
noncomputable def envTotal (H : ZFAxioms mem) (A R : V) : Nat → V :=
  scons A (scons R (fun _ => vempty H))

theorem fTotalOnF_spec (H : ZFAxioms mem) (A R y : V) :
    Sat mem (scons y (envTotal H A R)) fTotalOnF ↔ TotalOn H A R y := by
  unfold TotalOn
  constructor
  · intro h E hE
    obtain ⟨S, hclosed, hall⟩ :=
      h E (fun e he => (fEnvOnF_spec H
        (scons e (scons E (scons y (envTotal H A R)))) 0 3).mpr (hE e he))
    refine ⟨S, (fSatClosedF_spec H
      (scons S (scons E (scons y (envTotal H A R)))) 0 3 4).mp hclosed,
      fun e he => ?_⟩
    obtain ⟨b, hb⟩ := hall e he
    exact ⟨b, (fTripleMemF_spec H
      (scons b (scons e (scons S (scons E (scons y (envTotal H A R))))))
      4 1 0 2).mp hb⟩
  · intro h E hE
    obtain ⟨S, hclosed, hall⟩ :=
      h E (fun e he => (fEnvOnF_spec H
        (scons e (scons E (scons y (envTotal H A R)))) 0 3).mp (hE e he))
    refine ⟨S, (fSatClosedF_spec H
      (scons S (scons E (scons y (envTotal H A R)))) 0 3 4).mpr hclosed,
      fun e he => ?_⟩
    obtain ⟨b, hb⟩ := hall e he
    exact ⟨b, (fTripleMemF_spec H
      (scons b (scons e (scons S (scons E (scons y (envTotal H A R))))))
      4 1 0 2).mpr hb⟩

/-- **Totality, in the uniform form the induction proves.**

The two atomic cases and falsity start from the empty certificate; the three
Boolean cases union the two certificates supplied by the induction hypothesis
at the *same* set of environments; and the two quantifier cases apply the
induction hypothesis once, at the shifted set, and then decide the bit by a
case analysis whose negative branch is closed by `justified_bit` — a subcode
whose bit is not one has bit zero, and that is exactly the witness the clause
asks for. -/
theorem totalOn_of_isFormCodeSem (H : ZFAxioms mem) (A R : V) :
    ∀ c, IsFormCodeSem H c → TotalOn H A R c := by
  refine isFormCodeSem_ind' H (TotalOn H A R) fTotalOnF (envTotal H A R)
    (fun y => (fTotalOnF_spec H A R y).symm) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j hi hj E hE
    refine exists_extend H hE (satClosed_empty H A R) (fun e he => ?_)
    refine ⟨vbit H (mem (kpair H (applyV H e i) (applyV H e j)) R), ?_⟩
    unfold Justified
    exact Or.inl ⟨i, j, hi, hj, rfl, rfl⟩
  · intro i j hi hj E hE
    refine exists_extend H hE (satClosed_empty H A R) (fun e he => ?_)
    refine ⟨vbit H (applyV H e i = applyV H e j), ?_⟩
    unfold Justified
    exact Or.inr (Or.inl ⟨i, j, hi, hj, rfl, rfl⟩)
  · intro E hE
    refine exists_extend H hE (satClosed_empty H A R) (fun e he => ?_)
    refine ⟨natV H 0, ?_⟩
    unfold Justified
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro x y hx hy E hE
    obtain ⟨S1, hS1, k1⟩ := hx E hE
    obtain ⟨S2, hS2, k2⟩ := hy E hE
    refine exists_extend H hE (satClosed_cup H hS1 hS2) (fun e he => ?_)
    obtain ⟨b1, hb1⟩ := k1 e he
    obtain ⟨b2, hb2⟩ := k2 e he
    refine ⟨vbit H (b1 = natV H 1 → b2 = natV H 1), ?_⟩
    unfold Justified
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, b1, b2, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl hb1),
      (vcup_spec H S1 S2 _).mpr (Or.inr hb2), rfl⟩)))
  · intro x y hx hy E hE
    obtain ⟨S1, hS1, k1⟩ := hx E hE
    obtain ⟨S2, hS2, k2⟩ := hy E hE
    refine exists_extend H hE (satClosed_cup H hS1 hS2) (fun e he => ?_)
    obtain ⟨b1, hb1⟩ := k1 e he
    obtain ⟨b2, hb2⟩ := k2 e he
    refine ⟨vbit H (b1 = natV H 1 ∧ b2 = natV H 1), ?_⟩
    unfold Justified
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, b1, b2, rfl,
      (vcup_spec H S1 S2 _).mpr (Or.inl hb1),
      (vcup_spec H S1 S2 _).mpr (Or.inr hb2), rfl⟩))))
  · intro x y hx hy E hE
    obtain ⟨S1, hS1, k1⟩ := hx E hE
    obtain ⟨S2, hS2, k2⟩ := hy E hE
    refine exists_extend H hE (satClosed_cup H hS1 hS2) (fun e he => ?_)
    obtain ⟨b1, hb1⟩ := k1 e he
    obtain ⟨b2, hb2⟩ := k2 e he
    refine ⟨vbit H (b1 = natV H 1 ∨ b2 = natV H 1), ?_⟩
    unfold Justified
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨x, y, b1, b2, rfl,
        (vcup_spec H S1 S2 _).mpr (Or.inl hb1),
        (vcup_spec H S1 S2 _).mpr (Or.inr hb2), rfl⟩)))))
  · intro x hx E hE
    obtain ⟨S1, hS1, k1⟩ := hx (shiftEnvs H A E) (shiftEnvs_isEnvOn H hE)
    refine exists_extend H hE hS1 (fun e he => ?_)
    by_cases hall :
        ∀ d, mem d A → mem (satTriple H x (econs H d e) (natV H 1)) S1
    · refine ⟨natV H 1, ?_⟩
      unfold Justified
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨x, rfl, Or.inl ⟨rfl, hall⟩⟩))))))
    · have hex : ∃ d, mem d A ∧
          ¬ mem (satTriple H x (econs H d e) (natV H 1)) S1 :=
        Classical.byContradiction (fun hcon =>
          hall (fun d hd =>
            Classical.byContradiction (fun hnd => hcon ⟨d, hd, hnd⟩)))
      obtain ⟨d, hd, hnd⟩ := hex
      obtain ⟨b', hb'⟩ :=
        k1 _ (econs_mem_shiftEnvs H he (hE e he) hd)
      have hb0 : b' = natV H 0 := by
        rcases justified_bit H (hS1 _ _ _ hb').2 with h | h
        · exact h
        · exact absurd (h ▸ hb') hnd
      refine ⟨natV H 0, ?_⟩
      unfold Justified
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨x, rfl, Or.inr ⟨rfl, d, hd, hb0 ▸ hb'⟩⟩))))))
  · intro x hx E hE
    obtain ⟨S1, hS1, k1⟩ := hx (shiftEnvs H A E) (shiftEnvs_isEnvOn H hE)
    refine exists_extend H hE hS1 (fun e he => ?_)
    by_cases hall :
        ∀ d, mem d A → mem (satTriple H x (econs H d e) (natV H 0)) S1
    · refine ⟨natV H 0, ?_⟩
      unfold Justified
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, rfl, Or.inl ⟨rfl, hall⟩⟩))))))
    · have hex : ∃ d, mem d A ∧
          ¬ mem (satTriple H x (econs H d e) (natV H 0)) S1 :=
        Classical.byContradiction (fun hcon =>
          hall (fun d hd =>
            Classical.byContradiction (fun hnd => hcon ⟨d, hd, hnd⟩)))
      obtain ⟨d, hd, hnd⟩ := hex
      obtain ⟨b', hb'⟩ :=
        k1 _ (econs_mem_shiftEnvs H he (hE e he) hd)
      have hb1 : b' = natV H 1 := by
        rcases justified_bit H (hS1 _ _ _ hb').2 with h | h
        · exact absurd (h ▸ hb') hnd
        · exact h
      refine ⟨natV H 1, ?_⟩
      unfold Justified
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, rfl, Or.inr ⟨rfl, d, hd, hb1 ▸ hb'⟩⟩))))))

/-- **Totality of satisfaction certificates.**  Every code — including the
nonstandard ones — has a certificate at every environment.

The set structure is the interface under which later modules use this; the
proof does not need the carrier to be nonempty, since a quantifier clause over
an empty carrier is decided by its universal side, and it does not need the
membership relation to consist of pairs at all. -/
theorem certificate_total (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) :
    ∀ c, IsFormCodeSem H c → ∀ e, IsEnvOn H A e →
      ∃ S b, Certifies H A R S c e b := by
  have _ := hS
  intro c hcode e he
  obtain ⟨S, hclosed, hall⟩ :=
    totalOn_of_isFormCodeSem H A R c hcode (vsingle H e)
      (fun u hu => by rw [(vsingle_spec H e u).mp hu]; exact he)
  obtain ⟨b, hb⟩ := hall e ((vsingle_spec H e e).mpr rfl)
  exact ⟨S, b, ⟨hclosed, hb⟩⟩

/-! ## The satisfaction relation

`SatIn` is the payoff.  Totality makes it defined everywhere and
single-valuedness makes the bit it reads off independent of the certificate,
so the two together justify calling it satisfaction rather than an assignment.
`certifies_bit` packages both: the bit of *any* certificate is `vbit` of
`SatIn`, which is the form in which the eight inversion lemmas of
`BoundedZFCConsistency.InternalSat` turn into Tarski clauses. -/

/-- **Internal satisfaction**: some certificate assigns the bit one to the code
`c` under the environment `e`. -/
def SatIn (H : ZFAxioms mem) (A R c e : V) : Prop :=
  ∃ S, Certifies H A R S c e (natV H 1)

/-- Satisfaction is read off any certificate. -/
theorem satIn_iff_bit_eq_one (H : ZFAxioms mem) {A R S c e b : V}
    (hcode : IsFormCodeSem H c) (hcert : Certifies H A R S c e b) :
    SatIn H A R c e ↔ b = natV H 1 := by
  constructor
  · rintro ⟨S', hc'⟩
    exact certificate_functional H A R hcode hcert hc'
  · intro hb
    exact ⟨S, hb ▸ hcert⟩

/-- **The bit of any certificate is the truth bit of `SatIn`.**  This is the
statement that makes `SatIn` a satisfaction relation rather than a name for an
existential. -/
theorem certifies_bit (H : ZFAxioms mem) {A R S c e b : V}
    (hcode : IsFormCodeSem H c) (hcert : Certifies H A R S c e b) :
    b = vbit H (SatIn H A R c e) := by
  by_cases hsat : SatIn H A R c e
  · rw [vbit_pos H hsat]
    exact (satIn_iff_bit_eq_one H hcode hcert).mp hsat
  · rw [vbit_neg H hsat]
    rcases justified_bit H (Certifies.justified H hcert) with h | h
    · exact h
    · exact absurd ((satIn_iff_bit_eq_one H hcode hcert).mpr h) hsat

/-- A certificate carrying exactly the truth bit exists at every code and
environment. -/
theorem exists_certifies (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) {c : V} (hcode : IsFormCodeSem H c) {e : V}
    (he : IsEnvOn H A e) :
    ∃ S, Certifies H A R S c e (vbit H (SatIn H A R c e)) := by
  obtain ⟨S, b, hcert⟩ := certificate_total H hS c hcode e he
  exact ⟨S, certifies_bit H hcode hcert ▸ hcert⟩

/-! ### The Tarski clauses -/

/-- Atomic membership: the structure's relation, read at the two indices. -/
theorem satIn_memAtom (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {e i j : V} (hi : mem i (omegaV H)) (hj : mem j (omegaV H))
    (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 0) (kpair H i j)) e ↔
      mem (kpair H (applyV H e i) (applyV H e j)) R := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_memAtom H hi hj) e he
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_memAtom H hi hj) hcert,
      justified_memAtom H (Certifies.justified H hcert)]
  exact vbit_eq_one H _

/-- Atomic equality: the model's own equality, read at the two indices. -/
theorem satIn_eqAtom (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {e i j : V} (hi : mem i (omegaV H)) (hj : mem j (omegaV H))
    (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 1) (kpair H i j)) e ↔
      applyV H e i = applyV H e j := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_eqAtom H hi hj) e he
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_eqAtom H hi hj) hcert,
      justified_eqAtom H (Certifies.justified H hcert)]
  exact vbit_eq_one H _

/-- Falsity is never satisfied.  No hypothesis is needed: the falsity clause
fixes the bit outright. -/
theorem satIn_bot (H : ZFAxioms mem) {A R e : V} :
    ¬ SatIn H A R (kpair H (natV H 2) (vempty H)) e := by
  rintro ⟨S, hcert⟩
  exact natV_ne H (by decide) (justified_bot H (Certifies.justified H hcert))

/-- Implication. -/
theorem satIn_imp (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c1 c2 e : V} (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (SatIn H A R c1 e → SatIn H A R c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_imp H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := justified_imp H (Certifies.justified H hcert)
  have e1 : b1 = vbit H (SatIn H A R c1 e) :=
    certifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (SatIn H A R c2 e) :=
    certifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (SatIn H A R c1 e) = natV H 1 →
      vbit H (SatIn H A R c2 e) = natV H 1) ↔
      (SatIn H A R c1 e → SatIn H A R c2 e) := by
    constructor
    · exact fun h hs => (vbit_eq_one H _).mp (h ((vbit_eq_one H _).mpr hs))
    · exact fun h hs => (vbit_eq_one H _).mpr (h ((vbit_eq_one H _).mp hs))
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_imp H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-- Conjunction. -/
theorem satIn_and (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c1 c2 e : V} (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (SatIn H A R c1 e ∧ SatIn H A R c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_and H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := justified_and H (Certifies.justified H hcert)
  have e1 : b1 = vbit H (SatIn H A R c1 e) :=
    certifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (SatIn H A R c2 e) :=
    certifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (SatIn H A R c1 e) = natV H 1 ∧
      vbit H (SatIn H A R c2 e) = natV H 1) ↔
      (SatIn H A R c1 e ∧ SatIn H A R c2 e) := by
    constructor
    · exact fun h => ⟨(vbit_eq_one H _).mp h.1, (vbit_eq_one H _).mp h.2⟩
    · exact fun h => ⟨(vbit_eq_one H _).mpr h.1, (vbit_eq_one H _).mpr h.2⟩
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_and H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-- Disjunction. -/
theorem satIn_or (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c1 c2 e : V} (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2)
    (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (SatIn H A R c1 e ∨ SatIn H A R c2 e) := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_or H h1 h2) e he
  obtain ⟨b1, b2, k1, k2, hb⟩ := justified_or H (Certifies.justified H hcert)
  have e1 : b1 = vbit H (SatIn H A R c1 e) :=
    certifies_bit H h1 ⟨hcert.closed, k1⟩
  have e2 : b2 = vbit H (SatIn H A R c2 e) :=
    certifies_bit H h2 ⟨hcert.closed, k2⟩
  have hcong : (vbit H (SatIn H A R c1 e) = natV H 1 ∨
      vbit H (SatIn H A R c2 e) = natV H 1) ↔
      (SatIn H A R c1 e ∨ SatIn H A R c2 e) := by
    constructor
    · exact fun h => h.imp (vbit_eq_one H _).mp (vbit_eq_one H _).mp
    · exact fun h => h.imp (vbit_eq_one H _).mpr (vbit_eq_one H _).mpr
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_or H h1 h2) hcert, hb, e1, e2,
      vbit_congr H hcong]
  exact vbit_eq_one H _

/-- The universal quantifier, ranging over the carrier with the shifted
environment. -/
theorem satIn_all (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c1 e : V} (h1 : IsFormCodeSem H c1) (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 6) c1) e ↔
      ∀ d, mem d A → SatIn H A R c1 (econs H d e) := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_all H h1) e he
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_all H h1) hcert]
  rcases justified_all H (Certifies.justified H hcert) with
    ⟨hb, hall⟩ | ⟨hb, d, hd, hdz⟩
  · exact ⟨fun _ d hd => ⟨S, hcert.closed, hall d hd⟩, fun _ => hb⟩
  · constructor
    · intro hone
      exact absurd (hb.symm.trans hone) (natV_ne H (by decide))
    · intro hforall
      exfalso
      have hz : natV H 0 = vbit H (SatIn H A R c1 (econs H d e)) :=
        certifies_bit H h1 ⟨hcert.closed, hdz⟩
      rw [vbit_pos H (hforall d hd)] at hz
      exact natV_ne H (by decide) hz

/-- The existential quantifier, ranging over the carrier with the shifted
environment. -/
theorem satIn_ex (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c1 e : V} (h1 : IsFormCodeSem H c1) (he : IsEnvOn H A e) :
    SatIn H A R (kpair H (natV H 7) c1) e ↔
      ∃ d, mem d A ∧ SatIn H A R c1 (econs H d e) := by
  obtain ⟨S, b, hcert⟩ :=
    certificate_total H hS _ (isFormCodeSem_ex H h1) e he
  rw [satIn_iff_bit_eq_one H (isFormCodeSem_ex H h1) hcert]
  rcases justified_ex H (Certifies.justified H hcert) with
    ⟨hb, hall⟩ | ⟨hb, d, hd, hdo⟩
  · constructor
    · intro hone
      exact absurd (hb.symm.trans hone) (natV_ne H (by decide))
    · rintro ⟨d, hd, hsat⟩
      exfalso
      have hz : natV H 0 = vbit H (SatIn H A R c1 (econs H d e)) :=
        certifies_bit H h1 ⟨hcert.closed, hall d hd⟩
      rw [vbit_pos H hsat] at hz
      exact natV_ne H (by decide) hz
  · exact ⟨fun _ => ⟨d, hd, ⟨S, hcert.closed, hdo⟩⟩, fun _ => hb⟩

end InternalSatTotality

end BoundedZFCConsistency
end LeanProofs
