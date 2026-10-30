import BoundedZFCConsistency.Basic

/-!
# Recursion along the internal omega, for an arbitrary definable operation

`ZF.Zf` proves a finite-recursion theorem, but only for one fixed step: the
approximation predicate `Approx`, the stage relation `Theta`, and everything
downstream mention the closure operator `gstep H psiC eC` literally.  Nothing in
the argument depends on which operation is iterated, so this module carries the
same development with the step supplied as a parameter, and packages the result
as a genuine recursion theorem: from a seed `a` there is exactly one internal
function on the internal omega with `F 0 = a` and `F (n + 1) = G (F n)`.

## The shape of the parameter

The step cannot be an arbitrary Lean function.  Separation and Replacement carve
out sets by a `Form` with parameters, so the recursion must see the operation as
a *definable functional graph*: a formula `fG` whose two distinguished slots are
the output and the input, an environment `eG` supplying its parameters, and a
Lean-level function `G` with

```text
relOf mem fG eG y x  ↔  y = G x.
```

This is the pattern `ZF.Zf` uses for `psiPS` and `predImg`, sharpened from
"functional" to "the graph of `G`": a bare functionality hypothesis leaves the
operation partial, and a partial step has no total iteration sequence to build.
Functionality of the graph is then a consequence, recorded as `defOp_functional`.
Nothing else about `G` is assumed; in particular it need not be inflationary,
monotone, or set-like.

## What is proved

* **Internal linearity of the omega** — `nat_linear`, with its prerequisite
  `succ_le_of_lt` and the base case `vempty_le_nat`.  These are stated and proved
  first because they are independently useful and the ZF development lacks them;
  the recursion theorem itself does not use them.
* **The parametrized approximations** — `ApproxG` with `ApproxG_base`,
  `ApproxG_extend`, `ApproxG_exists`, and `ApproxG_agree`.
* **Existence** — `omega_recursion`, whose witness `recFun` is the image of the
  internal omega under the definable map `n ↦ ⟨n, F n⟩`.
* **Uniqueness** — `omega_recursion_agree` and `omega_recursion_unique`; two
  solutions agree pointwise on the omega and, being functions with that exact
  domain, are equal as sets.

Uniqueness needs no definability parameter at all: the agreement property
`∀ y y', ⟨n, y⟩ ∈ F → ⟨n, y'⟩ ∈ F' → y = y'` is already a `Form`, so `omega_ind`
applies to it directly.

## De Bruijn bookkeeping

Every formula below carries a table of its de Bruijn slots.  Slot arguments named
`_i` are ABSOLUTE positions in the environment at the use site; `off` marks the
first slot holding the parameter block `eG`, and each additional binder shifts it,
which the call sites account for explicitly.  The convention matches `ZF.Zf`: for
`relOf`, slot `0` is the output, slot `1` the input, and slots `k+2` the
parameters.

Neither Powerset nor Regularity is used, matching the six axioms bundled in
`ZFAxioms`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section OmegaRecursion

variable {V : Type u} {mem : V → V → Prop}

/-! ## Internal linearity of the omega

The arithmetic in `ZF.Zf` stops at transitivity, irreflexivity, and injectivity of
the successor.  Linearity is the next fact any serious internal recursion or
ordering argument wants, and it is proved here by two applications of the
definable-induction schema `omega_ind`.  Each property is written as a `Form`
first, since `omega_ind` takes its induction hypothesis as a formula together
with an environment and not as an arbitrary Lean predicate. -/

/-- "every member of slot `0` has its successor bounded by slot `0`".

| de Bruijn slot | contents                              |
| -------------- | ------------------------------------- |
| `0`            | the successor `s`, then `m`, then `n` |
| `1`            | `m` under the inner binder            |
| `2`            | `n` under both binders                |
| `k+1`          | the caller's slot `k`                 |
-/
def fSuccStepF : Form :=
  fAll (fImp (fMem 0 1)
    (fEx (fAnd (fSuccF 0 1) (fOr (fMem 0 2) (fEq 0 2)))))

theorem fSuccStepF_spec (H : ZFAxioms mem) (n : V) (e : Nat → V) :
    Sat mem (scons n e) fSuccStepF ↔
      ∀ m, mem m n → (mem (vsucc H m) n ∨ vsucc H m = n) := by
  constructor
  · intro h m hm
    obtain ⟨s, hs, hsn⟩ := h m hm
    have hs' : s = vsucc H m :=
      (fSuccF_spec H (scons s (scons m (scons n e))) 0 1).mp hs
    rw [← hs']
    exact hsn
  · intro h m hm
    exact ⟨vsucc H m,
      (fSuccF_spec H (scons (vsucc H m) (scons m (scons n e))) 0 1).mpr rfl,
      h m hm⟩

/-- **The successor bound.**  A member of an internal natural number has its
successor still bounded by that number.  This is the usual prerequisite for
linearity, and it is exactly the step that the transitivity lemma of `ZF.Zf` does
not give. -/
theorem succ_le_of_lt (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) → ∀ m, mem m n →
      (mem (vsucc H m) n ∨ vsucc H m = n) := by
  intro n hn
  refine (fSuccStepF_spec H n (fun _ => vempty H)).mp ?_
  refine omega_ind H fSuccStepF (fun _ => vempty H) ?_ ?_ n hn
  · exact (fSuccStepF_spec H (vempty H) (fun _ => vempty H)).mpr
      (fun m hm => absurd hm (vempty_spec H m))
  · intro k _ IH
    refine (fSuccStepF_spec H (vsucc H k) (fun _ => vempty H)).mpr ?_
    intro m hm
    rcases (vsucc_spec H k m).mp hm with hm | hm
    · rcases (fSuccStepF_spec H k (fun _ => vempty H)).mp IH m hm with h | h
      · exact Or.inl ((vsucc_spec H k (vsucc H m)).mpr (Or.inl h))
      · exact Or.inl ((vsucc_spec H k (vsucc H m)).mpr (Or.inr h))
    · exact Or.inr (by rw [hm])

/-- "the empty set is at most slot `0`".

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the witness `z` for emptiness   |
| `1`            | the induction variable `n`      |
| `k+1`          | the caller's slot `k`           |
-/
def fZeroLeF : Form :=
  fEx (fAnd (fEmptyF 0) (fOr (fMem 0 1) (fEq 0 1)))

theorem fZeroLeF_spec (H : ZFAxioms mem) (n : V) (e : Nat → V) :
    Sat mem (scons n e) fZeroLeF ↔
      (mem (vempty H) n ∨ vempty H = n) := by
  constructor
  · intro ⟨z, hz, hzn⟩
    have hz' : z = vempty H := (fEmptyF_spec H (scons z (scons n e)) 0).mp hz
    rw [← hz']
    exact hzn
  · intro h
    exact ⟨vempty H,
      (fEmptyF_spec H (scons (vempty H) (scons n e)) 0).mpr rfl, h⟩

/-- Zero is the least internal natural number. -/
theorem vempty_le_nat (H : ZFAxioms mem) :
    ∀ n, mem n (omegaV H) → (mem (vempty H) n ∨ vempty H = n) := by
  intro n hn
  refine (fZeroLeF_spec H n (fun _ => vempty H)).mp ?_
  refine omega_ind H fZeroLeF (fun _ => vempty H) ?_ ?_ n hn
  · exact (fZeroLeF_spec H (vempty H) (fun _ => vempty H)).mpr (Or.inr rfl)
  · intro k _ IH
    refine (fZeroLeF_spec H (vsucc H k) (fun _ => vempty H)).mpr ?_
    rcases (fZeroLeF_spec H k (fun _ => vempty H)).mp IH with h | h
    · exact Or.inl ((vsucc_spec H k (vempty H)).mpr (Or.inl h))
    · exact Or.inl ((vsucc_spec H k (vempty H)).mpr (Or.inr h))

/-- "slot `0` is comparable with every member of slot `1`".

| de Bruijn slot | contents                         |
| -------------- | -------------------------------- |
| `0`            | the second natural `n`           |
| `1`            | the induction variable `m`       |
| `2`            | the internal omega               |
-/
def fTrichF : Form :=
  fAll (fImp (fMem 0 2) (fOr (fMem 1 0) (fOr (fEq 1 0) (fMem 0 1))))

theorem fTrichF_spec (H : ZFAxioms mem) (m : V) :
    Sat mem (scons m (fun _ => omegaV H)) fTrichF ↔
      ∀ n, mem n (omegaV H) → (mem m n ∨ m = n ∨ mem n m) := by
  constructor
  · intro h n hn
    exact h n hn
  · intro h n hn
    exact h n hn

/-- **Internal linearity of the omega.**  Any two internal natural numbers are
comparable under the membership ordering.  The proof is induction on the first
argument: the base case is `vempty_le_nat`, and the successor step turns
`m ∈ n` into `succ m ⊆ n` by `succ_le_of_lt`, while the other two cases put `n`
below `succ m` directly. -/
theorem nat_linear (H : ZFAxioms mem) :
    ∀ m, mem m (omegaV H) → ∀ n, mem n (omegaV H) →
      (mem m n ∨ m = n ∨ mem n m) := by
  intro m hm
  refine (fTrichF_spec H m).mp ?_
  refine omega_ind H fTrichF (fun _ => omegaV H) ?_ ?_ m hm
  · refine (fTrichF_spec H (vempty H)).mpr ?_
    intro n hn
    rcases vempty_le_nat H n hn with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro k hk IH
    refine (fTrichF_spec H (vsucc H k)).mpr ?_
    intro n hn
    rcases (fTrichF_spec H k).mp IH n hn with h | h | h
    · rcases succ_le_of_lt H n hn k h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ((vsucc_spec H k n).mpr (Or.inr h.symm)))
    · exact Or.inr (Or.inr ((vsucc_spec H k n).mpr (Or.inl h)))

/-! ## The definable operation

The step of the recursion is a formula together with the Lean function it
defines.  Everything below takes `fG`, `eG`, `G`, and the graph hypothesis `hG`
as explicit parameters, exactly as `ZF.Zf` takes `psiC`, `eC`, and `HSL`. -/

/-- The graph hypothesis makes the defined relation functional; this is the form
Replacement asks for. -/
theorem defOp_functional (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) :
    Functional (relOf mem fG eG) := by
  intro x y1 y2 h1 h2
  rw [(hG y1 x).mp h1, (hG y2 x).mp h2]

/-- "slot `i` = `G` (slot `j`)", with the parameter block of `eG` starting at
slot `off`.  It is the relation formula of `G` renamed into place, so no new
coding is introduced. -/
def fOpF (fG : Form) (i j off : Nat) : Form := fRF fG i j off

theorem fOpF_spec (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x)
    (ee : Nat → V) (i j off : Nat) (hoff : ∀ k, ee (k + off) = eG k) :
    Sat mem ee (fOpF fG i j off) ↔ ee i = G (ee j) :=
  (fRF_spec fG eG ee i j off hoff).trans (hG (ee i) (ee j))

/-! ## The approximation predicate

`ApproxG H G a f m` is `ZF.Zf`'s `Approx` with `gstep H psiC eC` replaced by `G`.
Note that the predicate itself mentions only `G`: the formula `fG` enters solely
through the rendering of clause 5, which is what Separation and Replacement
need. -/

/-- `ApproxG H G a f m`: `f` is (the graph of) a function with domain
`{0, …, m}` recording the iteration `a, G a, G (G a), …`. -/
def ApproxG (H : ZFAxioms mem) (G : V → V) (a f m : V) : Prop :=
  (∀ k y y', mem (kpair H k y) f → mem (kpair H k y') f → y = y') ∧
  (∀ k y, mem (kpair H k y) f → (mem k m ∨ k = m)) ∧
  mem (kpair H (vempty H) a) f ∧
  (∀ k, (mem k m ∨ k = m) → ∃ y, mem (kpair H k y) f) ∧
  (∀ k t y, mem k m → mem (kpair H k t) f → mem (kpair H (vsucc H k) y) f →
    y = G t)

/-- clause 5: the recurrence `f (k+1) = G (f k)`.

| de Bruijn slot | contents                     |
| -------------- | ---------------------------- |
| `0`            | the value `y` at `k+1`       |
| `1`            | the value `t` at `k`         |
| `2`            | the successor of `k`         |
| `3`            | the index `k`                |
| `i+4`          | the caller's slot `i`        |
-/
def fAppG5 (fG : Form) (f_i m_i off : Nat) : Form :=
  fAll (fAll (fAll (fAll
    (fImp (fAnd (fAnd (fAnd (fMem 3 (m_i+4)) (fSuccF 2 3))
                      (fPairMemF 3 1 (f_i+4)))
                (fPairMemF 2 0 (f_i+4)))
          (fOpF fG 0 1 (off+4))))))

theorem fAppG5_spec (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x)
    (ee : Nat → V) (f_i m_i off : Nat) (hoff : ∀ k, ee (k + off) = eG k) :
    Sat mem ee (fAppG5 fG f_i m_i off) ↔
      (∀ k t y, mem k (ee m_i) → mem (kpair H k t) (ee f_i) →
        mem (kpair H (vsucc H k) y) (ee f_i) → y = G t) := by
  constructor
  · intro h k t y hk h1 h2
    have hc : Sat mem (scons y (scons t (scons (vsucc H k) (scons k ee))))
        (fOpF fG 0 1 (off+4)) := by
      apply h k (vsucc H k) t y
      refine ⟨⟨⟨hk, ?_⟩, ?_⟩, ?_⟩
      · exact (fSuccF_spec H
          (scons y (scons t (scons (vsucc H k) (scons k ee)))) 2 3).mpr rfl
      · exact (fPairMemF_spec H
          (scons y (scons t (scons (vsucc H k) (scons k ee)))) 3 1 (f_i+4)).mpr h1
      · exact (fPairMemF_spec H
          (scons y (scons t (scons (vsucc H k) (scons k ee)))) 2 0 (f_i+4)).mpr h2
    exact (fOpF_spec fG eG G hG
      (scons y (scons t (scons (vsucc H k) (scons k ee)))) 0 1 (off+4)
      (fun k0 => hoff k0)).mp hc
  · intro h d d0 d1 d2 hc
    have hc' :
        ((Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fMem 3 (m_i+4)) ∧
          Sat mem (scons d2 (scons d1 (scons d0 (scons d ee)))) (fSuccF 2 3)) ∧
         Sat mem (scons d2 (scons d1 (scons d0 (scons d ee))))
           (fPairMemF 3 1 (f_i+4))) ∧
        Sat mem (scons d2 (scons d1 (scons d0 (scons d ee))))
          (fPairMemF 2 0 (f_i+4)) := hc
    obtain ⟨⟨⟨hk, hsucc⟩, hP1⟩, hP2⟩ := hc'
    have hsucc' : d0 = vsucc H d :=
      (fSuccF_spec H (scons d2 (scons d1 (scons d0 (scons d ee)))) 2 3).mp hsucc
    have hP1' : mem (kpair H d d1) (ee f_i) :=
      (fPairMemF_spec H (scons d2 (scons d1 (scons d0 (scons d ee))))
        3 1 (f_i+4)).mp hP1
    have hP2' : mem (kpair H d0 d2) (ee f_i) :=
      (fPairMemF_spec H (scons d2 (scons d1 (scons d0 (scons d ee))))
        2 0 (f_i+4)).mp hP2
    apply (fOpF_spec fG eG G hG
      (scons d2 (scons d1 (scons d0 (scons d ee)))) 0 1 (off+4)
      (fun k0 => hoff k0)).mpr
    rw [hsucc'] at hP2'
    exact h d d1 d2 hk hP1' hP2'

/-- The full approximation formula.  Clauses 1–4 are literally those of `ZF.Zf`,
which mention no step at all; only clause 5 is parametrized. -/
def fApproxG (fG : Form) (f_i m_i a_i off : Nat) : Form :=
  fAnd (fAppC1 f_i)
       (fAnd (fAppC2 f_i m_i)
             (fAnd (fAppC3 f_i a_i)
                   (fAnd (fAppC4 f_i m_i) (fAppG5 fG f_i m_i off))))

theorem fApproxG_spec (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) (ee : Nat → V)
    (f_i m_i a_i off : Nat)
    (hoff : ∀ k, ee (k + off) = eG k) (ha : ee a_i = a) :
    Sat mem ee (fApproxG fG f_i m_i a_i off) ↔
      ApproxG H G a (ee f_i) (ee m_i) := by
  constructor
  · intro hc
    have hc' : Sat mem ee (fAppC1 f_i) ∧
        (Sat mem ee (fAppC2 f_i m_i) ∧
          (Sat mem ee (fAppC3 f_i a_i) ∧
            (Sat mem ee (fAppC4 f_i m_i) ∧
              Sat mem ee (fAppG5 fG f_i m_i off)))) := hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc'
    refine ⟨(fAppC1_spec H ee f_i).mp h1, (fAppC2_spec H ee f_i m_i).mp h2,
            ?_, (fAppC4_spec H ee f_i m_i).mp h4,
            (fAppG5_spec H fG eG G hG ee f_i m_i off hoff).mp h5⟩
    have := (fAppC3_spec H ee f_i a_i).mp h3
    rwa [ha] at this
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(fAppC1_spec H ee f_i).mpr h1,
            (fAppC2_spec H ee f_i m_i).mpr h2,
            ?_,
            (fAppC4_spec H ee f_i m_i).mpr h4,
            (fAppG5_spec H fG eG G hG ee f_i m_i off hoff).mpr h5⟩
    apply (fAppC3_spec H ee f_i a_i).mpr
    rw [ha]
    exact h3

/-! ### Existence and agreement of approximations -/

/-- The one-point approximation at stage `0`. -/
theorem ApproxG_base (H : ZFAxioms mem) (G : V → V) (a : V) :
    ApproxG H G a (vsingle H (kpair H (vempty H) a)) (vempty H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k y y' h1 h2
    have h1' := (vsingle_spec H (kpair H (vempty H) a) (kpair H k y)).mp h1
    have h2' := (vsingle_spec H (kpair H (vempty H) a) (kpair H k y')).mp h2
    rw [(kpair_inj H k y (vempty H) a h1').2, (kpair_inj H k y' (vempty H) a h2').2]
  · intro k y h
    have h' := (vsingle_spec H (kpair H (vempty H) a) (kpair H k y)).mp h
    exact Or.inr (kpair_inj H k y (vempty H) a h').1
  · exact (vsingle_spec H (kpair H (vempty H) a) (kpair H (vempty H) a)).mpr rfl
  · intro k hk
    rcases hk with hk | hk
    · exact absurd hk (vempty_spec H k)
    · refine ⟨a, ?_⟩
      rw [hk]
      exact (vsingle_spec H (kpair H (vempty H) a) (kpair H (vempty H) a)).mpr rfl
  · intro k t y hk _ _
    exact absurd hk (vempty_spec H k)

/-- Adjoining the single pair `⟨m+1, G t⟩` extends an approximation at stage `m`
whose value there is `t` to one at stage `m+1`. -/
theorem ApproxG_extend (H : ZFAxioms mem) (G : V → V)
    (a : V) (m f t : V) (hm : mem m (omegaV H))
    (hA : ApproxG H G a f m) (hmt : mem (kpair H m t) f) :
    ApproxG H G a
      (vcup H f (vsingle H (kpair H (vsucc H m) (G t))))
      (vsucc H m) := by
  obtain ⟨C1, C2, C3, C4, C5⟩ := hA
  have hf' : ∀ x, mem x (vcup H f (vsingle H (kpair H (vsucc H m) (G t))))
      ↔ (mem x f ∨ x = kpair H (vsucc H m) (G t)) := by
    intro x
    rw [vcup_spec H f (vsingle H (kpair H (vsucc H m) (G t))) x,
        vsingle_spec H (kpair H (vsucc H m) (G t)) x]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- functionality
    intro k y y' h1 h2
    rcases (hf' (kpair H k y)).mp h1 with h1 | h1 <;>
      rcases (hf' (kpair H k y')).mp h2 with h2 | h2
    · exact C1 k y y' h1 h2
    · exfalso
      have hk := (kpair_inj H k y' (vsucc H m) (G t) h2).1
      rw [hk] at h1
      exact succ_not_le H m hm (C2 (vsucc H m) y h1)
    · exfalso
      have hk := (kpair_inj H k y (vsucc H m) (G t) h1).1
      rw [hk] at h2
      exact succ_not_le H m hm (C2 (vsucc H m) y' h2)
    · rw [(kpair_inj H k y (vsucc H m) (G t) h1).2,
          (kpair_inj H k y' (vsucc H m) (G t) h2).2]
  · -- domain bound
    intro k y h
    rcases (hf' (kpair H k y)).mp h with h | h
    · rcases C2 k y h with hk | hk
      · exact Or.inl ((vsucc_spec H m k).mpr (Or.inl hk))
      · exact Or.inl ((vsucc_spec H m k).mpr (Or.inr hk))
    · exact Or.inr (kpair_inj H k y (vsucc H m) (G t) h).1
  · -- base pair
    exact (hf' (kpair H (vempty H) a)).mpr (Or.inl C3)
  · -- domain coverage
    intro k hk
    rcases hk with hk | hk
    · obtain ⟨y, hy⟩ := C4 k ((vsucc_spec H m k).mp hk)
      exact ⟨y, (hf' (kpair H k y)).mpr (Or.inl hy)⟩
    · refine ⟨G t, (hf' _).mpr (Or.inr ?_)⟩
      rw [hk]
  · -- recurrence
    intro k t' y hk h1 h2
    have h1' := (hf' (kpair H k t')).mp h1
    have h2' := (hf' (kpair H (vsucc H k) y)).mp h2
    have hk' := (vsucc_spec H m k).mp hk
    rcases h1' with h1' | h1'
    · rcases h2' with h2' | h2'
      · rcases hk' with hk' | hk'
        · exact C5 k t' y hk' h1' h2'
        · exfalso
          rw [hk'] at h2'
          exact succ_not_le H m hm (C2 (vsucc H m) y h2')
      · obtain ⟨hsk, hy⟩ :=
          kpair_inj H (vsucc H k) y (vsucc H m) (G t) h2'
        have hkm : k = m := succ_inj_nat H m hm k hk' hsk
        rw [hkm] at h1'
        rw [hy, C1 m t' t h1' hmt]
    · obtain ⟨hk'', _⟩ := kpair_inj H k t' (vsucc H m) (G t) h1'
      exfalso
      rw [hk''] at hk'
      exact succ_not_le H m hm hk'

/-- Existence of approximations at every internal stage, by definable induction.
The induction hypothesis is the formula `fEx (fApproxG fG 0 1 2 3)`; its slot `0`
is the approximation, slot `1` the stage, slot `2` the seed, and the parameters
of `eG` start at slot `3`. -/
theorem ApproxG_exists (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    ∀ m, mem m (omegaV H) → ∃ f, ApproxG H G a f m := by
  have hbr : ∀ n : V,
      Sat mem (scons n (scons a eG)) (fEx (fApproxG fG 0 1 2 3)) ↔
        ∃ f, ApproxG H G a f n := by
    intro n
    constructor
    · intro ⟨f, hf⟩
      exact ⟨f, (fApproxG_spec H fG eG G hG a
        (scons f (scons n (scons a eG))) 0 1 2 3 (fun _ => rfl) rfl).mp hf⟩
    · intro ⟨f, hf⟩
      exact ⟨f, (fApproxG_spec H fG eG G hG a
        (scons f (scons n (scons a eG))) 0 1 2 3 (fun _ => rfl) rfl).mpr hf⟩
  intro m hm
  apply (hbr m).mp
  apply omega_ind H (fEx (fApproxG fG 0 1 2 3)) (scons a eG) ?_ ?_ m hm
  · exact (hbr (vempty H)).mpr
      ⟨vsingle H (kpair H (vempty H) a), ApproxG_base H G a⟩
  · intro n hn IH
    apply (hbr (vsucc H n)).mpr
    obtain ⟨f, hf⟩ := (hbr n).mp IH
    obtain ⟨t, ht⟩ := hf.2.2.2.1 n (Or.inr rfl)
    exact ⟨vcup H f (vsingle H (kpair H (vsucc H n) (G t))),
      ApproxG_extend H G a n f t hn hf ht⟩

/-- "the values recorded at slot `0` by slots `1` and `2` agree, up to slot `3`".

| de Bruijn slot | contents                        |
| -------------- | ------------------------------- |
| `0`            | the value `y'` taken by `f'`    |
| `1`            | the value `y` taken by `f`      |
| `2`            | the index `k`                   |
| `3`            | the first approximation `f`     |
| `4`            | the second approximation `f'`   |
| `5`            | the stage `m`                   |
-/
def fApproxAgreeF : Form :=
  fAll (fAll (fImp
    (fAnd (fAnd (fOr (fMem 2 5) (fEq 2 5)) (fPairMemF 2 1 3))
          (fPairMemF 2 0 4))
    (fEq 1 0)))

theorem fApproxAgreeF_spec (H : ZFAxioms mem) (k f f' m : V) (e : Nat → V) :
    Sat mem (scons k (scons f (scons f' (scons m e)))) fApproxAgreeF ↔
      (∀ y y', (mem k m ∨ k = m) →
        mem (kpair H k y) f → mem (kpair H k y') f' → y = y') := by
  constructor
  · intro h y y' hkm h1 h2
    apply h y y'
    refine ⟨⟨hkm, ?_⟩, ?_⟩
    · exact (fPairMemF_spec H
        (scons y' (scons y (scons k (scons f (scons f' (scons m e)))))) 2 1 3).mpr h1
    · exact (fPairMemF_spec H
        (scons y' (scons y (scons k (scons f (scons f' (scons m e)))))) 2 0 4).mpr h2
  · intro h y y' hc
    have hc' : ((mem k m ∨ k = m) ∧
        Sat mem (scons y' (scons y (scons k (scons f (scons f' (scons m e))))))
          (fPairMemF 2 1 3)) ∧
        Sat mem (scons y' (scons y (scons k (scons f (scons f' (scons m e))))))
          (fPairMemF 2 0 4) := hc
    obtain ⟨⟨hkm, hP1⟩, hP2⟩ := hc'
    exact h y y' hkm
      ((fPairMemF_spec H _ 2 1 3).mp hP1)
      ((fPairMemF_spec H _ 2 0 4).mp hP2)

/-- Any two approximations at the same stage agree wherever both are defined. -/
theorem ApproxG_agree (H : ZFAxioms mem) (G : V → V)
    (a : V) (m : V) (hm : mem m (omegaV H)) (f f' : V)
    (hf : ApproxG H G a f m) (hf' : ApproxG H G a f' m) :
    ∀ k, mem k (omegaV H) →
      ∀ y y', (mem k m ∨ k = m) →
        mem (kpair H k y) f → mem (kpair H k y') f' → y = y' := by
  intro k hk
  apply (fApproxAgreeF_spec H k f f' m (fun _ => vempty H)).mp
  apply omega_ind H fApproxAgreeF
    (scons f (scons f' (scons m (fun _ => vempty H)))) ?_ ?_ k hk
  · -- base: both approximations record the seed at `0`
    apply (fApproxAgreeF_spec H (vempty H) f f' m (fun _ => vempty H)).mpr
    intro y y' _ h1 h2
    obtain ⟨C1, _, C3, _, _⟩ := hf
    obtain ⟨C1', _, C3', _, _⟩ := hf'
    calc y = a := C1 (vempty H) y a h1 C3
      _ = y' := (C1' (vempty H) y' a h2 C3').symm
  · -- step: both apply `G` to values already known to agree
    intro n _ IH
    apply (fApproxAgreeF_spec H (vsucc H n) f f' m (fun _ => vempty H)).mpr
    have IH' := (fApproxAgreeF_spec H n f f' m (fun _ => vempty H)).mp IH
    intro y y' hsm h1 h2
    have hnm : mem n m := succ_le_lt H m hm n hsm
    obtain ⟨_, _, _, C4, C5⟩ := hf
    obtain ⟨_, _, _, C4', C5'⟩ := hf'
    obtain ⟨t, ht⟩ := C4 n (Or.inl hnm)
    obtain ⟨t', ht'⟩ := C4' n (Or.inl hnm)
    have htt : t = t' := IH' t t' (Or.inl hnm) ht ht'
    rw [C5 n t y hnm ht h1, C5' n t' y' hnm ht' h2, htt]

/-! ## The stage relation

`ThetaG H G a y m` says that `y` is the value of the iteration at stage `m`.  It
is functional by `ApproxG_agree` and total on the internal omega by
`ApproxG_exists`, which is exactly what is needed to turn it into a set. -/

/-- `y` is the stage-`m` value of the iteration of `G` from `a`. -/
def ThetaG (H : ZFAxioms mem) (G : V → V) (a y m : V) : Prop :=
  mem m (omegaV H) ∧ ∃ f, ApproxG H G a f m ∧ mem (kpair H m y) f

/-- The stage relation as a formula.

| de Bruijn slot | contents                                  |
| -------------- | ----------------------------------------- |
| `0`            | the approximation `f` under the binder    |
| `i+1`          | the caller's slot `i` under that binder   |
-/
def fThetaG (fG : Form) (y_i m_i a_i om_i off : Nat) : Form :=
  fAnd (fMem m_i om_i)
       (fEx (fAnd (fApproxG fG 0 (m_i+1) (a_i+1) (off+1))
                  (fPairMemF (m_i+1) (y_i+1) 0)))

theorem fThetaG_spec (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) (ee : Nat → V)
    (y_i m_i a_i om_i off : Nat)
    (hoff : ∀ k, ee (k + off) = eG k) (ha : ee a_i = a)
    (hom : ee om_i = omegaV H) :
    Sat mem ee (fThetaG fG y_i m_i a_i om_i off) ↔
      ThetaG H G a (ee y_i) (ee m_i) := by
  unfold ThetaG
  constructor
  · intro hc
    have hc' : mem (ee m_i) (ee om_i) ∧
        ∃ f, Sat mem (scons f ee) (fApproxG fG 0 (m_i+1) (a_i+1) (off+1)) ∧
             Sat mem (scons f ee) (fPairMemF (m_i+1) (y_i+1) 0) := hc
    obtain ⟨hm, f, hA, hP⟩ := hc'
    rw [hom] at hm
    refine ⟨hm, f, ?_, ?_⟩
    · exact (fApproxG_spec H fG eG G hG a (scons f ee) 0 (m_i+1) (a_i+1) (off+1)
        (fun k => hoff k) ha).mp hA
    · exact (fPairMemF_spec H (scons f ee) (m_i+1) (y_i+1) 0).mp hP
  · intro ⟨hm, f, hA, hP⟩
    refine ⟨?_, f, ?_, ?_⟩
    · show mem (ee m_i) (ee om_i)
      rw [hom]; exact hm
    · exact (fApproxG_spec H fG eG G hG a (scons f ee) 0 (m_i+1) (a_i+1) (off+1)
        (fun k => hoff k) ha).mpr hA
    · exact (fPairMemF_spec H (scons f ee) (m_i+1) (y_i+1) 0).mpr hP

/-- The parameter block of the recursion: the seed, the internal omega, and then
the parameters of the step formula. -/
noncomputable def envRec (H : ZFAxioms mem) (eG : Nat → V) (a : V) : Nat → V :=
  scons a (scons (omegaV H) eG)

theorem thetaG_zero (H : ZFAxioms mem) (G : V → V) (a : V) :
    ThetaG H G a a (vempty H) :=
  ⟨vempty_in_omega H, vsingle H (kpair H (vempty H) a), ApproxG_base H G a,
    (vsingle_spec H (kpair H (vempty H) a) (kpair H (vempty H) a)).mpr rfl⟩

theorem thetaG_succ (H : ZFAxioms mem) (G : V → V) (a : V) {y n : V}
    (hn : mem n (omegaV H)) (h : ThetaG H G a y n) :
    ThetaG H G a (G y) (vsucc H n) := by
  obtain ⟨_, f, hf, hp⟩ := h
  refine ⟨omega_succ H n hn,
    vcup H f (vsingle H (kpair H (vsucc H n) (G y))),
    ApproxG_extend H G a n f y hn hf hp, ?_⟩
  exact (vcup_spec H f (vsingle H (kpair H (vsucc H n) (G y)))
    (kpair H (vsucc H n) (G y))).mpr
    (Or.inr ((vsingle_spec H _ _).mpr rfl))

theorem thetaG_total (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    ∀ n, mem n (omegaV H) → ∃ y, ThetaG H G a y n := by
  intro n hn
  obtain ⟨f, hf⟩ := ApproxG_exists H fG eG G hG a n hn
  obtain ⟨y, hy⟩ := hf.2.2.2.1 n (Or.inr rfl)
  exact ⟨y, hn, f, hf, hy⟩

theorem thetaG_unique (H : ZFAxioms mem) (G : V → V) (a : V) {y y' n : V}
    (h : ThetaG H G a y n) (h' : ThetaG H G a y' n) : y = y' := by
  obtain ⟨hn, f, hf, hp⟩ := h
  obtain ⟨_, f', hf', hp'⟩ := h'
  exact ApproxG_agree H G a n hn f f' hf hf' n hn y y' (Or.inr rfl) hp hp'

/-! ## The recursion set

Replacement is applied to the definable map `n ↦ ⟨n, F n⟩`, so the resulting set
is the graph itself rather than the set of values. -/

/-- The graph of `n ↦ ⟨n, F n⟩`, as a relation formula over `envRec`.

| de Bruijn slot | contents                    |
| -------------- | --------------------------- |
| `0`            | the stage value `y`         |
| `1`            | the output pair             |
| `2`            | the input stage `n`         |
| `3`            | the seed `a`                |
| `4`            | the internal omega          |
| `k+5`          | the parameter `eG k`        |
-/
def psiGraphG (fG : Form) : Form :=
  fEx (fAnd (fThetaG fG 0 2 3 4 5) (fKPairF 1 2 0))

theorem psiGraphG_rel (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a p n : V) :
    relOf mem (psiGraphG fG) (envRec H eG a) p n ↔
      ∃ y, ThetaG H G a y n ∧ p = kpair H n y := by
  unfold relOf psiGraphG envRec
  constructor
  · intro ⟨y, hT, hk⟩
    refine ⟨y, ?_, ?_⟩
    · exact (fThetaG_spec H fG eG G hG a
        (scons y (scons p (scons n (scons a (scons (omegaV H) eG)))))
        0 2 3 4 5 (fun _ => rfl) rfl rfl).mp hT
    · exact (fKPairF_spec H
        (scons y (scons p (scons n (scons a (scons (omegaV H) eG)))))
        1 2 0).mp hk
  · intro ⟨y, hT, hp⟩
    refine ⟨y, ?_, ?_⟩
    · exact (fThetaG_spec H fG eG G hG a
        (scons y (scons p (scons n (scons a (scons (omegaV H) eG)))))
        0 2 3 4 5 (fun _ => rfl) rfl rfl).mpr hT
    · exact (fKPairF_spec H
        (scons y (scons p (scons n (scons a (scons (omegaV H) eG)))))
        1 2 0).mpr hp

theorem psiGraphG_functional (H : ZFAxioms mem) (fG : Form) (eG : Nat → V)
    (G : V → V) (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    Functional (relOf mem (psiGraphG fG) (envRec H eG a)) := by
  intro n p p' h1 h2
  obtain ⟨y, hT, hp⟩ := (psiGraphG_rel H fG eG G hG a p n).mp h1
  obtain ⟨y', hT', hp'⟩ := (psiGraphG_rel H fG eG G hG a p' n).mp h2
  rw [hp, hp', thetaG_unique H G a hT hT']

/-- **The iteration sequence as a set.**  The image of the internal omega under
the definable map `n ↦ ⟨n, F n⟩`. -/
noncomputable def recFun (H : ZFAxioms mem) (fG : Form) (eG : Nat → V)
    (G : V → V) (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) : V :=
  (H.repl (psiGraphG fG) (envRec H eG a)
    (psiGraphG_functional H fG eG G hG a) (omegaV H)).choose

theorem recFun_spec (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a p : V) :
    mem p (recFun H fG eG G hG a) ↔
      ∃ n, mem n (omegaV H) ∧ ∃ y, ThetaG H G a y n ∧ p = kpair H n y := by
  unfold recFun
  rw [(H.repl (psiGraphG fG) (envRec H eG a)
    (psiGraphG_functional H fG eG G hG a) (omegaV H)).choose_spec p]
  constructor
  · intro ⟨n, hn, hrel⟩
    exact ⟨n, hn, (psiGraphG_rel H fG eG G hG a p n).mp hrel⟩
  · intro ⟨n, hn, hy⟩
    exact ⟨n, hn, (psiGraphG_rel H fG eG G hG a p n).mpr hy⟩

/-- Membership of the graph is exactly the stage relation. -/
theorem recFun_pair (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a n y : V) :
    mem (kpair H n y) (recFun H fG eG G hG a) ↔ ThetaG H G a y n := by
  rw [recFun_spec H fG eG G hG a (kpair H n y)]
  constructor
  · intro ⟨n', hn', y', hT, hk⟩
    obtain ⟨hn, hy⟩ := kpair_inj H n y n' y' hk
    rw [hn, hy]
    exact hT
  · intro hT
    exact ⟨n, hT.1, y, hT, rfl⟩

/-! ## Internal functions and application

A function is a set of Kuratowski pairs that is single-valued, defined on every
element of its domain, and made only of pairs with first component in the domain.
The third clause is what makes two solutions of the recursion *equal* rather than
merely pointwise equal. -/

/-- `F` is (the graph of) a function with domain exactly `d`. -/
def IsFunctionOn (H : ZFAxioms mem) (F d : V) : Prop :=
  (∀ x y y', mem (kpair H x y) F → mem (kpair H x y') F → y = y') ∧
  (∀ x, mem x d → ∃ y, mem (kpair H x y) F) ∧
  (∀ p, mem p F → ∃ x y, mem x d ∧ p = kpair H x y)

/-- "slot `f_i` is a function with domain slot `d_i`".

| de Bruijn slot | contents                                        |
| -------------- | ----------------------------------------------- |
| `0`            | the innermost bound variable of each clause     |
| `1`, `2`       | the outer bound variables of the same clause    |
| `i+n`          | the caller's slot `i` under `n` binders         |
-/
def fFunOnF (f_i d_i : Nat) : Form :=
  fAnd (fAppC1 f_i)
    (fAnd (fAll (fImp (fMem 0 (d_i+1)) (fEx (fPairMemF 1 0 (f_i+2)))))
          (fAll (fImp (fMem 0 (f_i+1))
                  (fEx (fEx (fAnd (fMem 1 (d_i+3)) (fKPairF 2 1 0)))))))

theorem fFunOnF_spec (H : ZFAxioms mem) (ee : Nat → V) (f_i d_i : Nat) :
    Sat mem ee (fFunOnF f_i d_i) ↔ IsFunctionOn H (ee f_i) (ee d_i) := by
  unfold IsFunctionOn
  constructor
  · intro hc
    obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨(fAppC1_spec H ee f_i).mp h1, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := h2 x hx
      exact ⟨y, (fPairMemF_spec H (scons y (scons x ee)) 1 0 (f_i+2)).mp hy⟩
    · intro p hp
      obtain ⟨x, y, hxd, hk⟩ := h3 p hp
      exact ⟨x, y, hxd,
        (fKPairF_spec H (scons y (scons x (scons p ee))) 2 1 0).mp hk⟩
  · intro ⟨h1, h2, h3⟩
    refine ⟨(fAppC1_spec H ee f_i).mpr h1, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := h2 x hx
      exact ⟨y, (fPairMemF_spec H (scons y (scons x ee)) 1 0 (f_i+2)).mpr hy⟩
    · intro p hp
      obtain ⟨x, y, hxd, hk⟩ := h3 p hp
      exact ⟨x, y, hxd,
        (fKPairF_spec H (scons y (scons x (scons p ee))) 2 1 0).mpr hk⟩

/-- The value of `F` at `x` exists whenever `F` records anything there.  Stated
as a conditional existential so that the application operator below is total. -/
theorem applyV_exists (H : ZFAxioms mem) (F x : V) :
    ∃ y, (∃ z, mem (kpair H x z) F) → mem (kpair H x y) F := by
  rcases Classical.em (∃ z, mem (kpair H x z) F) with h | h
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨vempty H, fun h' => absurd h' h⟩

/-- Internal application.  Off the domain it is the empty set; the specification
lemmas below never mention that case. -/
noncomputable def applyV (H : ZFAxioms mem) (F x : V) : V :=
  (applyV_exists H F x).choose

theorem applyV_mem (H : ZFAxioms mem) {F x : V}
    (h : ∃ y, mem (kpair H x y) F) : mem (kpair H x (applyV H F x)) F :=
  (applyV_exists H F x).choose_spec h

/-- On a single-valued set, application inverts membership of the graph: this is
the satisfaction-friendly characterization, since `mem (kpair H x y) F` is
rendered by `fPairMemF`. -/
theorem applyV_eq (H : ZFAxioms mem) {F : V}
    (hfun : ∀ x y y', mem (kpair H x y) F → mem (kpair H x y') F → y = y')
    {x y : V} (h : mem (kpair H x y) F) : applyV H F x = y :=
  hfun x (applyV H F x) y (applyV_mem H ⟨y, h⟩) h

theorem applyV_iff (H : ZFAxioms mem) {F d : V} (hF : IsFunctionOn H F d)
    {x : V} (hx : mem x d) (y : V) :
    mem (kpair H x y) F ↔ applyV H F x = y :=
  ⟨applyV_eq H hF.1, fun h => h ▸ applyV_mem H (hF.2.1 x hx)⟩

/-- "slot `i` is the value of slot `f_i` at slot `j`". -/
def fApplyF (i j f_i : Nat) : Form := fPairMemF j i f_i

theorem fApplyF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j f_i d_i : Nat)
    (hF : IsFunctionOn H (ee f_i) (ee d_i)) (hj : mem (ee j) (ee d_i)) :
    Sat mem ee (fApplyF i j f_i) ↔ ee i = applyV H (ee f_i) (ee j) := by
  rw [fApplyF, fPairMemF_spec H ee j i f_i, applyV_iff H hF hj (ee i)]
  exact eq_comm

/-! ## The recursion theorem -/

theorem recFun_isFunctionOn (H : ZFAxioms mem) (fG : Form) (eG : Nat → V)
    (G : V → V) (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    IsFunctionOn H (recFun H fG eG G hG a) (omegaV H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y y' h1 h2
    exact thetaG_unique H G a
      ((recFun_pair H fG eG G hG a x y).mp h1)
      ((recFun_pair H fG eG G hG a x y').mp h2)
  · intro x hx
    obtain ⟨y, hy⟩ := thetaG_total H fG eG G hG a x hx
    exact ⟨y, (recFun_pair H fG eG G hG a x y).mpr hy⟩
  · intro p hp
    obtain ⟨n, hn, y, _, hk⟩ := (recFun_spec H fG eG G hG a p).mp hp
    exact ⟨n, y, hn, hk⟩

theorem recFun_apply_theta (H : ZFAxioms mem) (fG : Form) (eG : Nat → V)
    (G : V → V) (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V)
    {n : V} (hn : mem n (omegaV H)) :
    ThetaG H G a (applyV H (recFun H fG eG G hG a) n) n := by
  obtain ⟨y, hy⟩ := thetaG_total H fG eG G hG a n hn
  have hmem : mem (kpair H n y) (recFun H fG eG G hG a) :=
    (recFun_pair H fG eG G hG a n y).mpr hy
  have := applyV_mem H (F := recFun H fG eG G hG a) (x := n) ⟨y, hmem⟩
  exact (recFun_pair H fG eG G hG a n _).mp this

theorem recFun_zero (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    applyV H (recFun H fG eG G hG a) (vempty H) = a :=
  thetaG_unique H G a
    (recFun_apply_theta H fG eG G hG a (vempty_in_omega H))
    (thetaG_zero H G a)

theorem recFun_succ (H : ZFAxioms mem) (fG : Form) (eG : Nat → V) (G : V → V)
    (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V)
    {n : V} (hn : mem n (omegaV H)) :
    applyV H (recFun H fG eG G hG a) (vsucc H n)
      = G (applyV H (recFun H fG eG G hG a) n) :=
  thetaG_unique H G a
    (recFun_apply_theta H fG eG G hG a (omega_succ H n hn))
    (thetaG_succ H G a hn (recFun_apply_theta H fG eG G hG a hn))

/-- **Recursion along the internal omega.**  Inside any model of the six ZF
axioms bundled by `ZFAxioms`, every definable operation `G` and every seed `a`
admit an internal function on the internal omega that starts at `a` and iterates
`G`.  The step is definable, not arbitrary: `fG` is its graph formula and `eG`
supplies that formula's parameters. -/
theorem omega_recursion (H : ZFAxioms mem) (fG : Form) (eG : Nat → V)
    (G : V → V) (hG : ∀ y x, relOf mem fG eG y x ↔ y = G x) (a : V) :
    ∃ F, IsFunctionOn H F (omegaV H) ∧ applyV H F (vempty H) = a ∧
      ∀ n, mem n (omegaV H) →
        applyV H F (vsucc H n) = G (applyV H F n) :=
  ⟨recFun H fG eG G hG a, recFun_isFunctionOn H fG eG G hG a,
    recFun_zero H fG eG G hG a, fun _ hn => recFun_succ H fG eG G hG a hn⟩

/-! ### Uniqueness

Agreement of two solutions is itself a definable property, so `omega_ind` applies
to it with no further coding; in particular uniqueness needs neither `fG` nor the
graph hypothesis, only the recurrence. -/

/-- "slots `1` and `2` record the same value at slot `0`".

| de Bruijn slot | contents                       |
| -------------- | ------------------------------ |
| `0`            | the value `y'` taken by `F'`   |
| `1`            | the value `y` taken by `F`     |
| `2`            | the index `n`                  |
| `3`            | the first function `F`         |
| `4`            | the second function `F'`       |
-/
def fAgreeF : Form :=
  fAll (fAll (fImp (fAnd (fPairMemF 2 1 3) (fPairMemF 2 0 4)) (fEq 1 0)))

theorem fAgreeF_spec (H : ZFAxioms mem) (n F F' : V) (e : Nat → V) :
    Sat mem (scons n (scons F (scons F' e))) fAgreeF ↔
      ∀ y y', mem (kpair H n y) F → mem (kpair H n y') F' → y = y' := by
  constructor
  · intro h y y' h1 h2
    apply h y y'
    exact ⟨(fPairMemF_spec H
        (scons y' (scons y (scons n (scons F (scons F' e))))) 2 1 3).mpr h1,
      (fPairMemF_spec H
        (scons y' (scons y (scons n (scons F (scons F' e))))) 2 0 4).mpr h2⟩
  · intro h y y' hc
    have hc' : Sat mem (scons y' (scons y (scons n (scons F (scons F' e)))))
          (fPairMemF 2 1 3) ∧
        Sat mem (scons y' (scons y (scons n (scons F (scons F' e)))))
          (fPairMemF 2 0 4) := hc
    exact h y y'
      ((fPairMemF_spec H _ 2 1 3).mp hc'.1)
      ((fPairMemF_spec H _ 2 0 4).mp hc'.2)

/-- **Pointwise uniqueness.**  Two internal functions on the omega that start at
the same seed and obey the same recurrence take the same value at every internal
natural number. -/
theorem omega_recursion_agree (H : ZFAxioms mem) (G : V → V) (a : V) (F F' : V)
    (hF : IsFunctionOn H F (omegaV H)) (hF0 : applyV H F (vempty H) = a)
    (hFs : ∀ n, mem n (omegaV H) →
      applyV H F (vsucc H n) = G (applyV H F n))
    (hF' : IsFunctionOn H F' (omegaV H)) (hF'0 : applyV H F' (vempty H) = a)
    (hF's : ∀ n, mem n (omegaV H) →
      applyV H F' (vsucc H n) = G (applyV H F' n)) :
    ∀ n, mem n (omegaV H) → applyV H F n = applyV H F' n := by
  have key : ∀ n, mem n (omegaV H) →
      ∀ y y', mem (kpair H n y) F → mem (kpair H n y') F' → y = y' := by
    intro n hn
    apply (fAgreeF_spec H n F F' (fun _ => vempty H)).mp
    apply omega_ind H fAgreeF (scons F (scons F' (fun _ => vempty H))) ?_ ?_ n hn
    · apply (fAgreeF_spec H (vempty H) F F' (fun _ => vempty H)).mpr
      intro y y' h1 h2
      rw [← applyV_eq H hF.1 h1, ← applyV_eq H hF'.1 h2, hF0, hF'0]
    · intro k hk IH
      apply (fAgreeF_spec H (vsucc H k) F F' (fun _ => vempty H)).mpr
      have IH' := (fAgreeF_spec H k F F' (fun _ => vempty H)).mp IH
      intro y y' h1 h2
      have hvk : applyV H F k = applyV H F' k :=
        IH' _ _ (applyV_mem H (hF.2.1 k hk)) (applyV_mem H (hF'.2.1 k hk))
      rw [← applyV_eq H hF.1 h1, ← applyV_eq H hF'.1 h2, hFs k hk, hF's k hk, hvk]
  intro n hn
  exact key n hn _ _ (applyV_mem H (hF.2.1 n hn)) (applyV_mem H (hF'.2.1 n hn))

/-- **Uniqueness.**  Two solutions of the recursion are the same set.  Pointwise
agreement gives the values; the domain clause of `IsFunctionOn` gives that the
solutions contain nothing else, and Extensionality then identifies them. -/
theorem omega_recursion_unique (H : ZFAxioms mem) (G : V → V) (a : V) (F F' : V)
    (hF : IsFunctionOn H F (omegaV H)) (hF0 : applyV H F (vempty H) = a)
    (hFs : ∀ n, mem n (omegaV H) →
      applyV H F (vsucc H n) = G (applyV H F n))
    (hF' : IsFunctionOn H F' (omegaV H)) (hF'0 : applyV H F' (vempty H) = a)
    (hF's : ∀ n, mem n (omegaV H) →
      applyV H F' (vsucc H n) = G (applyV H F' n)) :
    F = F' := by
  have hagree := omega_recursion_agree H G a F F' hF hF0 hFs hF' hF'0 hF's
  apply H.ext
  intro p
  constructor
  · intro hp
    obtain ⟨n, y, hn, hpk⟩ := hF.2.2 p hp
    have hy : applyV H F n = y := applyV_eq H hF.1 (hpk ▸ hp)
    have : mem (kpair H n y) F' := by
      rw [← hy, hagree n hn]
      exact applyV_mem H (hF'.2.1 n hn)
    rw [hpk]
    exact this
  · intro hp
    obtain ⟨n, y, hn, hpk⟩ := hF'.2.2 p hp
    have hy : applyV H F' n = y := applyV_eq H hF'.1 (hpk ▸ hp)
    have : mem (kpair H n y) F := by
      rw [← hy, ← hagree n hn]
      exact applyV_mem H (hF.2.1 n hn)
    rw [hpk]
    exact this

end OmegaRecursion

end BoundedZFCConsistency
end LeanProofs
