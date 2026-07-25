import PAFiniteBasisReduction.NonstandardHFFin

/-!
# Finite Skolem hulls for bounded PA syntax

For a raw arithmetic structure and a distinguished point, this file closes
under the arithmetic operations and under one chosen existential witness and
one chosen universal counterexample for every formula below a fixed structural
rank.  The resulting subtype is a `PA.PreModel`, and bounded-rank formulas are
absolute between it and the ambient structure.

The closure is intentionally an inductive, standard-finite-stage closure.
Consequently each of its elements has a finite derivation tree.  The later
proper-cut argument arithmetizes those trees; no meta-level `PA.Model`
induction is used here.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut

/-! ## Rank bounds and canonical finite environments -/

/-- The two symmetric bound steps used by every binary rank case below. -/
private theorem lt_succ_max_left {i a b : Nat} (h : i < a) : i < max a b + 1 :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt h) (Nat.le_max_left _ _))

private theorem lt_succ_max_right {i a b : Nat} (h : i < b) : i < max a b + 1 :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt h) (Nat.le_max_right _ _))

theorem termFree_lt_rank {i : Nat} {t : PA.Term}
    (h : PA.Term.Free i t) : i < termRank t := by
  induction t with
  | var k =>
      simp only [PA.Term.Free] at h
      subst i
      simp [termRank]
  | zero =>
      cases h
  | succ t ih =>
      simp only [PA.Term.Free] at h
      simp only [termRank]
      exact Nat.lt_succ_of_lt (ih h)
  | add a b iha ihb =>
      simp only [PA.Term.Free] at h
      simp only [termRank]
      rcases h with h | h
      · exact lt_succ_max_left (iha h)
      · exact lt_succ_max_right (ihb h)
  | mul a b iha ihb =>
      simp only [PA.Term.Free] at h
      simp only [termRank]
      rcases h with h | h
      · exact lt_succ_max_left (iha h)
      · exact lt_succ_max_right (ihb h)

theorem formulaFree_lt_rank {i : Nat} {phi : PA.Formula}
    (h : PA.Formula.Free i phi) : i < formulaRank phi := by
  induction phi generalizing i with
  | eq a b =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      rcases h with h | h
      · exact lt_succ_max_left (termFree_lt_rank h)
      · exact lt_succ_max_right (termFree_lt_rank h)
  | bot =>
      cases h
  | imp a b iha ihb =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      rcases h with h | h
      · exact lt_succ_max_left (iha h)
      · exact lt_succ_max_right (ihb h)
  | and a b iha ihb =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      rcases h with h | h
      · exact lt_succ_max_left (iha h)
      · exact lt_succ_max_right (ihb h)
  | or a b iha ihb =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      rcases h with h | h
      · exact lt_succ_max_left (iha h)
      · exact lt_succ_max_right (ihb h)
  | all a ih =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      have := ih h
      omega
  | ex a ih =>
      simp only [PA.Formula.Free] at h
      simp only [formulaRank]
      have := ih h
      omega

/-- Replace the irrelevant tail of an environment by zero. -/
def boundedEnv {alpha : Type u} (M : PA.PreModel alpha) (rank : Nat)
    (v : Fin rank → alpha) : Nat → alpha :=
  fun i => if hi : i < rank then v ⟨i, hi⟩ else M.zero

@[simp] theorem boundedEnv_of_lt {alpha : Type u} (M : PA.PreModel alpha)
    {rank i : Nat} (v : Fin rank → alpha) (hi : i < rank) :
    boundedEnv M rank v i = v ⟨i, hi⟩ := by
  simp [boundedEnv, hi]

@[simp] theorem boundedEnv_of_not_lt {alpha : Type u}
    (M : PA.PreModel alpha) {rank i : Nat} (v : Fin rank → alpha)
    (hi : ¬i < rank) :
    boundedEnv M rank v i = M.zero := by
  simp [boundedEnv, hi]

/-- Canonicalize an arbitrary environment at a displayed rank. -/
def canonEnv {alpha : Type u} (M : PA.PreModel alpha) (rank : Nat)
    (e : Nat → alpha) : Nat → alpha :=
  boundedEnv M rank (fun i => e i)

@[simp] theorem canonEnv_of_lt {alpha : Type u} (M : PA.PreModel alpha)
    {rank i : Nat} (e : Nat → alpha) (hi : i < rank) :
    canonEnv M rank e i = e i := by
  simp [canonEnv, hi]

theorem Sat_canonEnv {alpha : Type u} (M : PA.PreModel alpha)
    {rank : Nat} {phi : PA.Formula} (hRank : formulaRank phi ≤ rank)
    (e : Nat → alpha) :
    PA.Formula.Sat M (canonEnv M rank e) phi ↔
      PA.Formula.Sat M e phi := by
  apply PA.Formula.Sat_ext_free M phi
  intro i hi
  exact canonEnv_of_lt M e (Nat.lt_of_lt_of_le (formulaFree_lt_rank hi) hRank)

/-- Canonicalizing the tail below a binder preserves its body. -/
theorem Sat_scons_canonEnv {alpha : Type u} (M : PA.PreModel alpha)
    {rank : Nat} {body : PA.Formula}
    (hRank : formulaRank (PA.Formula.all body) ≤ rank)
    (d : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M (scons d (canonEnv M rank e)) body ↔
      PA.Formula.Sat M (scons d e) body := by
  apply PA.Formula.Sat_ext_free M body
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
      have hFree : PA.Formula.Free i (PA.Formula.all body) := hi
      have hiRank : i < rank :=
        Nat.lt_of_lt_of_le (formulaFree_lt_rank hFree) hRank
      simp [scons, canonEnv_of_lt M e hiRank]

/-! ## Canonical least/default witnesses and counterexamples -/

/-- Under one new universal binder, slot zero is the candidate, slot one is
the proposed output, and the old parameters begin at slot two. -/
def noSmallerGraph (body : PA.Formula) : PA.Formula :=
  PA.Formula.all
    (PA.Formula.imp
      (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1))
      (PA.Formula.imp
        (PA.Formula.rename (SetTheory.up Nat.succ) body)
        PA.Formula.bot))

/-- Graph of the canonical Skolem selector for a predicate `body`.

At an environment `output :: parameters`, the first disjunct says that the
output satisfies `body` and no smaller value does.  The second says that no
value satisfies `body` and the output is zero.  Thus the syntax itself fixes
the intended selector; there is no appeal to an opaque meta-level choice
function in the graph consumed by the later coding argument. -/
def leastDefaultGraph (body : PA.Formula) : PA.Formula :=
  PA.Formula.or
    (PA.Formula.and body (noSmallerGraph body))
    (PA.Formula.and
      (PA.Formula.imp
        (PA.Formula.ex
          (PA.Formula.rename (SetTheory.up Nat.succ) body))
        PA.Formula.bot)
      (PA.Formula.eq (PA.Term.var 0) PA.Term.zero))

/-- The canonical universal counterexample graph is the least/default graph
for the negation of the quantified body. -/
def leastCounterexampleGraph (body : PA.Formula) : PA.Formula :=
  leastDefaultGraph (PA.Formula.imp body PA.Formula.bot)

/-- Exact raw semantics of the fixed least/default graph.  This lemma uses no
arithmetic axioms; totality and uniqueness are deliberately separated below. -/
theorem sat_leastDefaultGraph_iff {alpha : Type u} (M : PA.PreModel alpha)
    (body : PA.Formula) (out : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M (scons out e) (leastDefaultGraph body) ↔
      ((PA.Formula.Sat M (scons out e) body ∧
          ∀ z,
            PA.Formula.Sat M (scons z (scons out e))
                (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) →
              ¬PA.Formula.Sat M (scons z e) body) ∨
        ((¬∃ z, PA.Formula.Sat M (scons z e) body) ∧ out = M.zero)) := by
  simp only [leastDefaultGraph, noSmallerGraph, PA.Formula.Sat]
  constructor
  · intro h
    rcases h with ⟨hout, hleast⟩ | ⟨hnone, hzero⟩
    · left
      refine ⟨hout, ?_⟩
      intro z hlt hz
      apply hleast z hlt
      exact (PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
        (scons z (scons out e))).mpr
        ((PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mpr hz)
    · right
      refine ⟨?_, hzero⟩
      rintro ⟨z, hz⟩
      apply hnone
      refine ⟨z, ?_⟩
      exact (PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
        (scons z (scons out e))).mpr
        ((PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mpr hz)
  · intro h
    rcases h with ⟨hout, hleast⟩ | ⟨hnone, hzero⟩
    · left
      refine ⟨hout, ?_⟩
      intro z hlt hz
      apply hleast z hlt
      exact (PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mp
        ((PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
          (scons z (scons out e))).mp hz)
    · right
      refine ⟨?_, hzero⟩
      rintro ⟨z, hz⟩
      apply hnone
      refine ⟨z, ?_⟩
      exact (PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mp
        ((PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
          (scons z (scons out e))).mp hz)

/-- Semantic assumptions needed from the ambient model to interpret the
fixed least/default graph as a genuine Skolem function.  In a model of PA
these are consequences of the least-number principle.  Keeping them in one
named structure prevents arbitrary choice from being mistaken for a
representable selector. -/
structure CanonicalSelectors {alpha : Type u} (M : PA.PreModel alpha) where
  graph_total : ∀ (body : PA.Formula) (e : Nat → alpha),
    ∃ out, PA.Formula.Sat M (scons out e) (leastDefaultGraph body)
  graph_functional : ∀ (body : PA.Formula) (e : Nat → alpha) {x y},
    PA.Formula.Sat M (scons x e) (leastDefaultGraph body) →
    PA.Formula.Sat M (scons y e) (leastDefaultGraph body) →
    x = y

/-- Value selected by the fixed least/default graph. -/
noncomputable def canonicalValue {alpha : Type u} {M : PA.PreModel alpha}
    (S : CanonicalSelectors M) (body : PA.Formula)
    (e : Nat → alpha) : alpha :=
  Classical.choose (S.graph_total body e)

/-- The selected value satisfies its object-language graph. -/
theorem canonicalValue_graph {alpha : Type u} {M : PA.PreModel alpha}
    (S : CanonicalSelectors M) (body : PA.Formula)
    (e : Nat → alpha) :
    PA.Formula.Sat M (scons (canonicalValue S body e) e)
      (leastDefaultGraph body) :=
  Classical.choose_spec (S.graph_total body e)

/-- The graph is exact: every satisfying output is the selected value. -/
theorem canonicalValue_eq_iff_graph {alpha : Type u}
    {M : PA.PreModel alpha} (S : CanonicalSelectors M)
    (body : PA.Formula) (e : Nat → alpha) (out : alpha) :
    PA.Formula.Sat M (scons out e) (leastDefaultGraph body) ↔
      out = canonicalValue S body e := by
  constructor
  · intro h
    exact S.graph_functional body e h (canonicalValue_graph S body e)
  · rintro rfl
    exact canonicalValue_graph S body e

theorem canonicalValue_spec {alpha : Type u} {M : PA.PreModel alpha}
    (S : CanonicalSelectors M) (body : PA.Formula) (e : Nat → alpha)
    (h : ∃ d, PA.Formula.Sat M (scons d e) body) :
    PA.Formula.Sat M (scons (canonicalValue S body e) e) body := by
  rcases (sat_leastDefaultGraph_iff M body (canonicalValue S body e) e).mp
      (canonicalValue_graph S body e) with hleast | hnone
  · exact hleast.1
  · exact False.elim (hnone.1 h)

theorem canonicalCounterexample_spec {alpha : Type u}
    {M : PA.PreModel alpha} (S : CanonicalSelectors M)
    (body : PA.Formula) (e : Nat → alpha)
    (h : ∃ d, ¬PA.Formula.Sat M (scons d e) body) :
    ¬PA.Formula.Sat M
      (scons (canonicalValue S (PA.Formula.imp body PA.Formula.bot) e) e)
      body := by
  have hex : ∃ d, PA.Formula.Sat M (scons d e)
      (PA.Formula.imp body PA.Formula.bot) := by
    rcases h with ⟨d, hd⟩
    exact ⟨d, hd⟩
  exact canonicalValue_spec S (PA.Formula.imp body PA.Formula.bot) e hex

/-! ## Standard finite Skolem programs -/

/-- Finite expression trees for the hull.  A Skolem node contains one child
program for each of the finitely many canonical environment slots.  This
datatype is external and genuinely standard-finite; it is the source of the
standard program codes used by the later proper-cut argument. -/
inductive Program (rank : Nat) : Type
  | star : Program rank
  | zero : Program rank
  | succ : Program rank → Program rank
  | add : Program rank → Program rank → Program rank
  | mul : Program rank → Program rank → Program rank
  | exSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
      (args : Fin rank → Program rank) : Program rank
  | allSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.all body) ≤ rank)
      (args : Fin rank → Program rank) : Program rank

namespace Program

/-- Interpret a finite Skolem program in the ambient raw structure. -/
noncomputable def eval {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) : Program rank → alpha
  | .star => star
  | .zero => M.zero
  | .succ p => M.succ (eval M S star p)
  | .add p q => M.add (eval M S star p) (eval M S star q)
  | .mul p q => M.mul (eval M S star p) (eval M S star q)
  | .exSkolem body _ args =>
      canonicalValue S body
        (boundedEnv M rank (fun i => eval M S star (args i)))
  | .allSkolem body _ args =>
      canonicalValue S (PA.Formula.imp body PA.Formula.bot)
        (boundedEnv M rank (fun i => eval M S star (args i)))

/-- Environment computed by the children of a Skolem program node. -/
noncomputable def argsEnv {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha)
    (args : Fin rank → Program rank) : Nat → alpha :=
  boundedEnv M rank (fun i => eval M S star (args i))

/-- Exact graph certificate attached to every existential Skolem node. -/
theorem eval_exSkolem_graph {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
    (args : Fin rank → Program rank) :
    PA.Formula.Sat M
      (scons (eval M S star (.exSkolem body hRank args))
        (argsEnv M S star args))
      (leastDefaultGraph body) := by
  exact canonicalValue_graph S body (argsEnv M S star args)

/-- Exact graph certificate attached to every universal-counterexample node. -/
theorem eval_allSkolem_graph {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.all body) ≤ rank)
    (args : Fin rank → Program rank) :
    PA.Formula.Sat M
      (scons (eval M S star (.allSkolem body hRank args))
        (argsEnv M S star args))
      (leastCounterexampleGraph body) := by
  exact canonicalValue_graph S (PA.Formula.imp body PA.Formula.bot)
    (argsEnv M S star args)

/-! ### External polynomial codes -/

/-- Polynomial pairing used for standard program codes. -/
def pairCode (a b : Nat) : Nat :=
  (a + b) * (a + b) + a

/-- A positive pairing node.  The offset makes both children strictly smaller
even in the degenerate `(0,0)` case. -/
def nodeCode (a b : Nat) : Nat := pairCode a b + 1

theorem pairCode_injective {a b c d : Nat}
    (h : pairCode a b = pairCode c d) : a = c ∧ b = d := by
  let s := a + b
  let t := c + d
  have ha : a ≤ s := by simp [s]
  have hc : c ≤ t := by simp [t]
  have hsEq : s = t := by
    rcases Nat.lt_trichotomy s t with hst | hst | hts
    · have hst' : s + 1 ≤ t := hst
      have hsquare : (s + 1) * (s + 1) ≤ t * t :=
        Nat.mul_le_mul hst' hst'
      have hgap : s * s + a < (s + 1) * (s + 1) := by
        calc
          s * s + a ≤ s * s + s := Nat.add_le_add_left ha (s * s)
          _ < (s + 1) * (s + 1) := by
            simp only [Nat.add_mul, Nat.mul_add]
            omega
      have hpLt : pairCode a b < pairCode c d := by
        calc
          pairCode a b = s * s + a := by simp [pairCode, s]
          _ < (s + 1) * (s + 1) := hgap
          _ ≤ t * t := hsquare
          _ ≤ t * t + c := Nat.le_add_right _ _
          _ = pairCode c d := by simp [pairCode, t]
      exact False.elim ((Nat.ne_of_lt hpLt) h)
    · exact hst
    · have hts' : t + 1 ≤ s := hts
      have htSquare : (t + 1) * (t + 1) ≤ s * s :=
        Nat.mul_le_mul hts' hts'
      have hgap : t * t + c < (t + 1) * (t + 1) := by
        calc
          t * t + c ≤ t * t + t := Nat.add_le_add_left hc (t * t)
          _ < (t + 1) * (t + 1) := by
            simp only [Nat.add_mul, Nat.mul_add]
            omega
      have hpLt : pairCode c d < pairCode a b := by
        calc
          pairCode c d = t * t + c := by simp [pairCode, t]
          _ < (t + 1) * (t + 1) := hgap
          _ ≤ s * s := htSquare
          _ ≤ s * s + a := Nat.le_add_right _ _
          _ = pairCode a b := by simp [pairCode, s]
      exact False.elim ((Nat.ne_of_lt hpLt) h.symm)
  have hac : a = c := by
    have h' : s * s + a = t * t + c := by
      simpa [pairCode, s, t] using h
    rw [hsEq] at h'
    exact Nat.add_left_cancel h'
  exact ⟨hac, by omega⟩

theorem nodeCode_injective {a b c d : Nat}
    (h : nodeCode a b = nodeCode c d) : a = c ∧ b = d := by
  apply pairCode_injective
  exact Nat.add_right_cancel h

theorem left_lt_nodeCode (a b : Nat) : a < nodeCode a b := by
  simp only [nodeCode, pairCode]
  omega

theorem right_lt_nodeCode (a b : Nat) : b < nodeCode a b := by
  let s := a + b
  have hb : b ≤ s := by simp [s]
  by_cases hs : s = 0
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    simp [nodeCode, pairCode, ha0, hb0]
  · have hsOne : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
    have hsSquare : s ≤ s * s := by
      simpa using Nat.mul_le_mul_left s hsOne
    have : b ≤ s * s + a :=
      Nat.le_trans hb (Nat.le_trans hsSquare (Nat.le_add_right _ _))
    simpa [nodeCode, pairCode, s] using Nat.lt_succ_of_le this

/-- Self-delimiting code of a finite list of natural-number fields. -/
def listCode : List Nat → Nat
  | [] => 0
  | x :: xs => nodeCode x (listCode xs)

theorem listCode_cons_pos (x : Nat) (xs : List Nat) :
    0 < listCode (x :: xs) := by
  simp only [listCode]
  exact Nat.zero_lt_of_lt (left_lt_nodeCode x (listCode xs))

theorem listCode_injective : Function.Injective listCode := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          apply False.elim
          apply (Nat.ne_of_lt (listCode_cons_pos y ys))
          simpa only [listCode] using h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          apply False.elim
          apply (Nat.ne_of_lt (listCode_cons_pos x xs))
          simpa only [listCode] using h.symm
      | cons y ys =>
          simp only [listCode] at h
          rcases nodeCode_injective h with ⟨hxy, htail⟩
          subst y
          exact congrArg (List.cons x) (ih htail)

theorem list_member_lt_code {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x < listCode xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      simp only [listCode]
      rcases h with rfl | h
      · exact left_lt_nodeCode _ (listCode ys)
      · exact Nat.lt_trans (ih h) (right_lt_nodeCode y (listCode ys))

theorem ofFn_injective {beta : Type} {n : Nat}
    {f g : Fin n → beta} (h : List.ofFn f = List.ofFn g) : f = g := by
  funext i
  have hi := congrArg (fun xs : List beta => xs[i.val]?) h
  simpa [List.getElem?_ofFn, i.isLt] using hi

/-- Code a fixed-length vector by first exposing its standard finite list. -/
def vectorCode {n : Nat} (v : Fin n → Nat) : Nat :=
  listCode (List.ofFn v)

theorem vectorCode_injective {n : Nat} :
    Function.Injective (@vectorCode n) := by
  intro f g h
  apply ofFn_injective
  exact listCode_injective h

theorem vector_entry_lt_code {n : Nat} (v : Fin n → Nat) (i : Fin n) :
    v i < vectorCode v := by
  apply list_member_lt_code
  exact (List.mem_ofFn).mpr ⟨i, rfl⟩

private theorem idxOf_injective_of_mem {beta : Type}
    [BEq beta] [LawfulBEq beta] {xs : List beta} {a b : beta}
    (ha : a ∈ xs) (hb : b ∈ xs) (hidx : xs.idxOf a = xs.idxOf b) :
    a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases hax : a = x
      · subst a
        by_cases hbx : b = x
        · exact hbx.symm
        · have hxb : x ≠ b := fun h => hbx h.symm
          have hbeq : (x == b) = false :=
            beq_eq_false_iff_ne.mpr hxb
          simp [List.idxOf_cons, hbeq] at hidx
      · by_cases hbx : b = x
        · subst b
          have hxa : x ≠ a := fun h => hax h.symm
          have hbeq : (x == a) = false :=
            beq_eq_false_iff_ne.mpr hxa
          simp [List.idxOf_cons, hbeq] at hidx
        · have hxa : x ≠ a := fun h => hax h.symm
          have hxb : x ≠ b := fun h => hbx h.symm
          have hbeqa : (x == a) = false :=
            beq_eq_false_iff_ne.mpr hxa
          have hbeqb : (x == b) = false :=
            beq_eq_false_iff_ne.mpr hxb
          apply ih
          · simpa [hax, hxa] using ha
          · simpa [hbx, hxb] using hb
          · simpa [List.idxOf_cons, hbeqa, hbeqb] using hidx

/-- Compile a rank-bounded formula to its position in the already checked
finite enumeration.  The evaluator will dispatch on this finite index rather
than interpret Gödel-coded PA syntax. -/
def formulaIndex (rank : Nat) (body : PA.Formula) : Nat :=
  (formulasOfRankAtMost rank).idxOf body

theorem formulaIndex_injective_of_rank {rank : Nat} {a b : PA.Formula}
    (ha : formulaRank a ≤ rank) (hb : formulaRank b ≤ rank)
    (h : formulaIndex rank a = formulaIndex rank b) : a = b := by
  apply idxOf_injective_of_mem
  · exact (mem_formulasOfRankAtMost rank a).mpr ha
  · exact (mem_formulasOfRankAtMost rank b).mpr hb
  · exact h

/-- Standard polynomial code of a finite Skolem expression.  Tags `0`
through `6` distinguish the constructors; Skolem nodes carry a finite formula
index and a fixed-length vector of child codes. -/
def code : Program rank → Nat
  | .star => nodeCode 0 0
  | .zero => nodeCode 1 0
  | .succ p => nodeCode 2 (code p)
  | .add p q => nodeCode 3 (nodeCode (code p) (code q))
  | .mul p q => nodeCode 4 (nodeCode (code p) (code q))
  | .exSkolem body _ args =>
      nodeCode 5
        (nodeCode (formulaIndex rank body)
          (vectorCode (fun i => code (args i))))
  | .allSkolem body _ args =>
      nodeCode 6
        (nodeCode (formulaIndex rank body)
          (vectorCode (fun i => code (args i))))

/-- Outer constructor tag of a program. -/
def tag : Program rank → Nat
  | .star => 0
  | .zero => 1
  | .succ _ => 2
  | .add _ _ => 3
  | .mul _ _ => 4
  | .exSkolem _ _ _ => 5
  | .allSkolem _ _ _ => 6

/-- Payload paired with the outer constructor tag. -/
def payload : Program rank → Nat
  | .star => 0
  | .zero => 0
  | .succ p => code p
  | .add p q => nodeCode (code p) (code q)
  | .mul p q => nodeCode (code p) (code q)
  | .exSkolem body _ args =>
      nodeCode (formulaIndex rank body)
        (vectorCode (fun i => code (args i)))
  | .allSkolem body _ args =>
      nodeCode (formulaIndex rank body)
        (vectorCode (fun i => code (args i)))

theorem code_eq_node_tag_payload (p : Program rank) :
    code p = nodeCode (tag p) (payload p) := by
  cases p <;> rfl

theorem code_eq_iff_tag_payload_eq {p q : Program rank} :
    code p = code q ↔ tag p = tag q ∧ payload p = payload q := by
  rw [code_eq_node_tag_payload, code_eq_node_tag_payload]
  constructor
  · exact nodeCode_injective
  · rintro ⟨htag, hpayload⟩
    rw [htag, hpayload]

/-- Polynomial program coding is injective. -/
theorem code_injective {rank : Nat} : Function.Injective (@code rank) := by
  intro p q hcode
  induction p generalizing q with
  | star =>
      have htag := (code_eq_iff_tag_payload_eq.mp hcode).1
      cases q <;> simp [tag] at htag ⊢
  | zero =>
      have htag := (code_eq_iff_tag_payload_eq.mp hcode).1
      cases q <;> simp [tag] at htag ⊢
  | succ p ih =>
      have hparts := code_eq_iff_tag_payload_eq.mp hcode
      cases q with
      | succ q =>
          apply congrArg Program.succ
          apply ih
          simpa [payload] using hparts.2
      | _ => simp [tag] at hparts
  | add left right ihLeft ihRight =>
      have hparts := code_eq_iff_tag_payload_eq.mp hcode
      cases q with
      | add r s =>
          have hpayload :
              nodeCode (code left) (code right) =
                nodeCode (code r) (code s) := by
            simpa [payload] using hparts.2
          rcases nodeCode_injective hpayload with ⟨hpr, hqs⟩
          rw [ihLeft hpr, ihRight hqs]
      | _ => simp [tag] at hparts
  | mul left right ihLeft ihRight =>
      have hparts := code_eq_iff_tag_payload_eq.mp hcode
      cases q with
      | mul r s =>
          have hpayload :
              nodeCode (code left) (code right) =
                nodeCode (code r) (code s) := by
            simpa [payload] using hparts.2
          rcases nodeCode_injective hpayload with ⟨hpr, hqs⟩
          rw [ihLeft hpr, ihRight hqs]
      | _ => simp [tag] at hparts
  | exSkolem body hRank args ih =>
      have hparts := code_eq_iff_tag_payload_eq.mp hcode
      cases q with
      | exSkolem body' hRank' args' =>
          have hpayload : nodeCode
                (formulaIndex rank body)
                (vectorCode (fun i => code (args i))) =
              nodeCode
                (formulaIndex rank body')
                (vectorCode (fun i => code (args' i))) := by
            simpa [payload] using hparts.2
          rcases nodeCode_injective hpayload with ⟨hbodyCode, hargsCode⟩
          have hbodyRank : formulaRank body ≤ rank := by
            simp only [formulaRank] at hRank
            omega
          have hbodyRank' : formulaRank body' ≤ rank := by
            simp only [formulaRank] at hRank'
            omega
          have hbody : body = body' :=
            formulaIndex_injective_of_rank hbodyRank hbodyRank' hbodyCode
          subst body'
          have hcodes : (fun i => code (args i)) =
              (fun i => code (args' i)) :=
            vectorCode_injective hargsCode
          have hargs : args = args' := by
            funext i
            exact ih i (congrFun hcodes i)
          subst args'
          rfl
      | _ => simp [tag] at hparts
  | allSkolem body hRank args ih =>
      have hparts := code_eq_iff_tag_payload_eq.mp hcode
      cases q with
      | allSkolem body' hRank' args' =>
          have hpayload : nodeCode
                (formulaIndex rank body)
                (vectorCode (fun i => code (args i))) =
              nodeCode
                (formulaIndex rank body')
                (vectorCode (fun i => code (args' i))) := by
            simpa [payload] using hparts.2
          rcases nodeCode_injective hpayload with ⟨hbodyCode, hargsCode⟩
          have hbodyRank : formulaRank body ≤ rank := by
            simp only [formulaRank] at hRank
            omega
          have hbodyRank' : formulaRank body' ≤ rank := by
            simp only [formulaRank] at hRank'
            omega
          have hbody : body = body' :=
            formulaIndex_injective_of_rank hbodyRank hbodyRank' hbodyCode
          subst body'
          have hcodes : (fun i => code (args i)) =
              (fun i => code (args' i)) :=
            vectorCode_injective hargsCode
          have hargs : args = args' := by
            funext i
            exact ih i (congrFun hcodes i)
          subst args'
          rfl
      | _ => simp [tag] at hparts

/-- Meta-level partial decoder for the polynomial code image.  The later PA
trace relation does not execute this decoder; it is provided here to state the
external coding theorem cleanly. -/
noncomputable def decode (rank : Nat) (n : Nat) : Option (Program rank) :=
  by
    classical
    exact if h : ∃ p : Program rank, code p = n
      then some (Classical.choose h)
      else none

@[simp] theorem decode_code (p : Program rank) :
    decode rank (code p) = some p := by
  unfold decode
  split
  · rename_i h
    apply congrArg some
    exact code_injective (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨p, rfl⟩)

theorem decode_eq_some_iff (n : Nat) (p : Program rank) :
    decode rank n = some p ↔ code p = n := by
  constructor
  · intro hdecode
    unfold decode at hdecode
    split at hdecode
    · rename_i h
      have hp : Classical.choose h = p := Option.some.inj hdecode
      rw [← hp]
      exact Classical.choose_spec h
    · contradiction
  · intro hcode
    rw [← hcode]
    exact decode_code p

theorem code_succ_child_lt (p : Program rank) :
    code p < code (.succ p) := by
  exact right_lt_nodeCode 2 (code p)

theorem code_add_left_lt (p q : Program rank) :
    code p < code (.add p q) := by
  exact Nat.lt_trans
    (left_lt_nodeCode (code p) (code q))
    (right_lt_nodeCode 3 (nodeCode (code p) (code q)))

theorem code_add_right_lt (p q : Program rank) :
    code q < code (.add p q) := by
  exact Nat.lt_trans
    (right_lt_nodeCode (code p) (code q))
    (right_lt_nodeCode 3 (nodeCode (code p) (code q)))

theorem code_mul_left_lt (p q : Program rank) :
    code p < code (.mul p q) := by
  exact Nat.lt_trans
    (left_lt_nodeCode (code p) (code q))
    (right_lt_nodeCode 4 (nodeCode (code p) (code q)))

theorem code_mul_right_lt (p q : Program rank) :
    code q < code (.mul p q) := by
  exact Nat.lt_trans
    (right_lt_nodeCode (code p) (code q))
    (right_lt_nodeCode 4 (nodeCode (code p) (code q)))

theorem code_ex_child_lt (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
    (args : Fin rank → Program rank) (i : Fin rank) :
    code (args i) < code (.exSkolem body hRank args) := by
  apply Nat.lt_trans (vector_entry_lt_code
    (fun j => code (args j)) i)
  apply Nat.lt_trans
    (right_lt_nodeCode (formulaIndex rank body)
      (vectorCode (fun j => code (args j))))
  exact right_lt_nodeCode 5
    (nodeCode (formulaIndex rank body)
      (vectorCode (fun j => code (args j))))

theorem code_all_child_lt (body : PA.Formula)
    (hRank : formulaRank (PA.Formula.all body) ≤ rank)
    (args : Fin rank → Program rank) (i : Fin rank) :
    code (args i) < code (.allSkolem body hRank args) := by
  apply Nat.lt_trans (vector_entry_lt_code
    (fun j => code (args j)) i)
  apply Nat.lt_trans
    (right_lt_nodeCode (formulaIndex rank body)
      (vectorCode (fun j => code (args j))))
  exact right_lt_nodeCode 6
    (nodeCode (formulaIndex rank body)
      (vectorCode (fun j => code (args j))))

end Program

/-! ## The standard-stage hull and its induced raw arithmetic structure -/

/-- The least closure containing `star`, the arithmetic constants and
operations, and the selected bounded-rank quantifier witnesses. -/
inductive Hull {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha) : alpha → Prop
  | star : Hull M S rank star star
  | zero : Hull M S rank star M.zero
  | succ {a : alpha} : Hull M S rank star a →
      Hull M S rank star (M.succ a)
  | add {a b : alpha} : Hull M S rank star a → Hull M S rank star b →
      Hull M S rank star (M.add a b)
  | mul {a b : alpha} : Hull M S rank star a → Hull M S rank star b →
      Hull M S rank star (M.mul a b)
  | exSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.ex body) ≤ rank)
      (v : Fin rank → alpha)
      (hv : ∀ i, Hull M S rank star (v i)) :
      Hull M S rank star
        (canonicalValue S body (boundedEnv M rank v))
  | allSkolem (body : PA.Formula)
      (hRank : formulaRank (PA.Formula.all body) ≤ rank)
      (v : Fin rank → alpha)
      (hv : ∀ i, Hull M S rank star (v i)) :
      Hull M S rank star
        (canonicalValue S (PA.Formula.imp body PA.Formula.bot)
          (boundedEnv M rank v))

/-- Every standard finite program evaluates to an element of the inductively
generated hull. -/
theorem Program.eval_mem_hull {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) :
    ∀ p : Program rank, Hull M S rank star (Program.eval M S star p)
  | .star => Hull.star
  | .zero => Hull.zero
  | .succ p => Hull.succ (Program.eval_mem_hull M S star p)
  | .add p q => Hull.add
      (Program.eval_mem_hull M S star p)
      (Program.eval_mem_hull M S star q)
  | .mul p q => Hull.mul
      (Program.eval_mem_hull M S star p)
      (Program.eval_mem_hull M S star q)
  | .exSkolem body hRank args =>
      Hull.exSkolem body hRank
        (fun i => Program.eval M S star (args i))
        (fun i => Program.eval_mem_hull M S star (args i))
  | .allSkolem body hRank args =>
      Hull.allSkolem body hRank
        (fun i => Program.eval M S star (args i))
        (fun i => Program.eval_mem_hull M S star (args i))

/-- Conversely, every hull element is denoted by a standard finite program.
Together with `Program.eval_mem_hull`, this identifies the inductive closure
with the image of the concrete expression datatype. -/
theorem Hull.exists_program {alpha : Type u} {M : PA.PreModel alpha}
    {S : CanonicalSelectors M} {rank : Nat} {star x : alpha}
    (h : Hull M S rank star x) :
    ∃ p : Program rank, Program.eval M S star p = x := by
  induction h with
  | star => exact ⟨Program.star, rfl⟩
  | zero => exact ⟨Program.zero, rfl⟩
  | succ h ih =>
      rcases ih with ⟨p, rfl⟩
      exact ⟨Program.succ p, rfl⟩
  | add ha hb iha ihb =>
      rcases iha with ⟨p, rfl⟩
      rcases ihb with ⟨q, rfl⟩
      exact ⟨Program.add p q, rfl⟩
  | mul ha hb iha ihb =>
      rcases iha with ⟨p, rfl⟩
      rcases ihb with ⟨q, rfl⟩
      exact ⟨Program.mul p q, rfl⟩
  | exSkolem body hRank v hv ih =>
      classical
      let args : Fin rank → Program rank := fun i => Classical.choose (ih i)
      have hargs :
          (fun i : Fin rank => Program.eval M S star (args i)) = v := by
        funext i
        exact Classical.choose_spec (ih i)
      refine ⟨Program.exSkolem body hRank args, ?_⟩
      simp only [Program.eval]
      rw [hargs]
  | allSkolem body hRank v hv ih =>
      classical
      let args : Fin rank → Program rank := fun i => Classical.choose (ih i)
      have hargs :
          (fun i : Fin rank => Program.eval M S star (args i)) = v := by
        funext i
        exact Classical.choose_spec (ih i)
      refine ⟨Program.allSkolem body hRank args, ?_⟩
      simp only [Program.eval]
      rw [hargs]

/-- Carrier of the induced bounded-rank Skolem hull. -/
abbrev Carrier {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha) : Type u :=
  {a : alpha // Hull M S rank star a}

/-- The arithmetic reduct on the Skolem hull. -/
noncomputable def preModel {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha) :
    PA.PreModel (Carrier M S rank star) where
  zero := ⟨M.zero, Hull.zero⟩
  succ a := ⟨M.succ a.val, Hull.succ a.property⟩
  add a b := ⟨M.add a.val b.val, Hull.add a.property b.property⟩
  mul a b := ⟨M.mul a.val b.val, Hull.mul a.property b.property⟩

@[simp] theorem preModel_zero_val {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha) :
    (preModel M S rank star).zero.val = M.zero := rfl

@[simp] theorem preModel_succ_val {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (a : Carrier M S rank star) :
    ((preModel M S rank star).succ a).val = M.succ a.val := rfl

@[simp] theorem preModel_add_val {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (a b : Carrier M S rank star) :
    ((preModel M S rank star).add a b).val = M.add a.val b.val := rfl

@[simp] theorem preModel_mul_val {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (a b : Carrier M S rank star) :
    ((preModel M S rank star).mul a b).val = M.mul a.val b.val := rfl

/-- Evaluation in the subtype model is ambient evaluation followed by the
subtype inclusion. -/
theorem termEval_val {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (e : Nat → Carrier M S rank star)
    (t : PA.Term) :
    (PA.Term.eval (preModel M S rank star) e t).val =
      PA.Term.eval M (fun i => (e i).val) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => simp only [PA.Term.eval, preModel_succ_val, ih]
  | add a b iha ihb =>
      simp only [PA.Term.eval, preModel_add_val, iha, ihb]
  | mul a b iha ihb =>
      simp only [PA.Term.eval, preModel_mul_val, iha, ihb]

/-- The subtype inclusion commutes with extending an environment. -/
theorem Sat_valEnv_scons {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (phi : PA.Formula) (d : Carrier M S rank star)
    (e : Nat → Carrier M S rank star) :
    PA.Formula.Sat M (fun i => (scons d e i).val) phi ↔
      PA.Formula.Sat M (scons d.val (fun i => (e i).val)) phi := by
  apply PA.Formula.Sat_ext M phi
  intro i
  cases i <;> rfl

/-! ## Bounded-rank elementarity -/

/-- Every formula below the closure rank has exactly the same truth value in
the induced hull and in the ambient raw structure. -/
theorem sat_iff_ambient {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (rank : Nat) (star : alpha)
    (phi : PA.Formula) (hRank : formulaRank phi ≤ rank)
    (e : Nat → Carrier M S rank star) :
    PA.Formula.Sat (preModel M S rank star) e phi ↔
      PA.Formula.Sat M (fun i => (e i).val) phi := by
  induction phi generalizing e with
  | eq a b =>
      simp only [PA.Formula.Sat]
      constructor
      · intro h
        simpa only [termEval_val] using congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        simpa only [termEval_val] using h
  | bot =>
      exact Iff.rfl
  | imp a b iha ihb =>
      simp only [PA.Formula.Sat]
      have ha : formulaRank a ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank a ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_left _ _
        omega
      have hb : formulaRank b ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank b ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_right _ _
        omega
      exact ⟨
        fun hab haRaw => (ihb hb _).mp (hab ((iha ha _).mpr haRaw)),
        fun hab haHull => (ihb hb _).mpr (hab ((iha ha _).mp haHull))⟩
  | and a b iha ihb =>
      simp only [PA.Formula.Sat]
      have ha : formulaRank a ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank a ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_left _ _
        omega
      have hb : formulaRank b ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank b ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_right _ _
        omega
      exact and_congr (iha ha _) (ihb hb _)
  | or a b iha ihb =>
      simp only [PA.Formula.Sat]
      have ha : formulaRank a ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank a ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_left _ _
        omega
      have hb : formulaRank b ≤ rank := by
        simp only [formulaRank] at hRank
        have hmax : formulaRank b ≤ Nat.max (formulaRank a) (formulaRank b) :=
          Nat.le_max_right _ _
        omega
      exact or_congr (iha ha _) (ihb hb _)
  | all body ih =>
      simp only [PA.Formula.Sat]
      have hbody : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      constructor
      · intro hHull d
        by_cases hd : PA.Formula.Sat M
            (scons d (fun i => (e i).val)) body
        · exact hd
        · exfalso
          let rawE : Nat → alpha := fun i => (e i).val
          let canonical := canonEnv M rank rawE
          have hFailCanonical :
              ∃ x, ¬PA.Formula.Sat M (scons x canonical) body := by
            refine ⟨d, ?_⟩
            intro hdCanonical
            apply hd
            exact (Sat_scons_canonEnv M hRank d rawE).mp hdCanonical
          let c : alpha := canonicalValue S
            (PA.Formula.imp body PA.Formula.bot) canonical
          have hcHull : Hull M S rank star c := by
            change Hull M S rank star
              (canonicalValue S (PA.Formula.imp body PA.Formula.bot)
                (boundedEnv M rank (fun i : Fin rank => rawE i)))
            exact Hull.allSkolem body hRank
              (fun i : Fin rank => rawE i) (fun i => (e i).property)
          let cHull : Carrier M S rank star := ⟨c, hcHull⟩
          have hcAmbient :
              PA.Formula.Sat M (scons c rawE) body :=
            (Sat_valEnv_scons M S rank star body cHull e).mp
              ((ih hbody (scons cHull e)).mp (hHull cHull))
          have hcCanonical :
              PA.Formula.Sat M (scons c canonical) body :=
            (Sat_scons_canonEnv M hRank c rawE).mpr hcAmbient
          exact (canonicalCounterexample_spec S body canonical
            hFailCanonical) hcCanonical
      · intro hAmbient d
        apply (ih hbody (scons d e)).mpr
        exact (Sat_valEnv_scons M S rank star body d e).mpr
          (hAmbient d.val)
  | ex body ih =>
      simp only [PA.Formula.Sat]
      have hbody : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      constructor
      · rintro ⟨d, hd⟩
        refine ⟨d.val, ?_⟩
        exact (Sat_valEnv_scons M S rank star body d e).mp
          ((ih hbody (scons d e)).mp hd)
      · intro hAmbient
        let rawE : Nat → alpha := fun i => (e i).val
        let canonical := canonEnv M rank rawE
        have hExistsCanonical :
            ∃ x, PA.Formula.Sat M (scons x canonical) body := by
          rcases hAmbient with ⟨d, hd⟩
          refine ⟨d, ?_⟩
          exact (Sat_scons_canonEnv M hRank d rawE).mpr hd
        let w : alpha := canonicalValue S body canonical
        have hwHull : Hull M S rank star w := by
          change Hull M S rank star
            (canonicalValue S body
              (boundedEnv M rank (fun i : Fin rank => rawE i)))
          exact Hull.exSkolem body hRank
            (fun i : Fin rank => rawE i) (fun i => (e i).property)
        let wHull : Carrier M S rank star := ⟨w, hwHull⟩
        refine ⟨wHull, (ih hbody (scons wHull e)).mpr ?_⟩
        apply (Sat_valEnv_scons M S rank star body wHull e).mpr
        exact (Sat_scons_canonEnv M hRank w rawE).mp
          (canonicalValue_spec S body canonical hExistsCanonical)

/-! ## A rank large enough for the actual sealed fragment axioms -/

def maxFormulaRank : List PA.Formula → Nat
  | [] => 0
  | phi :: rest => Nat.max (formulaRank phi) (maxFormulaRank rest)

theorem formulaRank_le_maxFormulaRank {phi : PA.Formula}
    {fs : List PA.Formula} (h : phi ∈ fs) :
    formulaRank phi ≤ maxFormulaRank fs := by
  induction fs with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      simp only [maxFormulaRank]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Semantic closure rank for the finite list that exactly enumerates the
canonical PA rank fragment. -/
def fragmentSemanticRank (n : Nat) : Nat :=
  maxFormulaRank (paRankFragmentAxioms n)

theorem fragment_axiom_rank_le {n : Nat} {phi : PA.Formula}
    (h : PARankFragment n phi) :
    formulaRank phi ≤ fragmentSemanticRank n := by
  apply formulaRank_le_maxFormulaRank
  exact (mem_paRankFragmentAxioms n phi).mpr h

/-- Any ambient raw structure satisfying the displayed PA axioms transfers
the whole canonical rank fragment to its finite-Skolem hull. -/
theorem hull_sat_rankFragment {alpha : Type u} (M : PA.PreModel alpha)
    (S : CanonicalSelectors M) (star : alpha) (n : Nat)
    (hPA : ∀ (e : Nat → alpha) (f : PA.Formula),
      PA.Formula.Ax_s f → PA.Formula.Sat M e f)
    (e : Nat → Carrier M S (fragmentSemanticRank n) star) :
    ∀ f, PARankFragment n f →
      PA.Formula.Sat (preModel M S (fragmentSemanticRank n) star) e f := by
  intro f hf
  apply (sat_iff_ambient M S (fragmentSemanticRank n) star f
    (fragment_axiom_rank_le hf) e).mpr
  exact hPA (fun i => (e i).val) f (paRankFragment_subset_ax_s hf)

end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
