import Mathlib.Tactic

/-!
# Jones–Matijasevič 1984, §1–§2: singlefold unary exponential Diophantine representations

An *exponential Diophantine* relation (the paper's (1)) is `A(a) ↔ ∃ x, R(a, x) = S(a, x)` with
`R, S` built from the variables and natural constants by `+`, `·` and exponentiation. It is
*unary* if only the one-place exponential `2^t` is used, and *singlefold* if for every `a` there
is at most one `x`.

Here:

* `UTerm ι`: terms over variables `ι` with `+`, `·` and `2^·`; `ETerm ι`: with general `A^B`;
* `SFU S`: `S` is singlefold unary exponential Diophantine, witnessed by a finite *list* of
  equations in finitely many unknowns (`SFU.single_equation` packs the list into one equation by
  `Σ (lᵢ − rᵢ)² = 0`, written `Σ (lᵢ² + rᵢ²) = Σ 2 lᵢ rᵢ`);
* closure under term equations, conjunction, substitution of parameters by terms, and
  existential quantification over *uniquely determined* values (`SFU.exists_unique`).
-/

namespace JM1984
namespace Exp

/-- Unary exponential terms: `+`, `·`, `2^·`. -/
inductive UTerm (ι : Type)
  | var (i : ι)
  | const (c : ℕ)
  | add (a b : UTerm ι)
  | mul (a b : UTerm ι)
  | pow2 (a : UTerm ι)

/-- General exponential terms: `+`, `·`, `A^B`. -/
inductive ETerm (ι : Type)
  | var (i : ι)
  | const (c : ℕ)
  | add (a b : ETerm ι)
  | mul (a b : ETerm ι)
  | pow (a b : ETerm ι)

namespace UTerm

variable {ι κ : Type}

/-- Evaluation. -/
def eval (v : ι → ℕ) : UTerm ι → ℕ
  | var i => v i
  | const c => c
  | add a b => a.eval v + b.eval v
  | mul a b => a.eval v * b.eval v
  | pow2 a => 2 ^ a.eval v

/-- Substitution of terms for variables. -/
def subst (f : ι → UTerm κ) : UTerm ι → UTerm κ
  | var i => f i
  | const c => const c
  | add a b => add (a.subst f) (b.subst f)
  | mul a b => mul (a.subst f) (b.subst f)
  | pow2 a => pow2 (a.subst f)

theorem eval_subst (f : ι → UTerm κ) (v : κ → ℕ) (t : UTerm ι) :
    (t.subst f).eval v = t.eval (fun i => (f i).eval v) := by
  induction t with
  | var i => rfl
  | const c => rfl
  | add a b iha ihb => simp [subst, eval, iha, ihb]
  | mul a b iha ihb => simp [subst, eval, iha, ihb]
  | pow2 a ih => simp [subst, eval, ih]

/-- A unary term as a general exponential term (`2^t` as the two-place exponential). -/
def toE : UTerm ι → ETerm ι
  | var i => .var i
  | const c => .const c
  | add a b => .add a.toE b.toE
  | mul a b => .mul a.toE b.toE
  | pow2 a => .pow (.const 2) a.toE

instance : Add (UTerm ι) := ⟨add⟩
instance : Mul (UTerm ι) := ⟨mul⟩
instance : OfNat (UTerm ι) n := ⟨const n⟩

@[simp] theorem eval_var (v : ι → ℕ) (i : ι) : (var i).eval v = v i := rfl
@[simp] theorem eval_const (v : ι → ℕ) (c : ℕ) : (const c : UTerm ι).eval v = c := rfl
@[simp] theorem eval_add' (v : ι → ℕ) (a b : UTerm ι) : (a + b).eval v = a.eval v + b.eval v := rfl
@[simp] theorem eval_mul' (v : ι → ℕ) (a b : UTerm ι) : (a * b).eval v = a.eval v * b.eval v := rfl
@[simp] theorem eval_ofNat (v : ι → ℕ) (n : ℕ) : (OfNat.ofNat n : UTerm ι).eval v = n := rfl
@[simp] theorem eval_pow2 (v : ι → ℕ) (a : UTerm ι) : (pow2 a).eval v = 2 ^ a.eval v := rfl

end UTerm

namespace ETerm

variable {ι : Type}

/-- Evaluation. -/
def eval (v : ι → ℕ) : ETerm ι → ℕ
  | var i => v i
  | const c => c
  | add a b => a.eval v + b.eval v
  | mul a b => a.eval v * b.eval v
  | pow a b => a.eval v ^ b.eval v

theorem eval_toE (v : ι → ℕ) (t : UTerm ι) : t.toE.eval v = t.eval v := by
  induction t with
  | var i => rfl
  | const c => rfl
  | add a b iha ihb => simp [UTerm.toE, eval, UTerm.eval, iha, ihb]
  | mul a b iha ihb => simp [UTerm.toE, eval, UTerm.eval, iha, ihb]
  | pow2 a ih => simp [UTerm.toE, eval, UTerm.eval, ih]

end ETerm

open UTerm

/-- A finite system of unary exponential equations holds. -/
def Holds {ι : Type} (E : List (UTerm ι × UTerm ι)) (v : ι → ℕ) : Prop :=
  ∀ e ∈ E, e.1.eval v = e.2.eval v

theorem holds_map {ι κ : Type} (E : List (UTerm ι × UTerm ι)) (f : ι → UTerm κ) (v : κ → ℕ) :
    Holds (E.map (fun e => (e.1.subst f, e.2.subst f))) v ↔ Holds E (fun i => (f i).eval v) := by
  simp only [Holds, List.mem_map]
  constructor
  · intro h e he
    have := h _ ⟨e, he, rfl⟩
    simpa only [eval_subst] using this
  · rintro h _ ⟨e, he, rfl⟩
    simpa only [eval_subst] using h e he

theorem holds_append {ι : Type} (E F : List (UTerm ι × UTerm ι)) (v : ι → ℕ) :
    Holds (E ++ F) v ↔ Holds E v ∧ Holds F v := by
  simp only [Holds, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- Parameters and unknowns joined. -/
def join {α : Type} {m : ℕ} (a : α → ℕ) (x : Fin m → ℕ) : α ⊕ Fin m → ℕ := Sum.elim a x

/-- **Singlefold unary exponential Diophantine**: `S a ↔ ∃ x, E(a, x)`, the `x` being unique. -/
def SFU {α : Type} (S : (α → ℕ) → Prop) : Prop :=
  ∃ (m : ℕ) (E : List (UTerm (α ⊕ Fin m) × UTerm (α ⊕ Fin m))),
    ∀ a, (S a ↔ ∃ x, Holds E (join a x)) ∧
      ∀ x y, Holds E (join a x) → Holds E (join a y) → x = y

namespace SFU

variable {α : Type}

theorem congr {S T : (α → ℕ) → Prop} (h : SFU S) (hST : ∀ a, S a ↔ T a) : SFU T := by
  obtain ⟨m, E, hE⟩ := h
  exact ⟨m, E, fun a => ⟨(hST a).symm.trans (hE a).1, (hE a).2⟩⟩

/-- A term equation. -/
theorem eq (s t : UTerm α) : SFU (fun a => s.eval a = t.eval a) := by
  refine ⟨0, [(s.subst fun i => var (Sum.inl i), t.subst fun i => var (Sum.inl i))], fun a => ⟨?_, ?_⟩⟩
  · constructor
    · intro h; exact ⟨Fin.elim0, by simp [Holds, eval_subst, join, h]⟩
    · rintro ⟨x, hx⟩; simpa [Holds, eval_subst, join] using hx
  · intro x y _ _; funext i; exact Fin.elim0 i

theorem true : SFU (fun _ : α → ℕ => True) :=
  (eq (const 0) (const 0)).congr (by simp)

/-- Conjunction. -/
theorem and {S T : (α → ℕ) → Prop} (hS : SFU S) (hT : SFU T) : SFU (fun a => S a ∧ T a) := by
  obtain ⟨m, E, hE⟩ := hS
  obtain ⟨k, F, hF⟩ := hT
  let fl : α ⊕ Fin m → UTerm (α ⊕ Fin (m + k)) := Sum.elim (fun i => var (Sum.inl i))
    (fun j => var (Sum.inr (Fin.castAdd k j)))
  let fr : α ⊕ Fin k → UTerm (α ⊕ Fin (m + k)) := Sum.elim (fun i => var (Sum.inl i))
    (fun j => var (Sum.inr (Fin.natAdd m j)))
  refine ⟨m + k, E.map (fun e => (e.1.subst fl, e.2.subst fl)) ++
    F.map (fun e => (e.1.subst fr, e.2.subst fr)), fun a => ⟨?_, ?_⟩⟩
  · have key : ∀ z : Fin (m + k) → ℕ, Holds (E.map (fun e => (e.1.subst fl, e.2.subst fl)) ++
        F.map (fun e => (e.1.subst fr, e.2.subst fr))) (join a z) ↔
        Holds E (join a (fun j => z (Fin.castAdd k j))) ∧
          Holds F (join a (fun j => z (Fin.natAdd m j))) := by
      intro z
      have e1 : (fun i => (fl i).eval (join a z)) = join a (fun j => z (Fin.castAdd k j)) := by
        funext i; cases i <;> rfl
      have e2 : (fun i => (fr i).eval (join a z)) = join a (fun j => z (Fin.natAdd m j)) := by
        funext i; cases i <;> rfl
      rw [holds_append, holds_map, holds_map, e1, e2]
    constructor
    · rintro ⟨hs, ht⟩
      obtain ⟨x, hx⟩ := (hE a).1.1 hs
      obtain ⟨y, hy⟩ := (hF a).1.1 ht
      refine ⟨Fin.append x y, (key _).2 ⟨?_, ?_⟩⟩
      · simpa [Fin.append_left] using hx
      · simpa [Fin.append_right] using hy
    · rintro ⟨z, hz⟩
      obtain ⟨h1, h2⟩ := (key z).1 hz
      exact ⟨(hE a).1.2 ⟨_, h1⟩, (hF a).1.2 ⟨_, h2⟩⟩
  · intro z z' hz hz'
    have key : ∀ z : Fin (m + k) → ℕ, Holds (E.map (fun e => (e.1.subst fl, e.2.subst fl)) ++
        F.map (fun e => (e.1.subst fr, e.2.subst fr))) (join a z) →
        Holds E (join a (fun j => z (Fin.castAdd k j))) ∧
          Holds F (join a (fun j => z (Fin.natAdd m j))) := by
      intro z h
      have e1 : (fun i => (fl i).eval (join a z)) = join a (fun j => z (Fin.castAdd k j)) := by
        funext i; cases i <;> rfl
      have e2 : (fun i => (fr i).eval (join a z)) = join a (fun j => z (Fin.natAdd m j)) := by
        funext i; cases i <;> rfl
      rwa [holds_append, holds_map, holds_map, e1, e2] at h
    obtain ⟨a1, a2⟩ := key z hz
    obtain ⟨b1, b2⟩ := key z' hz'
    have hl := (hE a).2 _ _ a1 b1
    have hr := (hF a).2 _ _ a2 b2
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact congrFun hl i
    · exact congrFun hr i

/-- Substitution of terms for the parameters. -/
theorem subst {β : Type} {S : (β → ℕ) → Prop} (hS : SFU S) (f : β → UTerm α) :
    SFU (fun a => S (fun b => (f b).eval a)) := by
  obtain ⟨m, E, hE⟩ := hS
  let g : β ⊕ Fin m → UTerm (α ⊕ Fin m) := Sum.elim (fun b => (f b).subst fun i => var (Sum.inl i))
    (fun j => var (Sum.inr j))
  have hg : ∀ a (x : Fin m → ℕ), (fun i => (g i).eval (join a x)) =
      join (fun b => (f b).eval a) x := by
    intro a x; funext i
    cases i with
    | inl b => simp [g, join, eval_subst]
    | inr j => rfl
  refine ⟨m, E.map (fun e => (e.1.subst g, e.2.subst g)), fun a => ⟨?_, ?_⟩⟩
  · show S (fun b => (f b).eval a) ↔ _
    rw [(hE _).1]
    simp only [holds_map, hg]
  · intro x y hx hy
    rw [holds_map, hg] at hx hy
    exact (hE _).2 x y hx hy

/-- Existential quantification over `k` values determined uniquely by the parameters. -/
theorem exists_unique {k : ℕ} {S : (α ⊕ Fin k → ℕ) → Prop} (hS : SFU S)
    (huniq : ∀ a (y z : Fin k → ℕ), S (join a y) → S (join a z) → y = z) :
    SFU (fun a => ∃ y : Fin k → ℕ, S (join a y)) := by
  obtain ⟨m, E, hE⟩ := hS
  -- parameters `α ⊕ Fin k` become parameters `α` and the first `k` unknowns
  let g : (α ⊕ Fin k) ⊕ Fin m → UTerm (α ⊕ Fin (k + m)) :=
    Sum.elim (Sum.elim (fun i => var (Sum.inl i)) (fun j => var (Sum.inr (Fin.castAdd m j))))
      (fun j => var (Sum.inr (Fin.natAdd k j)))
  have hg : ∀ a (z : Fin (k + m) → ℕ), (fun i => (g i).eval (join a z)) =
      join (join a (fun j => z (Fin.castAdd m j))) (fun j => z (Fin.natAdd k j)) := by
    intro a z; funext i
    rcases i with (i | i) | i <;> rfl
  refine ⟨k + m, E.map (fun e => (e.1.subst g, e.2.subst g)), fun a => ⟨?_, ?_⟩⟩
  · simp only [holds_map, hg]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (hE _).1.1 hy
      exact ⟨Fin.append y x, by simpa [Fin.append_left, Fin.append_right] using hx⟩
    · rintro ⟨z, hz⟩
      exact ⟨_, (hE _).1.2 ⟨_, hz⟩⟩
  · intro z z' hz hz'
    rw [holds_map, hg] at hz hz'
    have hy := huniq a _ _ ((hE _).1.2 ⟨_, hz⟩) ((hE _).1.2 ⟨_, hz'⟩)
    have hz2 := hz
    rw [hy] at hz2
    have hx := (hE _).2 _ _ hz2 hz'
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact congrFun hy i
    · exact congrFun hx i

/-- The left side of the packed equation. -/
def sumSq {ι : Type} (E : List (UTerm ι × UTerm ι)) : UTerm ι :=
  E.foldr (fun e acc => e.1 * e.1 + e.2 * e.2 + acc) (const 0)

/-- The right side of the packed equation. -/
def sumProd {ι : Type} (E : List (UTerm ι × UTerm ι)) : UTerm ι :=
  E.foldr (fun e acc => const 2 * e.1 * e.2 + acc) (const 0)

theorem sumProd_le {ι : Type} (E : List (UTerm ι × UTerm ι)) (v : ι → ℕ) :
    (sumProd E).eval v ≤ (sumSq E).eval v := by
  induction E with
  | nil => simp [sumSq, sumProd]
  | cons e E ih =>
    simp only [sumSq, sumProd, List.foldr_cons, eval_add', eval_mul', eval_const] at ih ⊢
    nlinarith [sq_nonneg ((e.1.eval v : ℤ) - e.2.eval v)]

theorem sumSq_eq_iff {ι : Type} (E : List (UTerm ι × UTerm ι)) (v : ι → ℕ) :
    (sumSq E).eval v = (sumProd E).eval v ↔ Holds E v := by
  induction E with
  | nil => simp [sumSq, sumProd, Holds]
  | cons e E ih =>
    have hle := sumProd_le E v
    simp only [sumSq, sumProd, Holds, List.foldr_cons, eval_add', eval_mul', eval_const,
      List.mem_cons, forall_eq_or_imp] at ih hle ⊢
    rw [← ih]
    set a := e.1.eval v
    set b := e.2.eval v
    have h1 : 2 * a * b ≤ a * a + b * b := by nlinarith [sq_nonneg ((a : ℤ) - b)]
    constructor
    · intro h
      have h2 : a * a + b * b = 2 * a * b := by omega
      have hab : a = b := by
        have hz : ((a : ℤ) - b) ^ 2 = 0 := by
          have := congrArg (fun n : ℕ => (n : ℤ)) h2
          push_cast at this
          nlinarith
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hz
        omega
      exact ⟨hab, by rw [hab] at h h2; omega⟩
    · rintro ⟨hab, h⟩
      rw [hab, h]
      ring

/-- **One equation**: the system packs into `Σ (lᵢ² + rᵢ²) = Σ 2 lᵢ rᵢ`. -/
theorem single_equation {S : (α → ℕ) → Prop} (hS : SFU S) :
    ∃ (m : ℕ) (L R : UTerm (α ⊕ Fin m)), ∀ a,
      (S a ↔ ∃ x, L.eval (join a x) = R.eval (join a x)) ∧
      ∀ x y, L.eval (join a x) = R.eval (join a x) → L.eval (join a y) = R.eval (join a y) →
        x = y := by
  obtain ⟨m, E, hE⟩ := hS
  exact ⟨m, sumSq E, sumProd E, fun a => ⟨by rw [(hE a).1]; simp only [sumSq_eq_iff],
    fun x y hx hy => (hE a).2 x y ((sumSq_eq_iff _ _).1 hx) ((sumSq_eq_iff _ _).1 hy)⟩⟩

end SFU

end Exp
end JM1984
