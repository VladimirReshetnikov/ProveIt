/-!
# Logic & Foundations Optimizations
# Repository: ProveIt
# Specialist: Logic & Foundations Specialist
# Scope: Logic/PeanoArithmetic, Computability/CombinatoryLogic, Logic/PresburgerArithmetic, Logic/Interpretability

This file contains verified, golfed, and structurally optimized formalizations
extracted during the audit of the Logic & Foundations modules in ProveIt:
1. **Peano Arithmetic Successor Model** (Richard Dedekind 1888, Giuseppe Peano 1889):
   - Categorical impossibility of finite models for the Dedekind-Peano successor axioms.
2. **Combinatory Logic & SKI Calculus** (Moses Schönfinkel 1924, Haskell Curry 1930):
   - Pure constructive 3-step self-cycle certificate for the self-replicating Omega combinator.
3. **Presburger Arithmetic & Cooper Quantifier Elimination** (Mojżesz Presburger 1929, D. C. Cooper 1972):
   - Affine form normalization scaling tails by L / |a| and reducing leading coefficients to sign.
4. **Arithmetization of Syntax & Sequence Coding** (Kurt Gödel 1931):
   - Conditional sequence decoding inversion theorem for arithmetic coding schemes.
-/

universe u

open Function

/-! =========================================================================
    1. Peano Arithmetic: NoFiniteModel Golfing & Elimination of Proof Bulk
    ========================================================================= -/

namespace ProveIt.Optimizations.NoFiniteModel

/-- A dependency-free equivalence between a type and a finite ordinal `Fin n`. -/
structure FinEquiv (α : Type u) (n : Nat) where
  /-- The forward mapping from `α` to `Fin n`. -/
  toFun : α → Fin n
  /-- The inverse mapping from `Fin n` to `α`. -/
  invFun : Fin n → α
  /-- Proof that `invFun` is a left inverse of `toFun`. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- Proof that `invFun` is a right inverse of `toFun`. -/
  right_inv : ∀ i, toFun (invFun i) = i

namespace FinEquiv

/-- The forward map of a `FinEquiv` is injective. -/
theorem toFun_injective {α : Type u} {n : Nat} (e : FinEquiv α n) :
    Injective e.toFun :=
  fun x y h => (e.left_inv x).symm.trans ((congrArg e.invFun h).trans (e.left_inv y))

/-- The inverse map of a `FinEquiv` is injective. -/
theorem invFun_injective {α : Type u} {n : Nat} (e : FinEquiv α n) :
    Injective e.invFun :=
  fun i j h => (e.right_inv i).symm.trans ((congrArg e.toFun h).trans (e.right_inv j))

/-- Identity equivalence between `Fin n` and itself. -/
def refl (n : Nat) : FinEquiv (Fin n) n where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end FinEquiv

/-- Explicit constructive finiteness asserting equivalence with some `Fin n`. -/
def IsFiniteType (α : Type u) : Prop :=
  ∃ n : Nat, Nonempty (FinEquiv α n)

/-- Transposition of zero with `a` in `Fin (n + 1)`. -/
def swapZero {n : Nat} (a x : Fin (n + 1)) : Fin (n + 1) :=
  if x = 0 then a else if x = a then 0 else x

/-- `swapZero a` is an involution on `Fin (n + 1)` whenever `a ≠ 0`. -/
theorem swapZero_involutive {n : Nat} {a : Fin (n + 1)} (ha : a ≠ 0)
    (x : Fin (n + 1)) : swapZero a (swapZero a x) = x := by
  by_cases hx0 : x = 0
  · subst hx0; simp [swapZero, ha]
  · by_cases hxa : x = a
    · subst hxa; simp [swapZero, ha]
    · simp [swapZero, hx0, hxa]

/-- `swapZero a` is injective on `Fin (n + 1)` since it is an involution. -/
theorem swapZero_injective {n : Nat} {a : Fin (n + 1)} (ha : a ≠ 0) :
    Injective (swapZero a) :=
  fun _ _ h => (swapZero_involutive ha _).symm.trans ((congrArg _ h).trans (swapZero_involutive ha _))

/-- A constructive finite pigeonhole argument: injective endomaps of `Fin n` are surjective. -/
theorem fin_surjective_of_injective :
    ∀ {n : Nat} (f : Fin n → Fin n), Injective f → Surjective f := by
  intro n
  induction n with
  | zero =>
      intro f _ y
      exact Fin.elim0 y
  | succ n ih =>
      intro f hf
      have normalized :
          ∀ (k : Fin (n + 1) → Fin (n + 1)), Injective k → k 0 = 0 →
            Surjective k := by
        intro k hk hk0
        have hnonzero : ∀ i : Fin n, k i.succ ≠ 0 := by
          intro i hi
          have hsame : k i.succ = k 0 := hi.trans hk0.symm
          exact Fin.succ_ne_zero i (hk hsame)
        let g : Fin n → Fin n := fun i => (k i.succ).pred (hnonzero i)
        have hg : Injective g := by
          intro i j hij
          apply Fin.succ_inj.mp
          apply hk
          calc
            k i.succ = ((k i.succ).pred (hnonzero i)).succ :=
              (Fin.succ_pred (k i.succ) (hnonzero i)).symm
            _ = ((k j.succ).pred (hnonzero j)).succ := congrArg Fin.succ hij
            _ = k j.succ := Fin.succ_pred (k j.succ) (hnonzero j)
        have hgsurj : Surjective g := ih g hg
        intro y
        by_cases hy : y = 0
        · subst y
          exact ⟨0, hk0⟩
        · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hy
          obtain ⟨i, hi⟩ := hgsurj j
          refine ⟨i.succ, ?_⟩
          calc
            k i.succ = ((k i.succ).pred (hnonzero i)).succ :=
              (Fin.succ_pred (k i.succ) (hnonzero i)).symm
            _ = j.succ := congrArg Fin.succ hi
            _ = y := hj.symm
      by_cases hf0 : f 0 = 0
      · exact normalized f hf hf0
      · let h : Fin (n + 1) → Fin (n + 1) :=
          fun i => swapZero (f 0) (f i)
        have hh0 : h 0 = 0 := by
          simp [h, swapZero, hf0]
        have hhinj : Injective h := by
          intro i j hij
          exact hf (swapZero_injective hf0 hij)
        have hhsurj : Surjective h := normalized h hhinj hh0
        intro y
        obtain ⟨i, hi⟩ := hhsurj (swapZero (f 0) y)
        refine ⟨i, ?_⟩
        exact swapZero_injective hf0 hi

/-- Any injective endomap on a type equivalent to `Fin n` is surjective. -/
theorem surjective_of_injective_of_equiv_fin {α : Type u} {n : Nat}
    (e : FinEquiv α n) (f : α → α) (hf : Injective f) : Surjective f := by
  let g : Fin n → Fin n := fun i => e.toFun (f (e.invFun i))
  have hg : Injective g := by
    intro i j hij
    apply e.invFun_injective
    apply hf
    exact e.toFun_injective hij
  have hgsurj : Surjective g := fin_surjective_of_injective g hg
  intro y
  obtain ⟨i, hi⟩ := hgsurj (e.toFun y)
  refine ⟨e.invFun i, ?_⟩
  apply e.toFun_injective
  simpa [g] using hi

/-- Any injective endomap on a constructively finite type is surjective. -/
theorem finite_self_surjective_of_injective {α : Type u}
    (hfinite : IsFiniteType α) (f : α → α) (hf : Injective f) :
    Surjective f := by
  rcases hfinite with ⟨n, ⟨e⟩⟩
  exact surjective_of_injective_of_equiv_fin e f hf

/-- A finite carrier cannot possess an injective successor map that misses zero. -/
theorem finite_carrier_cannot_have_injective_successor_missing_zero
    {α : Type u} (hfinite : IsFiniteType α) (zero : α) (succ : α → α)
    (hsucc_injective : Function.Injective succ)
    (hzero_not_succ : ∀ a, succ a ≠ zero) : False :=
  let ⟨a, ha⟩ := finite_self_surjective_of_injective hfinite succ hsucc_injective zero
  hzero_not_succ a ha

/-- Shallow Peano Arithmetic model structure specifying the Dedekind-Peano successor axioms:
    designated zero element, successor endomap, injectivity of successor, and exclusion of zero from the image
    (Richard Dedekind 1888, Giuseppe Peano 1889). Does not require induction or arithmetic schemas. -/
structure ShallowPAModel (α : Type u) where
  /-- The designated zero element of the model. -/
  zero : α
  /-- The successor endomap of the model. -/
  succ : α → α
  /-- Injectivity of the successor map. -/
  succ_injective : ∀ {a b}, succ a = succ b → a = b
  /-- Proof that zero is not in the image of the successor map. -/
  zero_not_succ : ∀ a, succ a ≠ zero

/-- The carrier type of any shallow Peano Arithmetic model cannot be finite. -/
theorem model_carrier_not_finite {α : Type u} (M : ShallowPAModel α) :
    ¬ IsFiniteType α :=
  fun hfinite => finite_carrier_cannot_have_injective_successor_missing_zero
    hfinite M.zero M.succ (fun _ _ h => M.succ_injective h) M.zero_not_succ

/-- **No Finite Model Theorem for Peano Successor Axioms** (Dedekind 1888, Peano 1889):
    There is no finite carrier type equipped with a shallow PA model satisfying the successor axioms. -/
theorem no_finite_PA_model :
    ¬ ∃ (α : Type u), ∃ _M : ShallowPAModel α, IsFiniteType α :=
  fun ⟨_, M, hfinite⟩ => model_carrier_not_finite M hfinite

end ProveIt.Optimizations.NoFiniteModel


/-! =========================================================================
    2. Combinatory Logic: SKI Reduction & Omega Self-Cycle Proof Golfing
    ========================================================================= -/

namespace ProveIt.Optimizations.CombinatoryLogic

namespace Reduction

/-- Reflexive-transitive closure of a binary relation `r`. -/
inductive Star {α : Type u} (r : α → α → Prop) (a : α) : α → Prop where
  /-- Reflexivity: `Star r a a`. -/
  | refl : Star r a a
  /-- Right-extension step: `Star r a b → r b c → Star r a c`. -/
  | tail {b c : α} : Star r a b → r b c → Star r a c

/-- Transitive (positive) closure of a binary relation `r`. -/
inductive Plus {α : Type u} (r : α → α → Prop) (a : α) : α → Prop where
  /-- Base step embedding `r a b` into `Plus r a b`. -/
  | single {b : α} : r a b → Plus r a b
  /-- Right-extension step: `Plus r a b → r b c → Plus r a c`. -/
  | tail {b c : α} : Plus r a b → r b c → Plus r a c

namespace Plus

/-- Inclusion of the transitive closure `Plus` into the reflexive-transitive closure `Star`. -/
theorem toStar {α : Type u} {r : α → α → Prop} {a b : α} (h : Plus r a b) : Star r a b := by
  induction h with
  | single step => exact Star.tail Star.refl step
  | tail _ step ih => exact Star.tail ih step

/-- Transitivity of the positive closure `Plus`. -/
theorem trans {α : Type u} {r : α → α → Prop} {a b c : α}
    (hab : Plus r a b) (hbc : Plus r b c) : Plus r a c := by
  induction hbc with
  | single step => exact .tail hab step
  | tail _ step ih => exact .tail ih step

end Plus

end Reduction

namespace SKI

/-- Terms of the pure SKI combinatory calculus. -/
inductive Term where
  /-- The `S` combinator: `S x y z → x z (y z)`. -/
  | s
  /-- The `K` combinator: `K x y → x`. -/
  | k
  /-- The `I` combinator: `I x → x`. -/
  | i
  /-- Application of a function term to an argument term. -/
  | app (function argument : Term)
  deriving DecidableEq, Repr

/-- Left-associative application notation `⬝` for SKI terms. -/
infixl:70 " ⬝ " => Term.app

/-- Small-step reduction relation for SKI combinatory terms. -/
inductive Step : Term → Term → Prop where
  /-- `I`-reduction rule: `I ⬝ x → x`. -/
  | i (x : Term) : Step (Term.i ⬝ x) x
  /-- `K`-reduction rule: `K ⬝ x ⬝ y → x`. -/
  | k (x y : Term) : Step (Term.k ⬝ x ⬝ y) x
  /-- `S`-reduction rule: `S ⬝ x ⬝ y ⬝ z → x ⬝ z ⬝ (y ⬝ z)`. -/
  | s (x y z : Term) : Step (Term.s ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  /-- Congruence rule reducing the left-hand function term. -/
  | appLeft (argument : Term) {function function' : Term}
      (step : Step function function') :
      Step (function ⬝ argument) (function' ⬝ argument)
  /-- Congruence rule reducing the right-hand argument term. -/
  | appRight (function : Term) {argument argument' : Term}
      (step : Step argument argument') :
      Step (function ⬝ argument) (function ⬝ argument')

/-- Multi-step (reflexive-transitive) reduction relation on SKI terms. -/
abbrev Steps := Reduction.Star Step

/-- Multi-step (transitive, at least one step) reduction relation on SKI terms. -/
abbrev StepsPlus := Reduction.Plus Step

/-- The kernel term `S ⬝ I ⬝ I` used to construct the self-replicating omega combinator. -/
def omegaKernel : Term := Term.s ⬝ Term.i ⬝ Term.i

/-- The self-replicating omega combinator `(S ⬝ I ⬝ I) ⬝ (S ⬝ I ⬝ I)`. -/
def omega : Term := omegaKernel ⬝ omegaKernel

/--
**Three-Step Self-Replication of the Omega Combinator** (Moses Schönfinkel 1924, Haskell Curry 1930):
`omega = (S ⬝ I ⬝ I) ⬝ (S ⬝ I ⬝ I)` reduces to itself in exactly three genuine SKI steps.
Verified by a 3-step constructive pipeline requiring 0 non-standard axioms.
-/
theorem omega_cycle : StepsPlus omega omega :=
  (Reduction.Plus.single (.s .i .i omegaKernel)).tail
    (.appLeft (Term.i ⬝ omegaKernel) (.i omegaKernel)) |>.tail
    (.appRight omegaKernel (.i omegaKernel))

end SKI

end ProveIt.Optimizations.CombinatoryLogic


/-! =========================================================================
    3. Presburger Arithmetic: Cooper Normalization Golfing
    ========================================================================= -/

namespace ProveIt.Optimizations.Presburger

/-- Affine linear form represented by an integer constant and a list of variable coefficients
    in Presburger arithmetic (Mojżesz Presburger 1929, D. C. Cooper 1972). -/
structure Affine where
  /-- Constant term of the affine form. -/
  const : Int
  /-- Coefficients of the variables in the affine form. -/
  coeffs : List Int
  deriving DecidableEq, Repr

/-- Leading coefficient of the affine form, defaulting to `0` if empty. -/
def Affine.head (t : Affine) : Int :=
  t.coeffs.head?.getD 0

/-- Remainder of the affine form with the leading coefficient dropped. -/
def Affine.tail (t : Affine) : Affine where
  const := t.const
  coeffs := t.coeffs.tail

/-- Prepend a new leading coefficient `c` to an affine form. -/
def Affine.consCoeff (c : Int) (t : Affine) : Affine where
  const := t.const
  coeffs := c :: t.coeffs

/-- Scale all coefficients and the constant term by an integer factor `s`. -/
def Affine.scale (s : Int) (t : Affine) : Affine where
  const := s * t.const
  coeffs := t.coeffs.map (s * ·)

/-- Normalizes an affine form `a * x + c * y + k` in D. C. Cooper's (1972) quantifier elimination algorithm
    for Presburger arithmetic (Cooper 1972):
    scales the tail (constant and remaining variable coefficients) by `L / |a|` (where `L` is the LCM
    of the leading coefficient absolute values across all constraints) and replaces the leading coefficient
    with its sign `t.head.sign ∈ {-1, 0, 1}`. -/
def normalizeAffine (L : Nat) (t : Affine) : Affine :=
  if t.head = 0 then Affine.consCoeff 0 t.tail
  else
    Affine.consCoeff t.head.sign (t.tail.scale (L / t.head.natAbs : Nat))

/--
**Head Normalization Certificate for Cooper's Algorithm** (D. C. Cooper 1972):
The leading coefficient of `normalizeAffine L t` is `0` if `t.head = 0`, and `t.head.sign` otherwise.
Definitional split reduces both branches directly via `rfl`.
-/
@[simp] theorem head_normalizeAffine (L : Nat) (t : Affine) :
    (normalizeAffine L t).head = if t.head = 0 then 0 else t.head.sign := by
  unfold normalizeAffine
  split <;> rfl

end ProveIt.Optimizations.Presburger


/-! =========================================================================
    4. Peano Arithmetic: PAListCoding Cleaned Reductions
    ========================================================================= -/

namespace ProveIt.Optimizations.PAListCoding

/-- **Sequence Decoding Inversion Theorem** (Kurt Gödel 1931):
    Decoding an encoded sequence yields the original sequence.
    Conditionality disclosure: this abstract inversion theorem is explicitly conditional
    on the encoding being injective (`hinj`), validity of all encoded objects (`hvalid`), and
    decoding soundness on valid code representations (`hdec`). -/
theorem decode_encode {SeqCode : Type u} (encode : List Nat → SeqCode) (decode : SeqCode → List Nat)
    (IsValidCode : SeqCode → Prop)
    (hinj : Injective encode)
    (hvalid : ∀ xs, IsValidCode (encode xs))
    (hdec : ∀ {p}, IsValidCode p → encode (decode p) = p)
    (xs : List Nat) : decode (encode xs) = xs :=
  hinj (hdec (hvalid xs))

end ProveIt.Optimizations.PAListCoding

