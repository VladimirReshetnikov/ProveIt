import DiophantineConsistency.ScalarPRCode
import DiophantineConsistency.ArithmeticUnaryRecursion
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-! # Scalar primitive recursive programs inside models of `𝗜𝚺₁`

`ScalarPRCode.eval` interprets a program on `ℕ` with Mathlib's pairing
`Nat.pair a b = if a < b then b*b + a else a*a + a + b`. Foundation's internal
pairing `LO.FirstOrder.Arithmetic.pair` is defined by exactly the same two
quadratic branches (`pair_graph`), and its inverse uses the internal square
root; `mpair`, `munpair₁`, `munpair₂` name these operations here, and
`natCast_pair` records the agreement on standard naturals.

Every program `c` gets a model-independent graph formula
`graphDef c : 𝚺₁.Semisentence 2` (output first, input second), defined by
structural recursion on `c`. In every model `V` of `𝗜𝚺₁`, `sem V c` is a
function `V → V` together with the proof that `graphDef c` defines it. The
primitive-recursion case uses Foundation's `PR.Blueprint`/`PR.Construction`,
whose blueprint is assembled from the graph formulas of the two subprograms;
this is why the definability proof is carried along the recursion.

`evalV c : V → V` is the resulting internal semantics. Its recursion equations
(`evalV_zero` … `evalV_prec_succ`) are the internal counterparts of the
defining clauses of `ScalarPRCode.eval`, and `evalV_natCast` shows that it
agrees with `ScalarPRCode.eval` on standard naturals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelScalarPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

/-! ### Internal pairing -/

section Pairing
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Internal pairing; the same two branches as `Nat.pair`. -/
abbrev mpair (a b : V) : V := LO.FirstOrder.Arithmetic.pair a b

/-- First internal unpairing projection. -/
abbrev munpair₁ (a : V) : V := LO.FirstOrder.Arithmetic.pi₁ a

/-- Second internal unpairing projection. -/
abbrev munpair₂ (a : V) : V := LO.FirstOrder.Arithmetic.pi₂ a

/-- The two quadratic branches of the internal pairing graph. -/
theorem mpair_eq_iff {a b c : V} :
    c = mpair a b ↔ (a < b ∧ c = b * b + a) ∨ (b ≤ a ∧ c = a * a + a + b) :=
  LO.FirstOrder.Arithmetic.pair_graph

theorem munpair₁_mpair (a b : V) : munpair₁ (mpair a b) = a :=
  LO.FirstOrder.Arithmetic.pi₁_pair a b

theorem munpair₂_mpair (a b : V) : munpair₂ (mpair a b) = b :=
  LO.FirstOrder.Arithmetic.pi₂_pair a b

theorem mpair_unpair (x : V) : mpair (munpair₁ x) (munpair₂ x) = x :=
  LO.FirstOrder.Arithmetic.pair_unpair x

theorem mpair_inj {a b c d : V} : mpair a b = mpair c d ↔ a = c ∧ b = d :=
  LO.FirstOrder.Arithmetic.pair_ext_iff

/-- On standard naturals the internal pairing is `Nat.pair`. -/
theorem natCast_pair (a b : ℕ) : ((Nat.pair a b : ℕ) : V) = mpair (a : V) (b : V) :=
  LO.FirstOrder.Arithmetic.coe_pair_eq_pair_coe a b

theorem natCast_eq_mpair (n : ℕ) :
    (n : V) = mpair (((Nat.unpair n).1 : ℕ) : V) (((Nat.unpair n).2 : ℕ) : V) := by
  rw [← natCast_pair, Nat.pair_unpair]

theorem munpair₁_natCast (n : ℕ) : munpair₁ (n : V) = (((Nat.unpair n).1 : ℕ) : V) := by
  rw [natCast_eq_mpair n, munpair₁_mpair]

theorem munpair₂_natCast (n : ℕ) : munpair₂ (n : V) = (((Nat.unpair n).2 : ℕ) : V) := by
  rw [natCast_eq_mpair n, munpair₂_mpair]

end Pairing

/-! ### Model-independent graph formulas -/

/-- Graph of the constant zero program. -/
def codeZeroDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. y = 0”

/-- Graph of the successor program. -/
def codeSuccDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. y = x + 1”

/-- Graph of the first unpairing projection. -/
def codeLeftDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !pi₁Def y x”

/-- Graph of the second unpairing projection. -/
def codeRightDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !pi₂Def y x”

/-- Graph of `x ↦ ⟪f x, g x⟫` from graphs of `f` and `g`. -/
def codePairDef (φ ψ : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ a b, !φ a x ∧ !ψ b x ∧ !pairDef y a b”

/-- Graph of `x ↦ f (g x)` from graphs of `f` and `g`. -/
def codeCompDef (φ ψ : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ z, !ψ z x ∧ !φ y z”

/-- Step graph of the recursion: output `u`, previous value `z`, index `i`,
parameter `a`; `u = g ⟪a, ⟪i, z⟫⟫`. -/
def codeStepDef (ψ : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 4 := .mkSigma
  “u z i a. ∃ q p, !pairDef q i z ∧ !pairDef p a q ∧ !ψ u p”

/-- The primitive-recursion blueprint built from the graphs of base and step. -/
def codeBlueprint (φ ψ : 𝚺₁.Semisentence 2) : PR.Blueprint 1 where
  zero := φ
  succ := codeStepDef ψ

/-- Graph of the recursion on the packed input `x = ⟪a, n⟫`. -/
def codePrecDef (φ ψ : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ a n, !pi₁Def a x ∧ !pi₂Def n x ∧ !(codeBlueprint φ ψ).resultDef y n a”

/-- The model-independent `𝚺₁` graph of a program, by structural recursion. -/
def graphDef : ScalarPRCode → 𝚺₁.Semisentence 2
  | .zero => codeZeroDef
  | .succ => codeSuccDef
  | .left => codeLeftDef
  | .right => codeRightDef
  | .pair f g => codePairDef (graphDef f) (graphDef g)
  | .comp f g => codeCompDef (graphDef f) (graphDef g)
  | .prec f g => codePrecDef (graphDef f) (graphDef g)

/-! ### Definability of the constructors -/

section Defined
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem codeZero_defined : 𝚺₁-Function₁[V] (fun _ : V => (0 : V)) via codeZeroDef :=
  .mk fun v => by simp [codeZeroDef]

theorem codeSucc_defined : 𝚺₁-Function₁[V] (fun x : V => x + 1) via codeSuccDef :=
  .mk fun v => by simp [codeSuccDef]

theorem codeLeft_defined : 𝚺₁-Function₁[V] (munpair₁ : V → V) via codeLeftDef :=
  .mk fun v => by simp [codeLeftDef, munpair₁]

theorem codeRight_defined : 𝚺₁-Function₁[V] (munpair₂ : V → V) via codeRightDef :=
  .mk fun v => by simp [codeRightDef, munpair₂]

variable {φ ψ : 𝚺₁.Semisentence 2} {F G : V → V}
  (hF : 𝚺₁-Function₁[V] F via φ) (hG : 𝚺₁-Function₁[V] G via ψ)
include hF hG

theorem codePair_defined :
    𝚺₁-Function₁[V] (fun x => mpair (F x) (G x)) via codePairDef φ ψ :=
  .mk fun v => by simp [codePairDef, hF.iff, hG.iff, mpair]

theorem codeComp_defined : 𝚺₁-Function₁[V] (fun x => F (G x)) via codeCompDef φ ψ :=
  .mk fun v => by simp [codeCompDef, hF.iff, hG.iff]

/-- The construction realizing `codeBlueprint φ ψ` from the defined base `F`
and step `G`: `result ![a] 0 = F a`, `result ![a] (i+1) = G ⟪a, ⟪i, result ![a] i⟫⟫`. -/
def precConstruction : PR.Construction V (codeBlueprint φ ψ) where
  zero w := F (w 0)
  succ w i z := G (mpair (w 0) (mpair i z))
  zero_defined := hF
  succ_defined := .mk fun v => by simp [codeBlueprint, codeStepDef, hG.iff, mpair]

/-- The internal primitive recursion on the packed input `x = ⟪a, n⟫`. -/
def precFun (x : V) : V :=
  (precConstruction hF hG).result ![munpair₁ x] (munpair₂ x)

theorem codePrec_defined : 𝚺₁-Function₁[V] (precFun hF hG) via codePrecDef φ ψ :=
  .mk fun v => by
    simp [codePrecDef, precFun, munpair₁, munpair₂,
      (ArithmeticUnaryRecursion.result_defined (codeBlueprint φ ψ)
        (precConstruction hF hG)).iff]

theorem precFun_zero (a : V) : precFun hF hG (mpair a 0) = F a := by
  have h := PR.Construction.result_zero (c := precConstruction hF hG) (v := ![a])
  unfold precFun
  rw [munpair₁_mpair, munpair₂_mpair]
  exact h

theorem precFun_succ (a n : V) :
    precFun hF hG (mpair a (n + 1)) = G (mpair a (mpair n (precFun hF hG (mpair a n)))) := by
  have h := PR.Construction.result_succ (c := precConstruction hF hG) (v := ![a]) n
  unfold precFun
  rw [munpair₁_mpair, munpair₂_mpair, munpair₁_mpair, munpair₂_mpair]
  exact h

end Defined

/-! ### The internal semantics -/

/-- The internal function of a program in the model `V`, carried together with
the proof that the model-independent formula `graphDef c` defines it. -/
def sem (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (c : ScalarPRCode) → {F : V → V // (𝚺₁-Function₁[V] F via (graphDef c))}
  | .zero => ⟨fun _ => 0, codeZero_defined⟩
  | .succ => ⟨fun x => x + 1, codeSucc_defined⟩
  | .left => ⟨munpair₁, codeLeft_defined⟩
  | .right => ⟨munpair₂, codeRight_defined⟩
  | .pair f g => ⟨fun x => mpair ((sem V f).1 x) ((sem V g).1 x),
      codePair_defined (sem V f).2 (sem V g).2⟩
  | .comp f g => ⟨fun x => (sem V f).1 ((sem V g).1 x),
      codeComp_defined (sem V f).2 (sem V g).2⟩
  | .prec f g => ⟨precFun (sem V f).2 (sem V g).2,
      codePrec_defined (sem V f).2 (sem V g).2⟩

section Semantics
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The internal semantics of a scalar primitive recursive program in `V`. -/
def evalV (c : ScalarPRCode) (x : V) : V := (sem V c).1 x

/-- `graphDef c` is a `𝚺₁` definition of the total function `evalV c`. -/
theorem evalV_defined (c : ScalarPRCode) : 𝚺₁-Function₁[V] (evalV c) via graphDef c :=
  (sem V c).2

theorem graphDef_iff (c : ScalarPRCode) (y x : V) :
    (graphDef c).val.Evalb ![y, x] ↔ y = evalV c x :=
  (evalV_defined c).df ![y, x]

theorem evalV_zero (x : V) : evalV .zero x = 0 := rfl

theorem evalV_succ (x : V) : evalV .succ x = x + 1 := rfl

theorem evalV_left (x : V) : evalV .left x = munpair₁ x := rfl

theorem evalV_right (x : V) : evalV .right x = munpair₂ x := rfl

theorem evalV_pair (f g : ScalarPRCode) (x : V) :
    evalV (.pair f g) x = mpair (evalV f x) (evalV g x) := rfl

theorem evalV_comp (f g : ScalarPRCode) (x : V) :
    evalV (.comp f g) x = evalV f (evalV g x) := rfl

theorem evalV_prec (f g : ScalarPRCode) (x : V) :
    evalV (.prec f g) x = precFun (sem V f).2 (sem V g).2 x := rfl

/-- Base clause of the internal recursion. -/
theorem evalV_prec_zero (f g : ScalarPRCode) (a : V) :
    evalV (.prec f g) (mpair a 0) = evalV f a :=
  precFun_zero (sem V f).2 (sem V g).2 a

/-- Step clause of the internal recursion. -/
theorem evalV_prec_succ (f g : ScalarPRCode) (a n : V) :
    evalV (.prec f g) (mpair a (n + 1)) =
      evalV g (mpair a (mpair n (evalV (.prec f g) (mpair a n)))) :=
  precFun_succ (sem V f).2 (sem V g).2 a n

/-- On standard naturals the internal semantics is `ScalarPRCode.eval`. -/
theorem evalV_natCast (c : ScalarPRCode) (n : ℕ) : evalV c (n : V) = ((c.eval n : ℕ) : V) := by
  induction c generalizing n with
  | zero =>
    show evalV ScalarPRCode.zero (n : V) = ((0 : ℕ) : V)
    rw [evalV_zero, Nat.cast_zero]
  | succ =>
    show evalV ScalarPRCode.succ (n : V) = ((n + 1 : ℕ) : V)
    rw [evalV_succ, Nat.cast_add, Nat.cast_one]
  | left =>
    show evalV ScalarPRCode.left (n : V) = (((Nat.unpair n).1 : ℕ) : V)
    rw [evalV_left, munpair₁_natCast]
  | right =>
    show evalV ScalarPRCode.right (n : V) = (((Nat.unpair n).2 : ℕ) : V)
    rw [evalV_right, munpair₂_natCast]
  | pair f g ihf ihg =>
    show evalV (ScalarPRCode.pair f g) (n : V) = ((Nat.pair (f.eval n) (g.eval n) : ℕ) : V)
    rw [evalV_pair, ihf, ihg, natCast_pair]
  | comp f g ihf ihg =>
    show evalV (ScalarPRCode.comp f g) (n : V) = ((f.eval (g.eval n) : ℕ) : V)
    rw [evalV_comp, ihg, ihf]
  | prec f g ihf ihg =>
    have key : ∀ a k : ℕ, evalV (ScalarPRCode.prec f g) (mpair (a : V) (k : V)) =
        ((Nat.rec (f.eval a) (fun i acc => g.eval (Nat.pair a (Nat.pair i acc))) k : ℕ) : V) := by
      intro a k
      induction k with
      | zero =>
        show evalV (ScalarPRCode.prec f g) (mpair (a : V) ((0 : ℕ) : V)) = ((f.eval a : ℕ) : V)
        rw [Nat.cast_zero, evalV_prec_zero, ihf]
      | succ k ih =>
        show evalV (ScalarPRCode.prec f g) (mpair (a : V) ((k + 1 : ℕ) : V)) =
          ((g.eval (Nat.pair a (Nat.pair k
            (Nat.rec (f.eval a) (fun i acc => g.eval (Nat.pair a (Nat.pair i acc))) k))) : ℕ) : V)
        rw [Nat.cast_add, Nat.cast_one, evalV_prec_succ, ih, ← natCast_pair, ← natCast_pair, ihg]
    show evalV (ScalarPRCode.prec f g) (n : V) =
      ((Nat.rec (f.eval (Nat.unpair n).1)
        (fun i acc => g.eval (Nat.pair (Nat.unpair n).1 (Nat.pair i acc)))
        (Nat.unpair n).2 : ℕ) : V)
    rw [natCast_eq_mpair n]
    exact key _ _

end Semantics

end DiophantineConsistency.ModelScalarPR
