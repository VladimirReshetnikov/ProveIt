import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.ModelDifferenceRing

/-! # The unrestricted-integer adapter for iPRA endpoints

The iPRA pipeline (`IPRAExpressionNative.equivalence_of_bridge`) speaks about natural unknowns
only: its sentence `nativeNoZero e` says that the split-natural syntax of `e` has no zero over
the naturals. A row of the frontier whose unknowns range over **all integers** is brought into
this form by the classical sign split.

**Convention.** For `e : Expr (Fin n)` with integer unknowns `x₀, …, xₙ₋₁`, the sentence
"`e` has no integer solution" is formalized as "`signedSplit e` has no natural zero", where
`signedSplit e : Expr (Fin (n+n))` writes each unknown as a difference `xᵢ = aᵢ − bᵢ` of two
natural unknowns, `aᵢ` at index `Fin.castAdd n i` and `bᵢ` at `Fin.natAdd n i`. Over the
standard naturals this is equivalent to the integer statement because every integer is such a
difference; inside an arbitrary model of `𝗜𝚺₁` the same holds for the ring of differences
`ModelDifferenceRing.DiffRing V` (`integer_zero_iff`).

* `IntegerModelBridge e`: in every model of `𝗜𝚺₁`, `e` has a zero in `DiffRing V` iff machine
  215 halts (the halting predicate of `IPRAOrdinary12.PositiveModelBridge`).
* `bridge_of_integer`: such a bridge is a `PolynomialBridge` of `signedSplit e`.
* `native_of_integer`, `standard_of_integer`, `reference_of_integer`: the native, standard and
  equality-only iPRA equivalences of `nativeNoZero (signedSplit e)` with the selected Foundation
  ZFC consistency predicate, mirroring `IPRAOrdinary12Chain.native_of_positive` etc. No positive
  shift is applied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IntegerDomain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open ModelDifferenceRing

/-- Each integer unknown `xᵢ` becomes `aᵢ − bᵢ`, with `aᵢ` at `castAdd n i` and `bᵢ` at
`natAdd n i`. -/
def signedSplit {n : ℕ} (e : Expr (Fin n)) : Expr (Fin (n + n)) :=
  e.subst fun i => .var (Fin.castAdd n i) - .var (Fin.natAdd n i)

theorem evalRing_subst {σ τ R : Type*} [CommRing R] (f : σ → Expr τ) (e : Expr σ)
    (v : τ → R) : (e.subst f).evalRing v = e.evalRing (fun i => (f i).evalRing v) := by
  induction e <;> simp_all [Expr.subst, Expr.evalRing]

theorem evalRing_signedSplit {n : ℕ} {R : Type*} [CommRing R] (e : Expr (Fin n))
    (v : Fin (n + n) → R) :
    (signedSplit e).evalRing v =
      e.evalRing (fun i => v (Fin.castAdd n i) - v (Fin.natAdd n i)) := by
  rw [signedSplit, evalRing_subst]
  rfl

/-- Integer zeros in every model exactly when machine 215 halts. -/
def IntegerModelBridge {n : ℕ} (e : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ w : Fin n → DiffRing V, e.evalRing w = 0) ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time) = 0

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem internalZero_signedSplit {n : ℕ} (e : Expr (Fin n)) (v : Fin (n + n) → V) :
    InternalZero (signedSplit e) v ↔
      e.evalRing (fun i => ι (v (Fin.castAdd n i)) - ι (v (Fin.natAdd n i))) = 0 := by
  rw [internalZero_iff, evalRing_signedSplit]

/-- **Sanity check of the convention.** A natural zero of `signedSplit e` exists in `V` iff
`e` has a zero in the ring of differences `DiffRing V`. -/
theorem integer_zero_iff {n : ℕ} (e : Expr (Fin n)) :
    (∃ v : Fin (n + n) → V, InternalZero (signedSplit e) v) ↔
      ∃ w : Fin n → DiffRing V, e.evalRing w = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, (internalZero_signedSplit e v).mp hv⟩
  · rintro ⟨w, hw⟩
    choose a b hab using fun i => exists_mk (w i)
    refine ⟨Fin.addCases a b, (internalZero_signedSplit e _).mpr ?_⟩
    have hw' : (fun i => ι (Fin.addCases (motive := fun _ => V) a b (Fin.castAdd n i)) -
        ι (Fin.addCases (motive := fun _ => V) a b (Fin.natAdd n i))) = w := by
      funext i
      rw [Fin.addCases_left, Fin.addCases_right, hab i, mk_eq_sub]
    rw [hw']
    exact hw

end Model

theorem bridge_of_integer {n : ℕ} (e : Expr (Fin n)) (hi : IntegerModelBridge e) :
    PolynomialBridge (signedSplit e) := by
  intro V _ _
  rw [classicalNoZero_iff]
  constructor
  · intro h hhalt
    obtain ⟨v, hv⟩ := (integer_zero_iff e).mpr ((hi V).mpr hhalt)
    exact h v hv
  · intro h v hz
    exact h ((hi V).mp ((integer_zero_iff e).mp ⟨v, hz⟩))

/-- **Native iPRA: no integer solution iff ZFC is consistent** (unknowns split as `a − b`). -/
theorem native_of_integer {n : ℕ} (e : Expr (Fin n)) (h : IntegerModelBridge e) :
    nativeTheory ⊢ IPRAExpressionNative.nativeNoZero (signedSplit e) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge_of_integer e h)

/-- **Standard iPRA.** -/
theorem standard_of_integer {n : ℕ} (e : Expr (Fin n)) (h : IntegerModelBridge e) :
    IPRAStandardTheory.standardTheory ⊢
      IPRAExpressionNative.nativeNoZero (signedSplit e) 🡘
        ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (native_of_integer e h)

/-- **Equality-only iPRA.** -/
theorem reference_of_integer {n : ℕ} (e : Expr (Fin n)) (h : IntegerModelBridge e) :
    IPRAEqualityOnlyReference.referenceTheory ⊢
      IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (signedSplit e)) 🡘
        ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference (native_of_integer e h)

#print axioms integer_zero_iff
#print axioms bridge_of_integer
#print axioms native_of_integer
#print axioms standard_of_integer
#print axioms reference_of_integer

end DiophantineConsistency.IntegerDomain
