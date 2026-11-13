import DiophantineConsistency.ModelRepArith
import DiophantineConsistency.ModelBetaFunction

/-! # Internal correctness of the primitive-recursion trace

`ScalarPRRepresentation.recursionCoordinates` represents `y = R z k` (with
`R z 0 = f z`, `R z (i+1) = g ⟪z, ⟪i, R z i⟫⟫`) by an explicit beta-function
trace: two trace parameters `a b` with entries `entry a b i = a % ((i+1)·b+1)`,
an initial and a final entry, and the transitions `∀ i < k` eliminated by
`Rep.boundedForall`.

This file proves, inside every model of `𝗜𝚺₁`:

* `trace_iff`: the internal trace condition holds for some `a b` exactly when
  `out = evalV (prec f g) ⟪z, k⟫`; the forward direction is Gödel's beta
  function (`ModelBetaFunction.beta_exists`), the backward one a `𝚺₁` induction;
* `graphHolds_recursionCoordinates` and `precCase_of_boundedForall`:
  `ModelRepBasic.PrecCase` follows from the internal correctness of
  `Rep.boundedForall` (`BoundedForallCase`);
* `boundedForallCase_of_certificate`: that correctness reduces to the internal
  correctness of the CRT certificate `BoundedForallRepresentation.representation`
  for natural expressions (`CertificateCase`).

`CertificateCase` is the remaining obligation (the internal
Davis–Putnam–Robinson bounded-quantifier theorem); it is stated here and not
proved. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepPrec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelDifferenceRing ModelScalarPR ModelRepBasic ModelRepArith
open AdaptiveEquationSyntax2011 (InternalZero)

/-! ### The bounded-universal interfaces -/

/-- Internal correctness of the input-bounded universal quantifier
`Rep.boundedForall`, for every internally correct representation. -/
abbrev BoundedForallCase : Prop :=
  ∀ (σ : Type) (P : (Option σ → ℕ) → Prop) (r : Rep (Option σ) P) (b : σ)
    (Q : ModelPred (Option σ)), Holds r Q →
      Holds (r.boundedForall b) (fun V _ _ x => ∀ k < x b, Q V (Option.elim' k x))

/-- Internal correctness of the CRT certificate for a pair of natural expressions:
the internal Davis–Putnam–Robinson bounded-quantifier theorem. -/
abbrev CertificateCase : Prop :=
  ∀ (σ : Type) (m : ℕ) (e f : NatExpr (Option σ ⊕ Fin m)) (b : σ),
    Holds (BoundedForallRepresentation.representation e f b)
      (fun V _ _ x => ∀ k < x b, ∃ w : Fin m → V,
        e.evalSemiring (Sum.elim (Option.elim' k x) w) =
          f.evalSemiring (Sum.elim (Option.elim' k x) w))

/-- The certificate case gives the bounded-universal case: `Rep.boundedForall`
is the certificate for the split-natural form of the expression. -/
theorem boundedForallCase_of_certificate (h : CertificateCase) : BoundedForallCase := by
  intro σ P r b Q hr
  refine holds_congr _ ?_ (h σ r.witnessCount r.expression.splitNatural.1
    r.expression.splitNatural.2 b)
  intro V _ _ x
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  exact (hr V (Option.elim' k x)).symm

/-! ### The internal trace -/

section Trace
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One entry of the internal beta-function trace. -/
def entry (a b i : V) : V := a % ((i + 1) * b + 1)

instance evalV_definable (c : ScalarPRCode) : 𝚺₁-Function₁[V] (evalV c : V → V) :=
  (evalV_defined c).to_definable

/-- The internal trace characterizes the internal primitive recursion. -/
theorem trace_iff (f g : ScalarPRCode) (z k out : V) :
    out = evalV (ScalarPRCode.prec f g) (mpair z k) ↔ ∃ a b : V,
      entry a b 0 = evalV f z ∧ entry a b k = out ∧
        ∀ i < k, entry a b (i + 1) = evalV g (mpair z (mpair i (entry a b i))) := by
  constructor
  · intro hout
    have hs : 𝚺₁-Function₁[V] (fun i : V => evalV (ScalarPRCode.prec f g) (mpair z i)) := by
      show 𝚺₁-Function₁[V]
        (fun i : V => evalV (ScalarPRCode.prec f g) (LO.FirstOrder.Arithmetic.pair z i))
      definability
    obtain ⟨a, b, hab⟩ := @ModelBetaFunction.beta_exists V _ _
      (fun i : V => evalV (ScalarPRCode.prec f g) (mpair z i)) hs k
    refine ⟨a, b, ?_, ?_, ?_⟩
    · show a % ((0 + 1) * b + 1) = evalV f z
      rw [hab 0 (Arithmetic.zero_le k), evalV_prec_zero]
    · show a % ((k + 1) * b + 1) = out
      rw [hab k le_rfl, hout]
    · intro i hik
      show a % ((i + 1 + 1) * b + 1) = evalV g (mpair z (mpair i (a % ((i + 1) * b + 1))))
      rw [hab (i + 1) (LO.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hik), hab i (le_of_lt hik),
        evalV_prec_succ]
  · rintro ⟨a, b, h0, hk, hstep⟩
    have key : ∀ i, i ≤ k →
        a % ((i + 1) * b + 1) = evalV (ScalarPRCode.prec f g) (mpair z i) := by
      intro i
      induction i using ISigma1.sigma1_succ_induction
      · show 𝚺₁-Predicate (fun i : V => i ≤ k →
          a % ((i + 1) * b + 1) =
            evalV (ScalarPRCode.prec f g) (LO.FirstOrder.Arithmetic.pair z i))
        definability
      case zero =>
        intro _
        rw [evalV_prec_zero]
        exact h0
      case succ i ih =>
        intro hi
        have hik : i < k := LO.FirstOrder.Arithmetic.succ_le_iff_lt.mp hi
        rw [evalV_prec_succ, ← ih (le_of_lt hik)]
        exact hstep i hik
    rw [← hk]
    exact key k le_rfl

/-- The trace condition in the raw form produced by the graph lemmas. -/
theorem certificate_iff (f g : ScalarPRCode) (z k out : V) :
    (∃ t : Fin 2 → V, entry (t 0) (t 1) ((0 : ℕ) : V) = evalV f z ∧
      entry (t 0) (t 1) k = out ∧
      ∀ i < k, entry (t 0) (t 1) (i + ((1 : ℕ) : V)) =
        evalV g (mpair z (mpair i (entry (t 0) (t 1) i)))) ↔
    out = evalV (ScalarPRCode.prec f g) (mpair z k) := by
  rw [trace_iff f g z k out]
  simp only [Nat.cast_zero, Nat.cast_one]
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t 0, t 1, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨![a, b], h⟩

end Trace

/-! ### Graph of one trace entry -/

theorem graphHolds_entryGraph {σ : Type*} {a b i : (σ → ℕ) → ℕ} {ra : GraphRep a}
    {rb : GraphRep b} {ri : GraphRep i} {A B I : ModelFun σ}
    (ha : GraphHolds ra A) (hb : GraphHolds rb B) (hi : GraphHolds ri I) :
    GraphHolds (ScalarPRRepresentation.entryGraph ra rb ri)
      (fun V _ _ v => entry (A V v) (B V v) (I V v)) := by
  refine graphHolds_of_eq (graphHolds_mod ha (graphHolds_add (graphHolds_mul
    (graphHolds_add hi (graphHolds_constant 1)) hb) (graphHolds_constant 1))) ?_
  intro V _ _ v
  show A V v % ((I V v + ((1 : ℕ) : V)) * B V v + ((1 : ℕ) : V)) =
    A V v % ((I V v + 1) * B V v + 1)
  rw [Nat.cast_one]

/-! ### The pieces of `recursionCoordinates` -/

section Pieces
open ScalarPRRepresentation (TraceVar entryGraph)

/-- First trace parameter. -/
abbrev coordA : GraphRep (fun v : TraceVar → ℕ => v (.inr 0)) :=
  GraphRep.coordinate (Sum.inr (0 : Fin 2) : TraceVar)
/-- Second trace parameter. -/
abbrev coordB : GraphRep (fun v : TraceVar → ℕ => v (.inr 1)) :=
  GraphRep.coordinate (Sum.inr (1 : Fin 2) : TraceVar)
/-- The recursion parameter. -/
abbrev coordZ : GraphRep (fun v : TraceVar → ℕ => v (.inl (some 0))) :=
  GraphRep.coordinate (Sum.inl (some (0 : Fin 2)) : TraceVar)
/-- The recursion length. -/
abbrev coordK : GraphRep (fun v : TraceVar → ℕ => v (.inl (some 1))) :=
  GraphRep.coordinate (Sum.inl (some (1 : Fin 2)) : TraceVar)
/-- The output. -/
abbrev coordOut : GraphRep (fun v : TraceVar → ℕ => v (.inl none)) :=
  GraphRep.coordinate (Sum.inl none : TraceVar)

/-- The initial-entry condition, with the syntax of `recursionCoordinates`. -/
def initialRep {f : ℕ → ℕ} (rf : GraphRep (fun v : Fin 1 → ℕ => f (v 0))) :=
  equalityGraphsRep (entryGraph coordA coordB (GraphRep.constant 0))
    (GraphRep.compose rf (fun _ : Fin 1 => coordZ))

/-- The final-entry condition. -/
def finalRep := equalityGraphsRep (entryGraph coordA coordB coordK) coordOut

/-- One transition, with the bounded index as the extra coordinate `none`. -/
def stepEqRep {g : ℕ → ℕ} (rg : GraphRep (fun v : Fin 1 → ℕ => g (v 0))) :=
  equalityGraphsRep
    (entryGraph (coordA.reindex some) (coordB.reindex some)
      ((GraphRep.coordinate (none : Option TraceVar)).add (GraphRep.constant 1)))
    (GraphRep.compose rg (fun _ : Fin 1 => (coordZ.reindex some).pair
      ((GraphRep.coordinate (none : Option TraceVar)).pair
        (entryGraph (coordA.reindex some) (coordB.reindex some)
          (GraphRep.coordinate (none : Option TraceVar))))))

/-- The complete trace certificate before `ofIff`. -/
def certificateRep {f g : ℕ → ℕ} (rf : GraphRep (fun v : Fin 1 → ℕ => f (v 0)))
    (rg : GraphRep (fun v : Fin 1 → ℕ => g (v 0))) :=
  ((initialRep rf).conjunction (finalRep.conjunction
    ((stepEqRep rg).boundedForall (Sum.inl (some 1) : TraceVar)))).existsBlock

theorem holds_initialRep {f : ℕ → ℕ} {rf : GraphRep (fun v : Fin 1 → ℕ => f (v 0))}
    {F : ModelFun (Fin 1)} (hf : GraphHolds rf F) :
    Holds (initialRep rf) (fun V _ _ u =>
      entry (u (Sum.inr 0)) (u (Sum.inr 1)) ((0 : ℕ) : V) =
        F V (fun _ => u (Sum.inl (some 0)))) :=
  holds_equalityGraphsRep
    (graphHolds_entryGraph (graphHolds_coordinate (Sum.inr (0 : Fin 2) : TraceVar))
      (graphHolds_coordinate (Sum.inr (1 : Fin 2) : TraceVar)) (graphHolds_constant 0))
    (graphHolds_compose hf
      (fun _ => graphHolds_coordinate (Sum.inl (some (0 : Fin 2)) : TraceVar)))

theorem holds_finalRep :
    Holds finalRep (fun V _ _ u =>
      entry (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inl (some 1))) = u (Sum.inl none)) :=
  holds_equalityGraphsRep
    (graphHolds_entryGraph (graphHolds_coordinate (Sum.inr (0 : Fin 2) : TraceVar))
      (graphHolds_coordinate (Sum.inr (1 : Fin 2) : TraceVar))
      (graphHolds_coordinate (Sum.inl (some (1 : Fin 2)) : TraceVar)))
    (graphHolds_coordinate (Sum.inl none : TraceVar))

theorem holds_stepEqRep {g : ℕ → ℕ} {rg : GraphRep (fun v : Fin 1 → ℕ => g (v 0))}
    {G : ModelFun (Fin 1)} (hg : GraphHolds rg G) :
    Holds (stepEqRep rg) (fun V _ _ x =>
      entry (x (some (Sum.inr 0))) (x (some (Sum.inr 1))) (x none + ((1 : ℕ) : V)) =
        G V (fun _ => mpair (x (some (Sum.inl (some 0))))
          (mpair (x none) (entry (x (some (Sum.inr 0))) (x (some (Sum.inr 1))) (x none))))) :=
  holds_equalityGraphsRep
    (graphHolds_entryGraph
      (graphHolds_reindex (graphHolds_coordinate (Sum.inr (0 : Fin 2) : TraceVar)) some)
      (graphHolds_reindex (graphHolds_coordinate (Sum.inr (1 : Fin 2) : TraceVar)) some)
      (graphHolds_add (graphHolds_coordinate (none : Option TraceVar)) (graphHolds_constant 1)))
    (graphHolds_compose hg (fun _ => graphHolds_pair
      (graphHolds_reindex (graphHolds_coordinate (Sum.inl (some (0 : Fin 2)) : TraceVar)) some)
      (graphHolds_pair (graphHolds_coordinate (none : Option TraceVar))
        (graphHolds_entryGraph
          (graphHolds_reindex (graphHolds_coordinate (Sum.inr (0 : Fin 2) : TraceVar)) some)
          (graphHolds_reindex (graphHolds_coordinate (Sum.inr (1 : Fin 2) : TraceVar)) some)
          (graphHolds_coordinate (none : Option TraceVar))))))

theorem holds_certificateRep (hbf : BoundedForallCase) {f g : ℕ → ℕ}
    {rf : GraphRep (fun v : Fin 1 → ℕ => f (v 0))}
    {rg : GraphRep (fun v : Fin 1 → ℕ => g (v 0))}
    {F G : ModelFun (Fin 1)} (hf : GraphHolds rf F) (hg : GraphHolds rg G) :
    Holds (certificateRep rf rg) (fun V _ _ v => ∃ t : Fin 2 → V,
      entry (t 0) (t 1) ((0 : ℕ) : V) = F V (fun _ => v (some 0)) ∧
      entry (t 0) (t 1) (v (some 1)) = v none ∧
      ∀ k < v (some 1), entry (t 0) (t 1) (k + ((1 : ℕ) : V)) =
        G V (fun _ => mpair (v (some 0)) (mpair k (entry (t 0) (t 1) k)))) :=
  holds_existsBlock (holds_conjunction (holds_initialRep hf)
    (holds_conjunction holds_finalRep
      (hbf _ _ _ (Sum.inl (some 1) : TraceVar) _ (holds_stepEqRep hg))))

end Pieces

/-! ### The primitive-recursion case -/

/-- The compiled trace graph computes the internal recursion on `⟪z, k⟫`. -/
theorem graphHolds_recursionCoordinates (hbf : BoundedForallCase) (f g : ScalarPRCode)
    (hf : GraphHolds f.graphRep (evalFun f)) (hg : GraphHolds g.graphRep (evalFun g)) :
    GraphHolds (ScalarPRRepresentation.recursionCoordinates f.graphRep g.graphRep)
      (fun V _ _ v => evalV (ScalarPRCode.prec f g) (mpair (v 0) (v 1))) := by
  refine holds_congr _ ?_ (holds_certificateRep hbf hf hg)
  intro V _ _ v
  exact certificate_iff f g (v (some 0)) (v (some 1)) (v none)

/-- `ModelRepBasic.PrecCase` from internal correctness of `Rep.boundedForall`. -/
theorem precCase_of_boundedForall (hbf : BoundedForallCase) : PrecCase := by
  intro f g hf hg
  refine graphHolds_of_eq (graphHolds_composeTwo (graphHolds_recursionCoordinates hbf f g hf hg)
    (graphHolds_unpairLeft (graphHolds_coordinate (0 : Fin 1)))
    (graphHolds_unpairRight (graphHolds_coordinate (0 : Fin 1)))) ?_
  intro V _ _ v
  show evalV (ScalarPRCode.prec f g) (mpair (munpair₁ (v 0)) (munpair₂ (v 0))) =
    evalV (ScalarPRCode.prec f g) (v 0)
  rw [mpair_unpair]

/-- `ModelRepBasic.PrecCase` from the internal CRT certificate. -/
theorem precCase_of_certificate (h : CertificateCase) : PrecCase :=
  precCase_of_boundedForall (boundedForallCase_of_certificate h)

/-- Every compiled program graph is internally correct, given the certificate case. -/
theorem graphRep_holds_of_certificate (h : CertificateCase) (c : ScalarPRCode) :
    GraphHolds c.graphRep (evalFun c) :=
  graphRep_holds (precCase_of_certificate h) c

end DiophantineConsistency.ModelRepPrec
