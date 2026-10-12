import GowersSzemeredi.Proofs16IntegerPolynomialRecurrence
import GowersSzemeredi.Proofs05ExplicitSchmidtRecurrence
import GowersSzemeredi.Proofs16FamilyRetiledLinearity
import GowersSzemeredi.Proofs16FamilyLemma6

/-! Explicit polynomial recurrence profiles with genuine integer boxes.
The named Schmidt constants are exactly those used by the existing cover
induction; no extra width or error loss is introduced. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem ascending_simultaneous_multiaffine_partition_bound_explicit
    (k : Nat) (hk : 0 < k) (h : Nat) :
    AscendingSimultaneousMultiaffinePartitionBound k h (multiaffinePartitionK k h)
      (multiaffinePartitionP k h) := by
  induction h with
  | zero => exact ascendingSimultaneousMultiaffinePartitionBound_zero k
  | succ h ih =>
    exact ih.step hk (two_le_multiaffinePartitionK k h) (multiaffinePartitionP_pos k h)
      (one_le_uniformSchmidtK k) (uniform_modular_monomial_recurrence_explicit k)

theorem ascendingMultilinearPartitionBoundAt_explicit (k : Nat) (hk : 0 < k) :
    AscendingMultilinearPartitionBoundAt k (multiaffinePartitionK k (2 ^ k))
      (multiaffinePartitionP k (2 ^ k)) :=
  ascendingMultilinearPartitionBoundAt_of
    (ascending_simultaneous_multiaffine_partition_bound_explicit k hk (2 ^ k))

def AscendingSection16RecurrenceProfileWith (k : Nat) (Thr : Nat → Nat)
    (Exp : Nat → Real) : Prop :=
  ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsAscendingInteger →
    ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
    Thr q ≤ m → m ≤ P.width →
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
      (∀ j, (m : Real) ^ Exp q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (Q j).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤ 2 * (m : Real) ^ (-Exp q) * N

def IntegerSection16RecurrenceProfileWith (k : Nat) (Thr : Nat → Nat)
    (Exp : Nat → Real) : Prop :=
  ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.HasIntegerRepresentatives →
    ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
    Thr q ≤ m → m ≤ P.width →
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
      (∀ j, (m : Real) ^ Exp q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (Q j).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤ 2 * (m : Real) ^ (-Exp q) * N

theorem ascendingSection16RecurrenceProfileWith_of_polynomial (k K p : Nat)
    (h : AscendingPolynomialSection16RecurrenceProfileAt k K p) :
    AscendingSection16RecurrenceProfileWith k (familyRecThr k K p) (familyRecExp k p) := h

theorem AscendingSection16RecurrenceProfileWith.to_integer {k : Nat}
    {Thr : Nat → Nat} {Exp : Nat → Real} (h : AscendingSection16RecurrenceProfileWith k Thr Exp) :
    IntegerSection16RecurrenceProfileWith k Thr Exp := by
  intro N q m _ P hP mu hmu hm hmP
  obtain ⟨d, A, hstep, hd, hA, hcarrier, hwidth, _⟩ := hP.canonical_axes
  let C := integerAxesBox N A d hstep
  have hC : C.IsAscendingInteger :=
    ⟨d, A, hd, rfl, fun i => ⟨(hA i).1, hstep i, (hA i).2, rfl⟩⟩
  obtain ⟨M, Q, hpart, hQ, hQwidth, hsmall⟩ :=
    h N q m C hC mu hmu hm (by rwa [hwidth])
  refine ⟨M, Q, ?_, hQ, hQwidth, hsmall⟩
  change IsPartition (fun j => (Q j).carrier) P.carrier
  rw [← hcarrier]
  exact hpart

theorem ascendingSection16RecurrenceProfileWith_explicit (k : Nat) :
    AscendingSection16RecurrenceProfileWith k
      (familyRecThr k (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1))))
        ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))
      (familyRecExp k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))) := by
  have hK := two_le_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
  have hp := multiaffinePartitionP_pos (k + 1) (2 ^ (k + 1))
  exact ascendingSection16RecurrenceProfileWith_of_polynomial k _ _
    (ascendingPolynomialSection16RecurrenceProfileAt_of k hK (Nat.mul_pos (Nat.succ_pos k) hp)
      (ascendingCommonDiffPartitionTwoBoundAt_of k hK hp
        (ascendingCommonDiffPartitionBoundAt_of k hK hp
          (ascendingMultilinearPartitionBoundAt_explicit (k + 1) (Nat.succ_pos k)))))

theorem integerSection16RecurrenceProfileWith_explicit (k : Nat) :
    IntegerSection16RecurrenceProfileWith k
      (familyRecThr k (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1))))
        ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))
      (familyRecExp k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))) :=
  (ascendingSection16RecurrenceProfileWith_explicit k).to_integer

end LeanProofs.GowersSzemeredi
