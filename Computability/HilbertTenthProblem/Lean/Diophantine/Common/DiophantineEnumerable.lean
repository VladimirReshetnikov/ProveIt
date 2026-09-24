import Diophantine.Common.MathlibDiophFinite
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE

/-!
# Diophantine sets are recursively enumerable

Finite-support extraction reduces Mathlib's arbitrarily indexed Diophantine
witnesses to a finite tuple. Polynomial evaluation is a difference of two
primitive-recursive natural functions, by induction on `IsPoly`. Equality of
those two functions is decidable by a primitive-recursive test. Unbounded
search over encoded finite tuples therefore semidecides the zero set.

No positivity restriction is imposed on the input, and the witness tuple may
be empty. The all-zero fallback for failed decoding does not remove or add
any possible natural witness tuple.
-/

namespace Diophantine

/-- Under primitive-recursive natural coordinate assignments, an integer
polynomial is the difference of two primitive-recursive natural functions. -/
theorem isPoly_exists_primrec_difference {ι α : Type*} [Primcodable α]
    {p : (ι → ℕ) → ℤ} (hp : IsPoly p)
    (coordinates : ι → α → ℕ) (hc : ∀ idx, Primrec (coordinates idx)) :
    ∃ positive negative : α → ℕ, Primrec positive ∧ Primrec negative ∧
      ∀ x, p (fun idx => coordinates idx x) = (positive x : ℤ) - (negative x : ℤ) := by
  induction hp with
  | proj idx =>
      refine ⟨coordinates idx, fun _ => 0, hc idx, Primrec.const 0, ?_⟩
      intro x
      simp
  | const coeff =>
      exact ⟨fun _ => coeff.toNat, fun _ => (-coeff).toNat,
        Primrec.const _, Primrec.const _, fun _ => (Int.toNat_sub_toNat_neg coeff).symm⟩
  | sub _ _ ihf ihg =>
      obtain ⟨a, b, ha, hb, hf⟩ := ihf
      obtain ⟨c, d, hcc, hd, hg⟩ := ihg
      refine ⟨fun x => a x + d x, fun x => b x + c x,
        Primrec.nat_add.comp ha hd, Primrec.nat_add.comp hb hcc, ?_⟩
      intro x
      dsimp only
      rw [hf x, hg x]
      push_cast
      ring
  | mul _ _ ihf ihg =>
      obtain ⟨a, b, ha, hb, hf⟩ := ihf
      obtain ⟨c, d, hcc, hd, hg⟩ := ihg
      refine ⟨fun x => a x * c x + b x * d x, fun x => a x * d x + b x * c x,
        Primrec.nat_add.comp (Primrec.nat_mul.comp ha hcc) (Primrec.nat_mul.comp hb hd),
        Primrec.nat_add.comp (Primrec.nat_mul.comp ha hd) (Primrec.nat_mul.comp hb hcc), ?_⟩
      intro x
      dsimp only
      rw [hf x, hg x]
      push_cast
      ring

-- Use the encoding belonging to `Primcodable.finArrow`, consistently in both
-- directions, rather than the independent general `Encodable.finPi` instance.
private def encodeFiniteWitness {r : ℕ} (w : Fin r → ℕ) : ℕ :=
  @Encodable.encode (Fin r → ℕ) Primcodable.toEncodable w

private def decodeFiniteWitness {r : ℕ} (code : ℕ) : Fin r → ℕ :=
  (@Encodable.decode (Fin r → ℕ) Primcodable.toEncodable code).getD (fun _ => 0)

private theorem primrec_decodeFiniteWitness {r : ℕ} :
    Primrec (@decodeFiniteWitness r) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (fun _ : Fin r => 0))

private theorem decodeFiniteWitness_encode {r : ℕ} (w : Fin r → ℕ) :
    decodeFiniteWitness (encodeFiniteWitness w) = w := by
  simp [decodeFiniteWitness, encodeFiniteWitness]

/-- Searching a total primitive-recursive test semidecides its existential projection. -/
private theorem rePred_nat_exists {p : ℕ × ℕ → Prop} (hp : PrimrecPred p) :
    REPred (fun n : ℕ => ∃ code : ℕ, p (n, code)) := by
  classical
  have hsearch : Partrec (fun n : ℕ =>
      Nat.rfind (fun code => Part.some (decide (p (n, code))))) :=
    Partrec.rfind hp.decide.to_comp.partrec
  refine hsearch.dom_re.of_eq ?_
  intro n
  simp [Nat.rfind_dom]

/-- The existential natural zero set of a finite integer polynomial is recursively
enumerable, including the case of no auxiliary witnesses. -/
theorem finite_polynomial_rePred {r : ℕ} (Q : MvPolynomial (Unit ⊕ Fin r) ℤ) :
    REPred (fun n : ℕ => ∃ w : Fin r → ℕ,
      MvPolynomial.eval
        (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) Q = 0) := by
  let coordinates : Unit ⊕ Fin r → (ℕ × ℕ) → ℕ := fun idx args =>
    Sum.elim (fun _ : Unit => args.1) (decodeFiniteWitness args.2) idx
  have hcoordinates : ∀ idx, Primrec (coordinates idx) := by
    intro idx
    cases idx with
    | inl _unit => exact Primrec.fst
    | inr idx =>
        exact Primrec.fin_app.comp (primrec_decodeFiniteWitness.comp Primrec.snd)
          (Primrec.const idx)
  obtain ⟨positive, negative, hp, hn, hvalues⟩ :=
    isPoly_exists_primrec_difference (isPoly_eval_mvPolynomial Q) coordinates hcoordinates
  have heval (n code : ℕ) :
      MvPolynomial.eval
        (fun idx => ((Sum.elim (fun _ : Unit => n) (decodeFiniteWitness code) idx : ℕ) : ℤ)) Q =
          (positive (n, code) : ℤ) - (negative (n, code) : ℤ) :=
    hvalues (n, code)
  have htest : PrimrecPred (fun args : ℕ × ℕ => positive args = negative args) :=
    Primrec.eq.comp hp hn
  refine (rePred_nat_exists htest).of_eq ?_
  intro n
  constructor
  · rintro ⟨code, hzero⟩
    refine ⟨decodeFiniteWitness code, ?_⟩
    rw [heval, hzero, sub_self]
  · rintro ⟨w, hw⟩
    refine ⟨encodeFiniteWitness w, ?_⟩
    have hz : (positive (n, encodeFiniteWitness w) : ℤ) -
        (negative (n, encodeFiniteWitness w) : ℤ) = 0 := by
      rw [← heval, decodeFiniteWitness_encode]
      exact hw
    exact_mod_cast (sub_eq_zero.mp hz)

/-- Every Diophantine subset of the naturals is recursively enumerable.
Mathlib's arbitrary witness type is reduced to finite support before search;
membership at zero is preserved. -/
theorem dioph_rePred {S : Set ℕ} (hS : Dioph {v : Unit → ℕ | v () ∈ S}) :
    REPred S := by
  obtain ⟨r, Q, hQ⟩ := dioph_iff_exists_fin_polynomial.mp hS
  refine (finite_polynomial_rePred Q).of_eq ?_
  intro n
  exact (hQ (fun _ : Unit => n)).symm

end Diophantine
