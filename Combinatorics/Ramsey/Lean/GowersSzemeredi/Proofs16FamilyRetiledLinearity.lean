import GowersSzemeredi.Proofs16RetiledLinearityBound
import GowersSzemeredi.Proofs16RetiledRecurrence
import GowersSzemeredi.Proofs16ShortProduct
import GowersSzemeredi.Proofs16ShortScale

/-! Retiled linearity for a whole family of functions on one partition.

Step (B) of Notes L.3: the simultaneous union of pieces. The sequential
union `MultiplyLinearWith.union` raises the width exponent to the number of
pieces. The family route instead builds one partition for all pieces at
each stage.

The first stage is retiled linearity. Its partition comes from the
recurrence for the covering graphs `μ` alone, so every function whose
frequencies those graphs cover is linear on the same cells.
* `Section16RecurrenceProfileWith k Thr Exp`: the recurrence profile with an
  abstract threshold and exponent. `PolynomialSection16RecurrenceProfileAt`
  is definitionally the polynomial instance. Keeping it abstract keeps this
  module off the OpenAI Schmidt closure.
* `retiled_linearity_family_of_recurrence_scale`: a copy of
  `retiled_linearity_of_recurrence_scale`. Its output cells are linear for
  every member of an arbitrary family `(K a, G a, A a, f a)`.
* `Section16RetiledLinearityFamilyBound` and
  `Section16RecurrenceProfileWith.retiled_family`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The simultaneous recurrence profile, with abstract threshold and exponent. -/
def Section16RecurrenceProfileWith (k : Nat) (Thr : Nat → Nat) (Exp : Nat → Real) : Prop :=
  ∀ (N q m : Nat) [NeZero N] (P : Box N k), P.IsProper →
    ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
    Thr q ≤ m → m ≤ P.width →
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ Exp q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (Q j).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤ 2 * (m : Real) ^ (-Exp q) * N

/-- **Retiled linearity for a family.** One recurrence partition gives
product cells on which every member of the family is linear. -/
theorem retiled_linearity_family_of_recurrence_scale {N k q : Nat} [NeZero N] {ι : Type}
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (s zeta : Real) (hs : 0 < s)
    (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hrec : ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, s ≤ (R j).width) ∧
      ∀ a j x, x ∈ (R j).carrier →
        (centeredAbs (mu a x * (R j).commonDiff) : Real) ≤ (2 / s) * N)
    (K : ι → Point N k → Finset (ZMod N)) (G : ι → Finset (Point N k))
    (A : ι → Point N k → Finset (ZMod N)) (f : ι → Point N k → ZMod N → ZMod N)
    (hcover : ∀ c, ∀ x ∈ P.carrier, x ∈ G c → ∀ r ∈ K c x, ∃ a, r = mu a x)
    (hlinear : ∀ c, ∀ x ∈ G c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x))
    (hlarge : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt s ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ c j x, x ∈ (T j).carrier → x ∈ G c → LinearOn ((J j).carrier ∩ A c x) (f c x) := by
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ :=
    section16_short_scale_margin s zeta hs hz hzHalf hlarge
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hTsub, hJlength, hsmall⟩ :=
    proper_retiled_product_of_recurrence P B I i u hI hBstep hIstep hsub hshort hL
      mu s (2 / s) hrec hv hvscale
  refine ⟨M, S, T, J, hpart, ?_, hproduct, ?_⟩
  · intro j
    exact ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩
  · intro c j x hx hxG
    exact hlinear c x hxG v (by omega) (J j) (hJlength j).2
      (product_recurrence_bohr_mem mu (K c) x (J j).step _ zeta v
        (hcover c x (hTsub j hx) hxG) (fun a => hsmall a j x hx) hvbudget)

/-- The family form of `Section16RetiledLinearityBound`. -/
def Section16RetiledLinearityFamilyBound (k q : Nat) (epsilon : Real) (threshold : Nat) : Prop :=
  ∀ (N m : Nat) [NeZero N] (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ),
    P.IsProper → I.IsProper → B.step = (↑u : ZMod N) → I.step = B.step →
    (P.axis i).carrier ⊆ B.carrier → 2 * B.length ≤ N → B.length ≤ I.length →
    ∀ mu : Fin q → Point N k → ZMod N, (∀ a, IsMultilinear (mu a)) →
    threshold ≤ m → m ≤ P.width →
    ∀ (ι : Type) (K : ι → Point N k → Finset (ZMod N)) (G : ι → Finset (Point N k))
      (A : ι → Point N k → Finset (ZMod N)) (f : ι → Point N k → ZMod N → ZMod N)
      (zeta : Real), 0 < zeta → zeta ≤ 1 / 2 →
    (∀ c, ∀ x ∈ P.carrier, x ∈ G c → ∀ r ∈ K c x, ∃ a, r = mu a x) →
    (∀ c, ∀ x ∈ G c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    1 < (zeta / 2) * Real.sqrt ((m : Real) ^ epsilon) →
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt ((m : Real) ^ epsilon) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ c j x, x ∈ (T j).carrier → x ∈ G c → LinearOn ((J j).carrier ∩ A c x) (f c x)

/-- A recurrence profile gives the family retiled linearity bound at every
graph count, with the same exponent and threshold. -/
theorem Section16RecurrenceProfileWith.retiled_family {k : Nat} {Thr : Nat → Nat}
    {Exp : Nat → Real} (hrec : Section16RecurrenceProfileWith k Thr Exp)
    (hThr : ∀ q, 0 < Thr q) (q : Nat) :
    Section16RetiledLinearityFamilyBound k q (Exp q) (Thr q) := by
  intro N m _ P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hm hmP
    ι K G A f zeta hz hzHalf hcover hlinear hlarge
  have hm0 : 0 < m := (hThr q).trans_le hm
  have hmR : (0 : Real) < m := by exact_mod_cast hm0
  apply retiled_linearity_family_of_recurrence_scale P B I i u hI hBstep hIstep hsub hshort hL
    mu _ zeta (Real.rpow_pos_of_pos hmR _) hz hzHalf _ K G A f hcover hlinear hlarge
  simpa only [Real.rpow_neg hmR.le, div_eq_mul_inv] using
    hrec N q m P hP mu hmu hm hmP

/-- A family bound gives the single-function bound. -/
theorem Section16RetiledLinearityFamilyBound.single {k q : Nat} {epsilon : Real} {thr : Nat}
    (h : Section16RetiledLinearityFamilyBound k q epsilon thr) :
    Section16RetiledLinearityBound k q epsilon thr := by
  intro N m _ P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hm hmP
    K G A f zeta hz hzHalf hcover hlinear hlarge
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hlin⟩ :=
    h N m P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hm hmP Unit
      (fun _ => K) (fun _ => G) (fun _ => A) (fun _ => f) zeta hz hzHalf
      (fun _ => hcover) (fun _ => hlinear) hlarge
  exact ⟨M, S, T, J, hpart, hproper, hproduct, fun j x hx hxG => hlin () j x hx hxG⟩

end LeanProofs.GowersSzemeredi
