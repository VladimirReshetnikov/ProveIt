import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.PolynomialBisection

/-!
# Fraction-free synthetic division and finite rational root bounds

Dependency of `foundations/ipra_finite_demand`, Section 5,
`thm:general-norm`: the finite distinct-root bound used before the norm
matrix argument.  Degrees in this module are fixed external naturals.
Coefficient codes, the supplied root list and its length, all numerators,
and all independently positive rational denominators are internal data.
Coefficients are signed numerators over a common nonzero coefficient
denominator; that common factor does not affect the zero equations.
The explicit degree selects the first `degree+1` decoded coefficients.

The polynomial and root codes below use a length paired with a forward
paired list.  This is an explicit coding convention, distinct from the
reverse-list convention of `MasterCertificate.sequence`; the decoder and
the generated synthetic quotient's decoding equations are proved here.

The fraction-free quotient is computed from the coefficients and one
rational root.  Neither a factorization nor the quotient's values at the
other roots are supplied as hypotheses.  The proof removes one actual
linear factor at a time and uses object-theory integer cancellation.
The determinant and fiber-multiplicity parts of `thm:general-norm` are
separate dependencies and are not claimed here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.PolynomialFiniteRoots

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (drop drop_zero drop_push subst_drop)
open LeanProofs.IPRA.Analysis.PolynomialBisection
  (naturalPower subst_naturalPower naturalPower_positive pack unpack subst_pack subst_unpack)

variable {n : ℕ} {Γ : List (Fm PTm n)}

namespace RingModel

variable {R : Type*} [CommRing R]

def H : List R → R → R → R
  | [], _, _ => 0
  | c :: cs, a, D => c * D ^ cs.length + a * H cs a D

def quotient : List R → R → R → List R
  | [], _, _ => []
  | [_], _, _ => []
  | _ :: c :: cs, b, B => H (c :: cs) b B :: (quotient (c :: cs) b B).map (B * ·)

def leading : List R → R
  | [] => 0
  | [a] => a
  | _ :: b :: bs => leading (b :: bs)

theorem H_scale (p : List R) (a D t : R) : H (p.map (t * ·)) a D = t * H p a D := by
  induction p with
  | nil => simp [H]
  | cons c cs ih => simp only [List.map_cons, H, List.length_map, ih]; ring

theorem quotient_length (p : List R) (b B : R) :
    (quotient p b B).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds => simp only [quotient, List.length_cons, List.length_map, ih]; omega

theorem division (c : R) (cs : List R) (a A b B : R) :
    B ^ cs.length * H (c :: cs) a A - A ^ cs.length * H (c :: cs) b B =
      (B * a - b * A) * H (quotient (c :: cs) b B) a A := by
  induction cs generalizing c with
  | nil => simp [H, quotient]
  | cons d ds ih =>
    have e := ih d
    simp only [H, quotient, List.length_cons, List.length_map, quotient_length,
      Nat.add_sub_cancel, H_scale, pow_succ] at e ⊢
    linear_combination (B * a) * e

theorem leading_scale (p : List R) (t : R) :
    leading (p.map (t * ·)) = t * leading p := by
  induction p with
  | nil => simp [leading]
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds => simpa only [List.map_cons, leading] using ih

theorem leading_quotient (c d : R) (cs : List R) (b B : R) :
    leading (quotient (c :: d :: cs) b B) = B ^ cs.length * leading (c :: d :: cs) := by
  induction cs generalizing c d with
  | nil => simp [quotient, H, leading]
  | cons e es ih =>
    simp only [quotient, List.map_cons, leading, List.length_cons, pow_succ]
    change leading ((quotient (d :: e :: es) b B).map (B * ·)) = _
    rw [leading_scale, ih d e]
    simp only [leading]
    ring

end RingModel

/-- Homogeneous numerator of a coefficient list, including the empty list. -/
def homogeneous : List (ZT n) → ZT n → PTm n → ZT n
  | [], _, _ => ZT.natLit 0
  | c :: cs, a, D => c * ZT.ofNat (naturalPower D cs.length) + a * homogeneous cs a D

/-- Actual fraction-free synthetic quotient at `b/B`. -/
def quotient : List (ZT n) → ZT n → PTm n → List (ZT n)
  | [], _, _ => []
  | [_], _, _ => []
  | _ :: c :: cs, b, B => homogeneous (c :: cs) b B :: (quotient (c :: cs) b B).map (ZT.ofNat B * ·)

def leading : List (ZT n) → ZT n
  | [] => ZT.natLit 0
  | [a] => a
  | _ :: b :: bs => leading (b :: bs)

@[simp] theorem quotient_length (p : List (ZT n)) (b : ZT n) (B : PTm n) :
    (quotient p b B).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds => simp only [quotient, List.length_cons, List.length_map, ih]; omega

@[simp] theorem toZ_power (D : PTm n) (k : ℕ) :
    Groth.ι (Q.mk Γ (naturalPower D k)) = Groth.ι (Q.mk Γ D) ^ k := by
  induction k with
  | zero => simp [naturalPower, Q.mk_one]
  | succ k ih => simp only [naturalPower, Q.mk_mul, map_mul, ih, pow_succ]

@[simp] theorem toZ_homogeneous (p : List (ZT n)) (a : ZT n) (D : PTm n) :
    ZT.toZ Γ (homogeneous p a D) =
      RingModel.H (p.map (ZT.toZ Γ)) (ZT.toZ Γ a) (Groth.ι (Q.mk Γ D)) := by
  induction p with
  | nil => simp [homogeneous, RingModel.H]
  | cons c cs ih => simp only [homogeneous, List.map_cons, RingModel.H, List.length_map,
      ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, toZ_power, ih]

@[simp] theorem toZ_quotient (p : List (ZT n)) (b : ZT n) (B : PTm n) :
    (quotient p b B).map (ZT.toZ Γ) =
      RingModel.quotient (p.map (ZT.toZ Γ)) (ZT.toZ Γ b) (Groth.ι (Q.mk Γ B)) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds =>
      simp only [quotient, RingModel.quotient, List.map_cons, List.map_map, toZ_homogeneous]
      congr 1
      simp only [Function.comp_def, ZT.toZ_mul, ZT.toZ_ofNat]
      simpa only [List.map_map, Function.comp_def, List.map_cons] using
        congrArg (List.map (Groth.ι (Q.mk Γ B) * ·)) ih

@[simp] theorem toZ_leading (p : List (ZT n)) :
    ZT.toZ Γ (leading p) = RingModel.leading (p.map (ZT.toZ Γ)) := by
  induction p with
  | nil => simp [leading, RingModel.leading]
  | cons c cs ih => cases cs with
    | nil => rfl
    | cons d ds => simpa only [leading, RingModel.leading, List.map_cons] using ih

/-- The displayed factor identity is an ordinary object-theory derivation. -/
theorem synthetic_division (c : ZT n) (cs : List (ZT n)) (a b : ZT n) (A B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower B cs.length) * homogeneous (c :: cs) a A -
        ZT.ofNat (naturalPower A cs.length) * homogeneous (c :: cs) b B)
      ((ZT.ofNat B * a - b * ZT.ofNat A) * homogeneous (quotient (c :: cs) b B) a A) := by
  apply ZT.derive
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, toZ_power, toZ_homogeneous, toZ_quotient]
  simpa only [List.map_cons, List.length_map] using
    RingModel.division (ZT.toZ Γ c) (cs.map (ZT.toZ Γ)) (ZT.toZ Γ a)
      (Groth.ι (Q.mk Γ A)) (ZT.toZ Γ b) (Groth.ι (Q.mk Γ B))

theorem synthetic_leading (c d : ZT n) (cs : List (ZT n)) (b : ZT n) (B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (leading (quotient (c :: d :: cs) b B))
      (ZT.ofNat (naturalPower B cs.length) * leading (c :: d :: cs)) := by
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_ofNat, toZ_power, toZ_leading, toZ_quotient]
  simpa only [List.map_cons, List.length_map] using
    RingModel.leading_quotient (ZT.toZ Γ c) (ZT.toZ Γ d) (cs.map (ZT.toZ Γ))
      (ZT.toZ Γ b) (Groth.ι (Q.mk Γ B))

/-- Another distinct rational zero is a zero of the computed quotient. -/
theorem quotient_root (c : ZT n) (cs : List (ZT n)) (a b : ZT n) (A B : PTm n)
    (ha : Γ ⊢[PRAAx] ZT.eq (homogeneous (c :: cs) a A) (ZT.natLit 0))
    (hb : Γ ⊢[PRAAx] ZT.eq (homogeneous (c :: cs) b B) (ZT.natLit 0))
    (hne : Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat B * a) (b * ZT.ofNat A))) :
    Γ ⊢[PRAAx] ZT.eq (homogeneous (quotient (c :: cs) b B) a A) (ZT.natLit 0) := by
  apply zt_mul_cancel_sub hne
  apply ZT.derive
  have factor := ZT.toZ_eq (synthetic_division (Γ := Γ) c cs a b A B)
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at factor ea eb ⊢
  rw [ea, eb] at factor
  simp only [Nat.cast_zero] at factor ⊢
  linear_combination -factor

theorem positive_nonzero (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat D) (ZT.natLit 0)) :=
  zt_ofNat_nonzero hD

/-- A polynomial represented by `d+1` coefficients which has `d+1`
pairwise distinct rational zeros has zero leading coefficient.  All
denominators are independent internal positive terms. -/
theorem leading_vanishes (d : ℕ) (p : List (ZT n)) (hlen : p.length = d + 1)
    (a : Fin (d + 1) → ZT n) (D : Fin (d + 1) → PTm n)
    (hD : ∀ i, Γ ⊢[PRAAx] le one (D i))
    (hz : ∀ i, Γ ⊢[PRAAx] ZT.eq (homogeneous p (a i) (D i)) (ZT.natLit 0))
    (hne : ∀ i j, j.val < i.val →
      (Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat (D j) * a i) (a j * ZT.ofNat (D i))))) :
    Γ ⊢[PRAAx] ZT.eq (leading p) (ZT.natLit 0) := by
  induction d generalizing p with
  | zero =>
    cases p with
    | nil => simp at hlen
    | cons c cs =>
      have hc : cs = [] := by simpa using hlen
      subst cs
      apply ZT.derive
      simpa [homogeneous, leading, naturalPower] using ZT.toZ_eq (hz 0)
  | succ d ih =>
    cases p with
    | nil => simp at hlen
    | cons c cs =>
      cases cs with
      | nil => simp at hlen
      | cons e es =>
        let q := quotient (c :: e :: es) (a 0) (D 0)
        have hq : q.length = d + 1 := by
          dsimp [q]
          rw [quotient_length, hlen]
          omega
        have roots : ∀ i : Fin (d + 1),
            Γ ⊢[PRAAx] ZT.eq (homogeneous q (a i.succ) (D i.succ)) (ZT.natLit 0) := by
          intro i
          exact quotient_root c (e :: es) (a i.succ) (a 0) (D i.succ) (D 0)
            (hz i.succ) (hz 0) (hne i.succ 0 (Nat.succ_pos i.val))
        have vanished := ih q hq (fun i => a i.succ) (fun i => D i.succ)
          (fun i => hD i.succ) roots (fun i j hij => hne i.succ j.succ (Nat.succ_lt_succ hij))
        have productZero : Γ ⊢[PRAAx] ZT.eq
            (ZT.ofNat (naturalPower (D 0) es.length) * leading (c :: e :: es)) (ZT.natLit 0) := by
          apply ZT.derive
          exact (ZT.toZ_eq (synthetic_leading (Γ := Γ) c e es (a 0) (D 0))).symm.trans (ZT.toZ_eq vanished)
        exact zt_mul_cancel_left
          (positive_nonzero _ (naturalPower_positive _ _ (hD 0))) productZero

/-! ## Actual forward-list codes and the generated quotient program -/

def forward : List (PTm n) → PTm n
  | [] => zero
  | c :: cs => pairT c (forward cs)

def encodeNaturals (p : List (PTm n)) : PTm n := pairT (num p.length) (forward p)

/-- Arbitrary internal lookup index in the explicit forward-list convention. -/
def read (code i : PTm n) : PTm n := fstT (drop i (sndT code))

def encode (p : List (ZT n)) : PTm n := encodeNaturals (p.map pack)
def coefficient (code i : PTm n) : ZT n := unpack (read code i)

ipra_subst read

ipra_subst coefficient

theorem forward_lookup (p : List (PTm n)) (i : Fin p.length) :
    Γ ⊢[PRAAx] fstT (drop (num i.val) (forward p)) ≐ p.get i := by
  induction p with
  | nil => exact i.elim0
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (drop_zero _).fstE
    · exact (congrFst (drop_push (num j.val) c (forward cs))).eqTrans (ih j)

theorem read_encode (p : List (PTm n)) (i : ℕ) (hi : i < p.length) :
    Γ ⊢[PRAAx] read (encodeNaturals p) (num i) ≐ p.get ⟨i, hi⟩ :=
  (congrFst (congrAp2 _ (.eqRefl _) (snd_pair _ _))).eqTrans (forward_lookup p ⟨i, hi⟩)

theorem coefficient_encode (p : List (ZT n)) (i : ℕ) (hi : i < p.length) :
    Γ ⊢[PRAAx] ZT.eq (coefficient (encode p) (num i)) (p.get ⟨i, hi⟩) := by
  have er := read_encode (Γ := Γ) (p.map pack) i (by simpa using hi)
  simp only [List.get_eq_getElem, List.getElem_map] at er
  change Γ ⊢[PRAAx] read (encode p) (num i) ≐ pack (p.get ⟨i, hi⟩) at er
  apply ZT.derive
  change Groth.ι (Q.mk Γ (fstT (read (encode p) (num i)))) -
    Groth.ι (Q.mk Γ (sndT (read (encode p) (num i)))) = _
  rw [natEq er.fstE, natEq er.sndE]
  rfl

theorem encoded_length (p : List (ZT n)) : Γ ⊢[PRAAx] fstT (encode p) ≐ num p.length := by
  simpa only [encode, encodeNaturals, List.length_map] using fst_pair (Γ := Γ) (num (p.map pack).length) (forward (p.map pack))

/-- Decode precisely the specified finite coefficient prefix. -/
def coefficients (count : ℕ) (code : PTm n) : List (ZT n) :=
  List.ofFn (fun i : Fin count => coefficient code (num i.val))

@[simp] theorem coefficients_length (count : ℕ) (code : PTm n) :
    (coefficients count code).length = count := List.length_ofFn

def evaluate (degree : ℕ) (code : PTm n) (a : ZT n) (D : PTm n) : ZT n :=
  homogeneous (coefficients (degree + 1) code) a D

private theorem leading_append_singleton (p : List (ZT n)) (c : ZT n) : leading (p ++ [c]) = c := by
  induction p with
  | nil => rfl
  | cons a ps ih => cases ps with
    | nil => rfl
    | cons b bs => simpa only [List.cons_append, leading] using ih

/-- The nonzero leading-coefficient test is the actual last decoded entry. -/
theorem leading_coefficients (degree : ℕ) (code : PTm n) :
    leading (coefficients (degree + 1) code) = coefficient code (num degree) := by
  unfold coefficients
  rw [List.ofFn_succ_last, leading_append_singleton]
  rfl

def quotientCode (degree : ℕ) (code : PTm n) (b : ZT n) (B : PTm n) : PTm n :=
  encode (quotient (coefficients (degree + 1) code) b B)

theorem decoded_encode (p : List (ZT n)) (count : ℕ) (hlen : p.length = count) :
    (coefficients count (encode p)).map (ZT.toZ Γ) = p.map (ZT.toZ Γ) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp only [coefficients, List.getElem_map, List.getElem_ofFn]
    exact ZT.toZ_eq (coefficient_encode (Γ := Γ) p i (by simpa using hj))

/-- The generated coefficient code really decodes to the computed quotient. -/
theorem evaluate_quotientCode (d : ℕ) (code : PTm n) (a b : ZT n) (A B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (evaluate d (quotientCode (d + 1) code b B) a A)
      (homogeneous (quotient (coefficients (d + 2) code) b B) a A) := by
  apply ZT.derive
  simp only [evaluate, quotientCode, toZ_homogeneous]
  rw [decoded_encode _ (d + 1) (by simp)]

theorem quotientCode_length (d : ℕ) (code : PTm n) (b : ZT n) (B : PTm n) :
    Γ ⊢[PRAAx] fstT (quotientCode (d + 1) code b B) ≐ num (d + 1) := by
  simpa only [quotientCode, quotient_length, coefficients_length, Nat.add_sub_cancel] using
    encoded_length (Γ := Γ) (quotient (coefficients (d + 1 + 1) code) b B)

theorem synthetic_division_length (degree : ℕ) (p : List (ZT n)) (hlen : p.length = degree + 1)
    (a b : ZT n) (A B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower B degree) * homogeneous p a A -
        ZT.ofNat (naturalPower A degree) * homogeneous p b B)
      ((ZT.ofNat B * a - b * ZT.ofNat A) * homogeneous (quotient p b B) a A) := by
  cases p with
  | nil => simp at hlen
  | cons c cs =>
    have hc : cs.length = degree := by simpa using hlen
    simpa only [hc] using synthetic_division (Γ := Γ) c cs a b A B

/-- Exact synthetic division with the actual coded quotient evaluator. -/
theorem coded_synthetic_division (d : ℕ) (code : PTm n) (a b : ZT n) (A B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower B (d + 1)) * evaluate (d + 1) code a A -
        ZT.ofNat (naturalPower A (d + 1)) * evaluate (d + 1) code b B)
      ((ZT.ofNat B * a - b * ZT.ofNat A) * evaluate d (quotientCode (d + 1) code b B) a A) := by
  apply ZT.derive
  have e := ZT.toZ_eq (synthetic_division_length (Γ := Γ) (d + 1)
    (coefficients (d + 2) code) (by simp) a b A B)
  simp only [ZT.toZ_sub, ZT.toZ_mul] at e ⊢
  rw [ZT.toZ_eq (evaluate_quotientCode (Γ := Γ) d code a b A B)]
  exact e

/-- Root removal refers to the actual generated quotient code. -/
theorem coded_quotient_root (d : ℕ) (code : PTm n) (a b : ZT n) (A B : PTm n)
    (ha : Γ ⊢[PRAAx] ZT.eq (evaluate (d + 1) code a A) (ZT.natLit 0))
    (hb : Γ ⊢[PRAAx] ZT.eq (evaluate (d + 1) code b B) (ZT.natLit 0))
    (hne : Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat B * a) (b * ZT.ofNat A))) :
    Γ ⊢[PRAAx] ZT.eq (evaluate d (quotientCode (d + 1) code b B) a A) (ZT.natLit 0) := by
  apply zt_mul_cancel_sub hne
  apply ZT.derive
  have factor := ZT.toZ_eq (coded_synthetic_division (Γ := Γ) d code a b A B)
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at factor ea eb ⊢
  rw [ea, eb] at factor
  simp only [Nat.cast_zero] at factor ⊢
  linear_combination -factor

theorem synthetic_leading_length (d : ℕ) (p : List (ZT n)) (hlen : p.length = d + 2)
    (b : ZT n) (B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (leading (quotient p b B))
      (ZT.ofNat (naturalPower B d) * leading p) := by
  cases p with
  | nil => simp at hlen
  | cons c cs => cases cs with
    | nil => simp at hlen
    | cons e es =>
      have he : es.length = d := by simpa [Nat.add_assoc] using hlen
      simpa only [he] using synthetic_leading (Γ := Γ) c e es b B

/-- Exact degree control for the coded quotient, including the scale factor
which remains nonzero when the root denominator is positive. -/
theorem coded_quotient_leading (d : ℕ) (code : PTm n) (b : ZT n) (B : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (coefficient (quotientCode (d + 1) code b B) (num d))
      (ZT.ofNat (naturalPower B d) * coefficient code (num (d + 1))) := by
  apply ZT.derive
  have e := ZT.toZ_eq (synthetic_leading_length (Γ := Γ) d
    (coefficients (d + 2) code) (by simp) b B)
  have decoded : ZT.toZ Γ (coefficient (quotientCode (d + 1) code b B) (num d)) =
      ZT.toZ Γ (leading (quotient (coefficients (d + 2) code) b B)) := by
    rw [← leading_coefficients d]
    simp only [toZ_leading, quotientCode]
    rw [decoded_encode _ (d + 1) (by simp)]
  rw [decoded]
  simpa only [leading_coefficients] using e

@[simp] theorem subst_homogeneous {m : ℕ} (σ : Fin n → PTm m)
    (p : List (ZT n)) (a : ZT n) (D : PTm n) :
    (homogeneous p a D).subst σ = homogeneous (p.map (ZT.subst σ)) (a.subst σ) (Syn.subst σ D) := by
  induction p with
  | nil => simp [homogeneous]
  | cons c cs ih => simp only [homogeneous, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat,
      subst_naturalPower, List.map_cons, List.length_map, ih]

@[simp] theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m)
    (p : List (ZT n)) (b : ZT n) (B : PTm n) :
    (quotient p b B).map (ZT.subst σ) = quotient (p.map (ZT.subst σ)) (b.subst σ) (Syn.subst σ B) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds =>
      simp only [quotient, List.map_cons, List.map_map, subst_homogeneous]
      congr 1
      simp only [Function.comp_def, ZT.subst_mul, ZT.subst_ofNat]
      simpa only [List.map_map, Function.comp_def, List.map_cons] using
        congrArg (List.map (ZT.ofNat (Syn.subst σ B) * ·)) ih

@[simp] theorem subst_forward {m : ℕ} (σ : Fin n → PTm m) (p : List (PTm n)) :
    Syn.subst σ (forward p) = forward (p.map (Syn.subst σ)) := by
  induction p with
  | nil => simp [forward]
  | cons c cs ih => simp [forward, ih]

@[simp] theorem subst_encode {m : ℕ} (σ : Fin n → PTm m) (p : List (ZT n)) :
    Syn.subst σ (encode p) = encode (p.map (ZT.subst σ)) := by
  simp only [encode, encodeNaturals, subst_pairT, LeanProofs.IPRA.PTm.subst_num,
    subst_forward, List.map_map, List.length_map, Function.comp_def, subst_pack]

@[simp] theorem subst_coefficients {m : ℕ} (σ : Fin n → PTm m) (count : ℕ) (code : PTm n) :
    (coefficients count code).map (ZT.subst σ) = coefficients count (Syn.subst σ code) := by
  simp [coefficients, List.map_ofFn, Function.comp_def]

ipra_subst evaluate

ipra_subst quotientCode

/-- One actual fixed primitive-recursive symbol, with runtime arguments
`coefficientCode, rootPositiveNumerator, rootNegativeNumerator, rootDenominator`. -/
def quotientF (degree : ℕ) : PR 4 :=
  PTm.toPR (quotientCode degree (var 0) ⟨var 1, var 2⟩ (var 3))

def apply4 (f : PR 4) (a b c d : PTm n) : PTm n := app f ![a, b, c, d]

theorem quotient_program_at (degree : ℕ) (code : PTm n) (b : ZT n) (B : PTm n) :
    Γ ⊢[PRAAx] apply4 (quotientF degree) code b.pos b.neg B ≐ quotientCode degree code b B := by
  have h := toPR_eq (Γ := Γ) (quotientCode degree (var 0) ⟨var 1, var 2⟩ (var 3)) ![code, b.pos, b.neg, B]
  simpa [quotientF, apply4, ZT.subst] using h

theorem coded_quotient_nonzero (d : ℕ) (code : PTm n) (b : ZT n) (B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hlead : Γ ⊢[PRAAx] neg (ZT.eq (coefficient code (num (d + 1))) (ZT.natLit 0))) :
    Γ ⊢[PRAAx] neg (ZT.eq (coefficient (quotientCode (d + 1) code b B) (num d)) (ZT.natLit 0)) := by
  refine .impI (.impE hlead.wk ?_)
  have productZero : ZT.eq (coefficient (quotientCode (d + 1) code b B) (num d)) (ZT.natLit 0) :: Γ
      ⊢[PRAAx] ZT.eq (ZT.ofNat (naturalPower B d) * coefficient code (num (d + 1))) (ZT.natLit 0) := by
    apply ZT.derive
    have e := ZT.toZ_eq (coded_quotient_leading
      (Γ := ZT.eq (coefficient (quotientCode (d + 1) code b B) (num d)) (ZT.natLit 0) :: Γ) d code b B)
    have z := ZT.toZ_eq (Prf.hyp0 :
      ZT.eq (coefficient (quotientCode (d + 1) code b B) (num d)) (ZT.natLit 0) :: Γ ⊢[PRAAx] _)
    exact e.symm.trans z
  exact zt_mul_cancel_left (positive_nonzero _ (naturalPower_positive _ _ hB.wk)) productZero

/-- Each root entry is `pairT (pack numerator) positiveDenominator`. -/
def rootNumerator (roots i : PTm n) : ZT n := unpack (fstT (read roots i))
def rootDenominator (roots i : PTm n) : PTm n := sndT (read roots i)

ipra_subst rootNumerator

ipra_subst rootDenominator

def rationalDistinct (a : ZT n) (A : PTm n) (b : ZT n) (B : PTm n) : Fm PTm n :=
  neg (ZT.eq (ZT.ofNat B * a) (b * ZT.ofNat A))

ipra_subst rationalDistinct

def rootsCondition (degree : ℕ) (code roots : PTm n) : Fm PTm n :=
  .all (lt (var 0) (fstT (Syn.shift roots)) ⟶
    (le one (rootDenominator (Syn.shift roots) (var 0)) ⋏
      ZT.eq (evaluate degree (Syn.shift code) (rootNumerator (Syn.shift roots) (var 0))
        (rootDenominator (Syn.shift roots) (var 0))) (ZT.natLit 0)))

def distinctCondition (roots : PTm n) : Fm PTm n :=
  .all (lt (var 0) (fstT (Syn.shift roots)) ⟶
    .all (lt (var 0) (var 1) ⟶
      rationalDistinct (rootNumerator (Syn.shift (Syn.shift roots)) (var 1))
        (rootDenominator (Syn.shift (Syn.shift roots)) (var 1))
        (rootNumerator (Syn.shift (Syn.shift roots)) (var 0))
        (rootDenominator (Syn.shift (Syn.shift roots)) (var 0))))

theorem roots_at (degree : ℕ) (code roots i : PTm n)
    (hz : Γ ⊢[PRAAx] rootsCondition degree code roots) (hi : Γ ⊢[PRAAx] lt i (fstT roots)) :
    Γ ⊢[PRAAx] le one (rootDenominator roots i) ⋏
      ZT.eq (evaluate degree code (rootNumerator roots i) (rootDenominator roots i)) (ZT.natLit 0) := by
  have e := Prf.allE i hz
  simp [rootsCondition] at e
  exact Prf.impE e hi

theorem distinct_at (roots i j : PTm n) (hd : Γ ⊢[PRAAx] distinctCondition roots)
    (hi : Γ ⊢[PRAAx] lt i (fstT roots)) (hj : Γ ⊢[PRAAx] lt j i) :
    Γ ⊢[PRAAx] rationalDistinct (rootNumerator roots i) (rootDenominator roots i)
      (rootNumerator roots j) (rootDenominator roots j) := by
  have e := Prf.allE i hd
  simp [distinctCondition] at e
  have e2 := Prf.allE j (Prf.impE e hi)
  simp at e2
  have hs : Syn.subst (Syn.up (Syn.inst i)) (Syn.shift (Syn.shift roots)) = Syn.shift roots := by
    rw [Syn.subst_shift]
    simp only [Syn.up_succ]
    rw [Syn.subst_shift]
    simp only [Syn.inst_succ, Syn.shift, Syn.subst_var]
  simp only [hs, Syn.subst_inst_shift] at e2
  exact Prf.impE e2 hj

theorem numeral_le {i j : ℕ} (h : i ≤ j) : Γ ⊢[PRAAx] le (num i) (num j) := by
  apply le_of_eq_add (d := num (j - i))
  apply deriveNat
  ipra_simps
  have e : j = i + (j - i) := (Nat.add_sub_of_le h).symm
  simpa only [Nat.cast_add] using congrArg (fun k : ℕ => (k : Groth (Q Γ))) e

theorem numeral_lt {i j : ℕ} (h : i < j) : Γ ⊢[PRAAx] lt (num i) (num j) :=
  numeral_le (Nat.succ_le_of_lt h)

/-- Exact finite-list root bound.  The supplied list length is an arbitrary
internal number, rather than the size of an external Lean tuple. -/
theorem finite_root_bound (degree : ℕ) (code roots : PTm n)
    (hlead : Γ ⊢[PRAAx] neg (ZT.eq (coefficient code (num degree)) (ZT.natLit 0)))
    (hz : Γ ⊢[PRAAx] rootsCondition degree code roots)
    (hd : Γ ⊢[PRAAx] distinctCondition roots) :
    Γ ⊢[PRAAx] le (fstT roots) (num degree) := by
  refine .orE (lt_or_le (num degree) (fstT roots)) ?_ Prf.hyp0
  let Δ := lt (num degree) (fstT roots) :: Γ
  have inside : ∀ i : Fin (degree + 1), Δ ⊢[PRAAx] lt (num i.val) (fstT roots) := by
    intro i
    exact lt_of_le_of_lt (numeral_le (Nat.le_of_lt_succ i.isLt)) Prf.hyp0
  have rootsAt : ∀ i : Fin (degree + 1), Δ ⊢[PRAAx]
      le one (rootDenominator roots (num i.val)) ⋏
        ZT.eq (evaluate degree code (rootNumerator roots (num i.val))
          (rootDenominator roots (num i.val))) (ZT.natLit 0) :=
    fun i => roots_at degree code roots (num i.val) hz.wk (inside i)
  have vanished := leading_vanishes degree (coefficients (degree + 1) code) (by simp)
    (fun i => rootNumerator roots (num i.val)) (fun i => rootDenominator roots (num i.val))
    (fun i => Prf.andE₁ (rootsAt i)) (fun i => Prf.andE₂ (rootsAt i))
    (fun i j hij => distinct_at roots (num i.val) (num j.val) hd.wk (inside i) (numeral_lt hij))
  rw [leading_coefficients] at vanished
  exact .botE _ (.impE hlead.wk vanished)

def finiteRootFormula (degree : ℕ) : Fm PTm 2 :=
  neg (ZT.eq (coefficient (var 0) (num degree)) (ZT.natLit 0)) ⟶
    rootsCondition degree (var 0) (var 1) ⟶ distinctCondition (var 1) ⟶
      le (fstT (var 1)) (num degree)

theorem finite_root_bound_closed (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (finiteRootFormula degree) :=
  closeUniv 2 (.impI (.impI (.impI (finite_root_bound degree (var 0) (var 1) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

def quotientProgramFormula (d : ℕ) : Fm PTm 4 :=
  (apply4 (quotientF (d + 1)) (var 0) (var 1) (var 2) (var 3) ≐
    quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) ⋏
  (fstT (apply4 (quotientF (d + 1)) (var 0) (var 1) (var 2) (var 3)) ≐ num (d + 1))

theorem quotient_program_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (quotientProgramFormula d) := by
  apply closeUniv 4
  have e := quotient_program_at (Γ := []) (d + 1) (var 0 : PTm 4) ⟨var 1, var 2⟩ (var 3)
  exact .andI e ((congrFst e).eqTrans (quotientCode_length d _ _ _))

def codedDivisionFormula (d : ℕ) : Fm PTm 7 :=
  ZT.eq
    (ZT.ofNat (naturalPower (var 3) (d + 1)) * evaluate (d + 1) (var 0) ⟨var 4, var 5⟩ (var 6) -
      ZT.ofNat (naturalPower (var 6) (d + 1)) * evaluate (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3))
    ((ZT.ofNat (var 3) * (⟨var 4, var 5⟩ : ZT 7) - (⟨var 1, var 2⟩ : ZT 7) * ZT.ofNat (var 6)) *
      evaluate d (quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) ⟨var 4, var 5⟩ (var 6))

theorem coded_synthetic_division_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 (codedDivisionFormula d) :=
  closeUniv 7 (coded_synthetic_division d (var 0) ⟨var 4, var 5⟩ ⟨var 1, var 2⟩ (var 6) (var 3))

def codedRootRemovalFormula (d : ℕ) : Fm PTm 7 :=
  ZT.eq (evaluate (d + 1) (var 0) ⟨var 4, var 5⟩ (var 6)) (ZT.natLit 0) ⟶
  ZT.eq (evaluate (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) (ZT.natLit 0) ⟶
  rationalDistinct ⟨var 4, var 5⟩ (var 6) ⟨var 1, var 2⟩ (var 3) ⟶
  ZT.eq (evaluate d (quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3))
    ⟨var 4, var 5⟩ (var 6)) (ZT.natLit 0)

theorem coded_root_removal_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 (codedRootRemovalFormula d) :=
  closeUniv 7 (.impI (.impI (.impI
    (coded_quotient_root d (var 0) ⟨var 4, var 5⟩ ⟨var 1, var 2⟩ (var 6) (var 3)
      Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

def codedQuotientDegreeFormula (d : ℕ) : Fm PTm 4 :=
  ZT.eq (coefficient (quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) (num d))
    (ZT.ofNat (naturalPower (var 3) d) * coefficient (var 0) (num (d + 1))) ⋏
  (le one (var 3) ⟶
    neg (ZT.eq (coefficient (var 0) (num (d + 1))) (ZT.natLit 0)) ⟶
      ((fstT (quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) ≐ num (d + 1)) ⋏
        neg (ZT.eq (coefficient (quotientCode (d + 1) (var 0) ⟨var 1, var 2⟩ (var 3)) (num d)) (ZT.natLit 0))))

theorem coded_quotient_degree_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (codedQuotientDegreeFormula d) :=
  closeUniv 4 (.andI (coded_quotient_leading d _ _ _)
    (.impI (.impI (.andI (quotientCode_length d _ _ _)
      (coded_quotient_nonzero d _ _ _ Prf.hyp1 Prf.hyp0)))))

#print axioms synthetic_division
#print axioms synthetic_leading
#print axioms quotient_root
#print axioms leading_vanishes
#print axioms coefficient_encode
#print axioms evaluate_quotientCode
#print axioms quotient_program_at
#print axioms quotient_program_closed
#print axioms coded_synthetic_division_closed
#print axioms coded_root_removal_closed
#print axioms coded_quotient_degree_closed
#print axioms finite_root_bound_closed

end LeanProofs.IPRA.Algebra.PolynomialFiniteRoots
