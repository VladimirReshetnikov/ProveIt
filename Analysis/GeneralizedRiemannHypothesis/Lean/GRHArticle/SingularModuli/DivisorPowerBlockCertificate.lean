import GRHArticle.SingularModuli.DivisorPowerPrefixCertificate

/-!
# Checking divisor tables in consecutive blocks

Each block is checked at its original offset. The certificates compose
by concatenation, as do the coefficient lists.
-/

namespace GRHArticle.SingularModuli.DivisorPowerPrefixCertificate

/-- Check a block starting at the given index. -/
def checkBlock (start : ℕ) (rows : List (List (ℕ × ℕ))) : Bool :=
  (rows.zipIdx start).all fun x ↦ decide (RowValid x.2 x.1)

theorem checkBlock_append (start : ℕ) (a b : List (List (ℕ × ℕ))) :
    checkBlock start (a ++ b) = (checkBlock start a && checkBlock (start+a.length) b) := by
  simp only [checkBlock, List.zipIdx_append, List.all_append]

theorem check_eq_zeroBlock (rows : List (List (ℕ × ℕ))) :
    check rows = checkBlock 0 rows := rfl

/-- Compute one block of the divisor-power coefficients. -/
def coefficientsBlock (start k : ℕ) (rows : List (List (ℕ × ℕ))) : List ℕ :=
  (rows.zipIdx start).map fun x ↦ if x.2 = 0 then 0 else witnessSigma k x.1

theorem coefficientsBlock_append (start k : ℕ) (a b : List (List (ℕ × ℕ))) :
    coefficientsBlock start k (a ++ b) =
      coefficientsBlock start k a ++ coefficientsBlock (start+a.length) k b := by
  simp only [coefficientsBlock, List.zipIdx_append, List.map_append]

theorem coefficients_eq_zeroBlock (k : ℕ) (rows : List (List (ℕ × ℕ))) :
    coefficients k rows = coefficientsBlock 0 k rows := by
  exact List.mapIdx_eq_zipIdx_map

/-- Use the least factor test so primality checks do not enumerate all smaller integers. -/
def FastWitnessValid : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, e) :: ws => (2 ≤ p ∧ p.minFac = p) ∧ (p^e).Coprime (witnessProduct ws) ∧ FastWitnessValid ws

instance (ws : List (ℕ × ℕ)) : Decidable (FastWitnessValid ws) :=
  match ws with
  | [] => isTrue trivial
  | (p, e) :: ws => by
    letI := instDecidableFastWitnessValid ws
    unfold FastWitnessValid
    infer_instance

private theorem witnessValid_of_fast {ws : List (ℕ × ℕ)} (h : FastWitnessValid ws) :
    WitnessValid ws := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    rcases w with ⟨p,e⟩
    obtain ⟨hp,hc,hs⟩ := h
    exact ⟨Nat.prime_def_minFac.mpr hp, hc, ih hs⟩

def FastRowValid (i : ℕ) (ws : List (ℕ × ℕ)) : Prop :=
  i = 0 ∨ witnessProduct ws = i ∧ FastWitnessValid ws

instance (i : ℕ) (ws : List (ℕ × ℕ)) : Decidable (FastRowValid i ws) := by
  unfold FastRowValid
  infer_instance

/-- The reduced primality test suffices for each indexed block. -/
def checkBlockFast (start : ℕ) (rows : List (List (ℕ × ℕ))) : Bool :=
  (rows.zipIdx start).all fun x ↦ decide (FastRowValid x.2 x.1)

theorem checkBlock_of_fast (start : ℕ) (rows : List (List (ℕ × ℕ)))
    (h : checkBlockFast start rows = true) : checkBlock start rows = true := by
  unfold checkBlock checkBlockFast at *
  refine List.all_eq_true.mpr fun x hx ↦ decide_eq_true ?_
  have hr := of_decide_eq_true (List.all_eq_true.mp h x hx)
  rcases hr with he | ⟨he,hv⟩
  · exact Or.inl he
  · exact Or.inr ⟨he,witnessValid_of_fast hv⟩

end GRHArticle.SingularModuli.DivisorPowerPrefixCertificate
