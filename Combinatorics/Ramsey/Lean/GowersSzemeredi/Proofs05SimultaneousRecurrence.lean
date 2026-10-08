import GowersSzemeredi.Proofs16Slicing

/-! Simultaneous monomial recurrence in `ZMod N`, from Schmidt's theorem.

The openai/math port proves Schmidt-type simultaneous recurrence as
`OAI.Erdos3.simultaneous_monomial_recurrence` (module
`OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition`,
manifest entry 3295; audited prefix). For each degree `j + 1` it has
constants `K ≥ 1`, `p > 0` such that, for any finite family `α : ι → ℝ` and
`0 < R ≤ 1` with `N ≥ (K (|ι|+1)/R)^(p (|ι|+1)^2)`, some `1 ≤ q ≤ N` puts
every `q^(j+1) α i` within `R` of an integer.

`MonomialRecurrence j` restates that conclusion verbatim, restricted to
`ι = Fin d`, so the port's theorem instantiates it directly. This module
does not import the port, which is not built on this machine. It derives
the `ZMod N` form used by Section 5. The exponent `1/(p (d+1)^2)` is
polynomial in the number `d` of simultaneous monomials; Gowers's Lemma 5.5
iterated over `d` polynomials is exponential in `d`. That difference is
item (D) of research notes Part J (J.3). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Schmidt's simultaneous monomial recurrence of degree `j + 1`, in the
exact form of `OAI.Erdos3.simultaneous_monomial_recurrence j` (for
`ι = Fin d`). -/
def MonomialRecurrence (j : Nat) : Prop :=
  ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧
    ∀ (d : Nat) (α : Fin d → Real) (N : Nat) (R : Real), 0 < R → R ≤ 1 →
      (K * ((d : Real) + 1) / R) ^ (p * (d + 1) ^ 2) ≤ N →
      ∃ q : Nat, 0 < q ∧ q ≤ N ∧ ∃ m : Fin d → Int, ∀ i, |(q : Real) ^ (j + 1) * α i - m i| < R

/-- **Simultaneous recurrence in `ZMod N`.** Under `MonomialRecurrence j`,
for `d` residues `a i`, some `1 ≤ q ≤ T` makes every `q^(j+1) a i` have
centered absolute value below `R N`, as soon as `T` passes Schmidt's
threshold. -/
theorem MonomialRecurrence.zmod {j : Nat} (h : MonomialRecurrence j) :
    ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧
      ∀ (N d T : Nat) [NeZero N] (a : Fin d → ZMod N) (R : Real), 0 < R → R ≤ 1 →
        (K * ((d : Real) + 1) / R) ^ (p * (d + 1) ^ 2) ≤ T →
        ∃ q : Nat, 0 < q ∧ q ≤ T ∧
          ∀ i, (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real) < R * N := by
  obtain ⟨K, p, hK, hp, hrec⟩ := h
  refine ⟨K, p, hK, hp, ?_⟩
  intro N d T _ a R hR hR1 hT
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨q, hq, hqT, m, hm⟩ := hrec d (fun i => ((a i).val : Real) / N) T R hR hR1 hT
  refine ⟨q, hq, hqT, fun i => ?_⟩
  -- the residue `q^(j+1) * a i` is represented by the integer
  -- `q^(j+1) * (a i).val`; subtract `m i * N`.
  let z : Int := (q : Int) ^ (j + 1) * ((a i).val : Int)
  have hcast : (((z - m i * N : Int)) : ZMod N) = (q : ZMod N) ^ (j + 1) * a i := by
    simp [z]
  have hreal : (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real) ≤ |(z : Real) - m i * N| := by
    rw [← hcast]
    have h1 := centeredAbs_intCast_le (N := N) (z - m i * N)
    have h2 : (((z - m i * N).natAbs : Nat) : Real) = |(z : Real) - m i * N| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← h2]
    exact_mod_cast h1
  have hid : (z : Real) - m i * N = N * ((q : Real) ^ (j + 1) * (((a i).val : Real) / N) - m i) := by
    simp only [z]
    push_cast
    field_simp
  have hscale : |(z : Real) - m i * N| = N * |(q : Real) ^ (j + 1) * (((a i).val : Real) / N) - m i| := by
    rw [hid, abs_mul, abs_of_pos hN]
  rw [hscale] at hreal
  calc (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real)
      ≤ N * |(q : Real) ^ (j + 1) * (((a i).val : Real) / N) - m i| := hreal
    _ < N * R := mul_lt_mul_of_pos_left (hm i) hN
    _ = R * N := mul_comm _ _

end LeanProofs.GowersSzemeredi
