import GowersSzemeredi.Proofs03Basic

/-! Modulus-independent cube patterns in a short interval. The no-wrap
hypothesis is explicit and applies in every cube dimension. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- The origin and coordinate vertices of a Boolean cube. -/
def cubeZero (d : Nat) : Fin d → Bool := fun _ => false

def cubeUnit {d : Nat} (i : Fin d) : Fin d → Bool := fun j => decide (j = i)

@[simp] theorem cubeArgument_zero {N d : Nat} (s : ZMod N) (a : Point N d) :
    cubeArgument s a (cubeZero d) = s := by simp [cubeArgument, cubeZero]

@[simp] theorem cubeArgument_unit {N d : Nat} (s : ZMod N) (a : Point N d) (i : Fin d) :
    cubeArgument s a (cubeUnit i) = s - a i := by simp [cubeArgument, cubeUnit]

private theorem cube_ite_sub {N : Nat} (b : Bool) (x y : ZMod N) :
    (if b then x - y else 0) = (if b then x else 0) - (if b then y else 0) := by
  cases b <;> simp

/-- The affine relation determining every vertex from the origin and its
coordinate neighbors, expressed using only nonnegative sums. -/
theorem cubeArgument_anchor_relation {N d : Nat} (s : ZMod N) (a : Point N d)
    (e : Fin d → Bool) :
    cubeArgument s a e + (∑ i, if e i then s else 0) =
      s + ∑ i, if e i then cubeArgument s a (cubeUnit i) else 0 := by
  simp_rw [cubeArgument_unit, cube_ite_sub]
  unfold cubeArgument
  rw [Finset.sum_sub_distrib]
  abel

/-- A cube with every vertex represented by an index below L. The equations
are ordinary natural-number equalities and therefore independent of modulus. -/
def IsIntervalCube {L d : Nat} (v : (Fin d → Bool) → Fin L) : Prop :=
  ∀ e, (v e : Nat) + (∑ i, if e i then (v (cubeZero d) : Nat) else 0) =
    (v (cubeZero d) : Nat) + ∑ i, if e i then (v (cubeUnit i) : Nat) else 0

abbrev IntervalCube (L d : Nat) := {v : (Fin d → Bool) → Fin L // IsIntervalCube v}

/-- A modular cube whose vertex representatives lie in [0,L). -/
abbrev SupportedIntervalCube (N L d : Nat) [NeZero N] :=
  {p : Point N d × ZMod N // ∀ e, (cubeArgument p.2 p.1 e).val < L}

/-- Sums appearing in an affine cube relation remain below (d+1)*L. -/
theorem interval_cube_sum_lt {L d : Nat} (s : Fin L) (u : Fin d → Fin L)
    (e : Fin d → Bool) :
    (s : Nat) + (∑ i, if e i then (u i : Nat) else 0) < (d + 1) * L := by
  have hsum : (∑ i, if e i then (u i : Nat) else 0) ≤ d * L := by
    calc
      _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
      _ = _ := by simp
  have hs := s.isLt
  nlinarith only [hs, hsum]

/-- The representatives of a supported modular cube satisfy the exact
integer cube equations when (d+1)*L<=N. -/
def SupportedIntervalCube.toInterval {N L d : Nat} [NeZero N]
    (hsize : (d + 1) * L ≤ N) (p : SupportedIntervalCube N L d) : IntervalCube L d := by
  let v : (Fin d → Bool) → Fin L := fun e => ⟨(cubeArgument p.1.2 p.1.1 e).val, p.2 e⟩
  refine ⟨v, fun e => ?_⟩
  have hcast (e : Fin d → Bool) : ((v e : Nat) : ZMod N) = cubeArgument p.1.2 p.1.1 e :=
    ZMod.natCast_zmod_val _
  have heq : (((v e : Nat) + (∑ i, if e i then (v (cubeZero d) : Nat) else 0) : Nat) : ZMod N) =
      (((v (cubeZero d) : Nat) + (∑ i, if e i then (v (cubeUnit i) : Nat) else 0) : Nat) : ZMod N) := by
    push_cast
    simp_rw [hcast, cubeArgument_zero]
    exact cubeArgument_anchor_relation p.1.2 p.1.1 e
  have hl := (interval_cube_sum_lt (v e) (fun _ => v (cubeZero d)) e).trans_le hsize
  have hr := (interval_cube_sum_lt (v (cubeZero d)) (fun i => v (cubeUnit i)) e).trans_le hsize
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ N).mp heq
  simpa only [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hmod

/-- Embed an integer cube pattern in any sufficiently large cyclic group. -/
def IntervalCube.toSupported {N L d : Nat} [NeZero N]
    (hsize : L ≤ N) (v : IntervalCube L d) : SupportedIntervalCube N L d := by
  let s : ZMod N := (v.1 (cubeZero d) : Nat)
  let a : Point N d := fun i => s - ((v.1 (cubeUnit i) : Nat) : ZMod N)
  have heq (e : Fin d → Bool) : cubeArgument s a e = ((v.1 e : Nat) : ZMod N) := by
    have hc := congrArg (fun n : Nat => (n : ZMod N)) (v.2 e)
    push_cast at hc
    dsimp [cubeArgument, a]
    simp_rw [cube_ite_sub]
    rw [Finset.sum_sub_distrib]
    dsimp [s] at *
    linear_combination -hc
  refine ⟨(a, s), fun e => ?_⟩
  rw [heq, ZMod.val_natCast_of_lt ((v.1 e).isLt.trans_le hsize)]
  exact (v.1 e).isLt

/-- The embedded cube has exactly the prescribed vertices. -/
theorem IntervalCube.toSupported_vertex {N L d : Nat} [NeZero N]
    (hsize : L ≤ N) (v : IntervalCube L d) (e : Fin d → Bool) :
    cubeArgument (v.toSupported hsize).1.2 (v.toSupported hsize).1.1 e =
      ((v.1 e : Nat) : ZMod N) := by
  have hc := congrArg (fun n : Nat => (n : ZMod N)) (v.2 e)
  push_cast at hc
  change cubeArgument ((v.1 (cubeZero d) : Nat) : ZMod N)
    (fun i => ((v.1 (cubeZero d) : Nat) : ZMod N) - ((v.1 (cubeUnit i) : Nat) : ZMod N)) e = _
  unfold cubeArgument
  simp_rw [cube_ite_sub]
  rw [Finset.sum_sub_distrib]
  linear_combination -hc

/-- Exact equivalence between modular cubes in a short interval and integer
cube patterns. In particular, no new cubes appear on changing large modulus. -/
def intervalCubeEquiv {N L d : Nat} [NeZero N]
    (hsize : (d + 1) * L ≤ N) : SupportedIntervalCube N L d ≃ IntervalCube L d where
  toFun := SupportedIntervalCube.toInterval hsize
  invFun := IntervalCube.toSupported ((Nat.le_mul_of_pos_left L (by omega)).trans hsize)
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change ((cubeArgument p.1.2 p.1.1 (cubeZero d)).val : ZMod N) -
        ((cubeArgument p.1.2 p.1.1 (cubeUnit i)).val : ZMod N) = p.1.1 i
      simp only [ZMod.natCast_zmod_val, cubeArgument_zero, cubeArgument_unit]
      abel
    · change ((cubeArgument p.1.2 p.1.1 (cubeZero d)).val : ZMod N) = p.1.2
      simp only [ZMod.natCast_zmod_val, cubeArgument_zero]
  right_inv v := by
    apply Subtype.ext
    funext e
    apply Fin.ext
    change (cubeArgument _ _ e).val = (v.1 e : Nat)
    rw [IntervalCube.toSupported_vertex]
    exact ZMod.val_natCast_of_lt ((v.1 e).isLt.trans_le
      ((Nat.le_mul_of_pos_left L (by omega)).trans hsize))

end LeanProofs.GowersSzemeredi
