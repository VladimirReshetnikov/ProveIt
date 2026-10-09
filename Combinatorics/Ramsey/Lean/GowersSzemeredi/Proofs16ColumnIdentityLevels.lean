import GowersSzemeredi.Proofs16ColumnPairComposition

/-! A finite uniform radius schedule for composing local column identities.
Each step removes the intermediate frequencies from the conclusion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnIdentityRadius (d : Nat) (rho : Real) : Nat → Real
  | 0 => rho
  | n+1 => min (columnIdentityRadius d rho n)
      (refinementKernelRadius (4*d) (2*d) rho (columnIdentityRadius d rho n))

def columnIdentityModulusBound (d : Nat) (rho : Real) (n : Nat) : Nat :=
  (Finset.range n).sup (fun j => refinementKernelCap (4*d) (2*d) rho (columnIdentityRadius d rho j)) + 1

theorem columnIdentityRadius_pos (d : Nat) {rho : Real} (hrho : 0 < rho) (n : Nat) :
    0 < columnIdentityRadius d rho n := by
  induction n with
  | zero => exact hrho
  | succ n ih => exact lt_min ih (refinementKernelRadius_pos _ _ hrho ih)

theorem columnIdentityRadius_antitone (d : Nat) (rho : Real) : Antitone (columnIdentityRadius d rho) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

theorem columnIdentityRadius_le (d : Nat) (rho : Real) (n : Nat) :
    columnIdentityRadius d rho n ≤ rho := columnIdentityRadius_antitone d rho (Nat.zero_le n)

theorem columnIdentityModulusBound_spec (d : Nat) (rho : Real) {n j N : Nat}
    (hj : j < n) (hN : columnIdentityModulusBound d rho n ≤ N) :
    refinementKernelCap (4*d) (2*d) rho (columnIdentityRadius d rho j) < N := by
  have h := Finset.le_sup (f := fun j => refinementKernelCap (4*d) (2*d) rho (columnIdentityRadius d rho j))
    (Finset.mem_range.mpr hj)
  exact lt_of_le_of_lt h (Nat.lt_of_succ_le hN)

/-- Two identities at any earlier levels compose at the next level. -/
theorem ColumnPairIdentity.trans_levels {N d n i j m : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ X, L x 0 = 0)
    {p q z : ZMod N × ZMod N} (hp : p.1 ∈ X ∧ p.2 ∈ X)
    (hq : q.1 ∈ X ∧ q.2 ∈ X) (hz : z.1 ∈ X ∧ z.2 ∈ X)
    (hpq : ColumnPairIdentity T L (columnIdentityRadius d rho i) p q)
    (hqz : ColumnPairIdentity T L (columnIdentityRadius d rho j) q z)
    (hi : i ≤ m) (hj : j ≤ m) (hm : m < n) (hN : columnIdentityModulusBound d rho n ≤ N) :
    ColumnPairIdentity T L (columnIdentityRadius d rho (m+1)) p z := by
  have h1 := hpq.mono_radius (columnIdentityRadius_antitone d rho hi)
  have h2 := hqz.mono_radius (columnIdentityRadius_antitone d rho hj)
  have h := ColumnPairIdentity.trans_shrink X T L hrho (columnIdentityRadius_pos d hrho m)
    (columnIdentityRadius_le d rho m) hT hL hzero hp hq hz h1 h2
    (columnIdentityModulusBound_spec d rho hm hN)
  exact h.mono_radius (min_le_right _ _)

/-- Every bounded-length path of original identities gives an endpoint
identity on the uniformly controlled radius. -/
theorem column_identity_path {N d n : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ X, L x 0 = 0)
    (p : Nat → ZMod N × ZMod N) (hp : ∀ j ≤ n, (p j).1 ∈ X ∧ (p j).2 ∈ X)
    (hedge : ∀ j < n, ColumnPairIdentity T L rho (p j) (p (j+1)))
    (hN : columnIdentityModulusBound d rho n ≤ N) :
    ColumnPairIdentity T L (columnIdentityRadius d rho n) (p 0) (p n) := by
  have hpath : ∀ m ≤ n, ColumnPairIdentity T L (columnIdentityRadius d rho m) (p 0) (p m) := by
    intro m
    induction m with
    | zero => intro _; exact ColumnPairIdentity.refl T L rho (p 0)
    | succ m ih =>
      intro hm
      exact ColumnPairIdentity.trans_levels (i := m) (j := 0) (m := m) (n := n) (d := d) X T L hrho hT hL hzero (hp 0 (by omega))
        (hp m (by omega)) (hp (m+1) hm) (ih (by omega)) (hedge m (by omega))
        le_rfl (Nat.zero_le m) (by omega) hN
  exact hpath n le_rfl

end LeanProofs.GowersSzemeredi
