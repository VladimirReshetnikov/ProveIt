import GowersSzemeredi.Proofs16ColumnIdentityLevels

/-! Symmetric additive column relations with quantitative weak transitivity.
In a sufficiently large prime target, one intermediate pair suffices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ColumnPairRelated {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p q : ZMod N × ZMod N) : Prop :=
  (p.1 ∈ X ∧ p.2 ∈ X) ∧ (q.1 ∈ X ∧ q.2 ∈ X) ∧
    p.1 - p.2 = q.1 - q.2 ∧ ColumnPairIdentity T L r p q

/-- Interchange the two pairs. -/
theorem ColumnPairRelated.symm {N : Nat} [NeZero N]
    {X : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {r : Real} {p q : ZMod N × ZMod N}
    (h : ColumnPairRelated X T L r p q) : ColumnPairRelated X T L r q p :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

/-- Reverse both pairs. -/
theorem ColumnPairRelated.swap {N : Nat} [NeZero N]
    {X : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {r : Real} {p q : ZMod N × ZMod N}
    (h : ColumnPairRelated X T L r p q) : ColumnPairRelated X T L r p.swap q.swap := by
  refine ⟨⟨h.1.2, h.1.1⟩, ⟨h.2.1.2, h.2.1.1⟩, ?_, ?_⟩
  · change p.2 - p.1 = q.2 - q.1
    linear_combination -h.2.2.1
  · intro y hp2 hp1 hq2 hq1
    have heq := h.2.2.2 y hp1 hp2 hq1 hq2
    change L p.2 y - L p.1 y = L q.2 y - L q.1 y
    linear_combination -heq

/-- Exchange the middle entries in the signed additive quadruple. -/
theorem ColumnPairRelated.cross {N : Nat} [NeZero N]
    {X : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {r : Real} {p q : ZMod N × ZMod N}
    (h : ColumnPairRelated X T L r p q) :
    ColumnPairRelated X T L r (p.1, q.1) (p.2, q.2) := by
  refine ⟨⟨h.1.1, h.2.1.1⟩, ⟨h.1.2, h.2.1.2⟩, ?_, ?_⟩
  · change p.1 - q.1 = p.2 - q.2
    linear_combination h.2.2.1
  · intro y hp1 hq1 hp2 hq2
    have heq := h.2.2.2 y hp1 hp2 hq1 hq2
    change L p.1 y - L q.1 y = L p.2 y - L q.2 y
    linear_combination heq

/-- The first level is the original radius. Later levels successively
remove intermediate constraints. -/
def ColumnRelationLevel {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (d : Nat) (rho : Real) (i : Nat) (p q : ZMod N × ZMod N) : Prop :=
  ColumnPairRelated X T L (columnIdentityRadius d rho (i-1)) p q

/-- Positive relation levels satisfy additive transitivity. This is
stronger than the many-bridge weak transitivity condition. -/
theorem columnRelationLevel_trans {N d n i j : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ X, L x 0 = 0)
    {p q z : ZMod N × ZMod N}
    (hpq : ColumnRelationLevel X T L d rho i p q) (hqz : ColumnRelationLevel X T L d rho j q z)
    (hi : 0 < i) (hj : 0 < j) (hij : i+j ≤ n) (hN : columnIdentityModulusBound d rho n ≤ N) :
    ColumnRelationLevel X T L d rho (i+j) p z := by
  refine ⟨hpq.1, hqz.2.1, hpq.2.2.1.trans hqz.2.2.1, ?_⟩
  let m := max (i-1) (j-1)
  have hcomp := ColumnPairIdentity.trans_levels (i := i-1) (j := j-1) (m := m) (n := n)
    X T L hrho hT hL hzero hpq.1 hpq.2.1 hqz.2.1 hpq.2.2.2 hqz.2.2.2
    (le_max_left _ _) (le_max_right _ _) (by dsimp [m]; omega) hN
  exact hcomp.mono_radius (columnIdentityRadius_antitone d rho (by dsimp [m]; omega))

/-- Any nonempty set of intermediate pairs gives the endpoint relation;
there is no additional bridge-density loss. -/
theorem columnRelationLevel_of_bridge {N d n i j : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ X, L x 0 = 0)
    {p z : ZMod N × ZMod N}
    (hbridge : ∃ q, ColumnRelationLevel X T L d rho i p q ∧ ColumnRelationLevel X T L d rho j q z)
    (hi : 0 < i) (hj : 0 < j) (hij : i+j ≤ n) (hN : columnIdentityModulusBound d rho n ≤ N) :
    ColumnRelationLevel X T L d rho (i+j) p z := by
  obtain ⟨q, hpq, hqz⟩ := hbridge
  exact columnRelationLevel_trans X T L hrho hT hL hzero hpq hqz hi hj hij hN

end LeanProofs.GowersSzemeredi
