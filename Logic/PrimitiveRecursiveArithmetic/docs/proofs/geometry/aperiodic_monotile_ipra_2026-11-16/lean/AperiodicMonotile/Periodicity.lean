import AperiodicMonotile.Substitution

namespace AperiodicMonotile

/-- Natural-valued triangular norm, after sign coding has been eliminated. -/
def Q (m n : Nat) : Nat := m*m + m*n + n*n

/-- The complete mod-2 table. -/
theorem even_Q_forces_even (m n : Nat) (h : Q m n % 2 = 0) :
    m % 2 = 0 ∧ n % 2 = 0 := by
  omega

/-- A 2-adic infinite-descent core, stated without valuations. -/
theorem no_Q_eq_twoQ_nonzero
    (a b c d : Nat)
    (h : Q c d = 2 * Q a b)
    (hnz : Q a b ≠ 0) : False := by
  -- From h, Q(a,b) is even; hence a=2a', b=2b'.  Substitute and cancel 2
  -- to obtain a strictly smaller solution.  Instantiate `Core/DescentEx` with
  -- the indicator of `Q(c,d)=2*Q(a,b) ∧ Q(a,b)≠0` and bound a+b.
  sorry

/-- Exact contraction of a hat placement to a chevron placement. -/
opaque toChevron : TileInstance → TileInstance
/-- Exact contraction of a hat placement to a comet placement. -/
opaque toComet : TileInstance → TileInstance

/-- All tiles in a periodic quotient can be aligned to one triangular lattice. -/
opaque alignPeriodic : TorusCode → TorusCode

/-- A single period can be completed to a finite torus by repetition of a
    bounded transverse state. -/
theorem weak_to_strong_periodic
    (window : Nat → PatchCode) (u : Axial)
    (hu : u ≠ axialOfIntPair (0,0))
    (hperiod : ∀ r, periodOnWindowB hatPolygon (window r) u r = true) :
    ∃ torus, periodicTorusB hatPolygon torus = true := by
  -- Encode the finite set of cross-sections of a strip of width O(|u|).
  -- Apply `IPRADerivations.Core.Pigeonhole` to two equal states.
  sorry

/-- Finite-torus form of the chevron/comet coupling theorem. -/
theorem coupling_forces_similarity
    (torus : TorusCode)
    (hvalid : periodicTorusB hatPolygon torus = true) :
    ∃ a b c d : Nat,
      Q a b ≠ 0 ∧ Q c d = 2 * Q a b := by
  /-
  1. Contract each representative to a chevron and a comet.
  2. Count areas in the same finite fundamental domain: det(g)=2/3.
  3. Split chevrons into rhombi; on the torus the three worm families are
     finite unions of directed cycles.
  4. Synchronize cycles by bounded lcm.  Orientation balance gives
       g(A v_i) = (A/2) v_i + b_i v_i'.
     Summing over i and using v₁+v₂+v₃=v₁'+v₂'+v₃'=0 gives b₁=b₂=b₃.
  5. Thus g is a similarity.  Express one nonzero period in triangular
     coordinates in both lattices; squared scale 2/3, together with the edge-length ratio sqrt(3):1, gives Q(c,d)=2Q(a,b).
  -/
  sorry

/-- No strongly periodic hat tiling exists. -/
theorem no_periodic_torus (torus : TorusCode) :
    periodicTorusB hatPolygon torus = false := by
  by_contra h
  have hv : periodicTorusB hatPolygon torus = true := by simpa using h
  obtain ⟨a,b,c,d,hnz,heq⟩ := coupling_forces_similarity torus hv
  exact no_Q_eq_twoQ_nonzero a b c d heq hnz

end AperiodicMonotile
