import IPRADerivations.Core.Tactic

/-! Closed object-iPRA certificates. Each integer input is a difference of two
natural variables. The open lemmas also allow arbitrary integer terms. -/

namespace LeanProofs.IPRA.PlaneMetric

open LeanProofs.ConciseIPRA
open scoped Fm

def normSq {n} (x y : ZT n) := x.sq + y.sq
def dot {n} (x y u v : ZT n) := x * u + y * v
def wedge {n} (x y u v : ZT n) := x * v - y * u

def gram {n} (x y u v : ZT n) :=
  (normSq x y * normSq u v).eq ((dot x y u v).sq + (wedge x y u v).sq)

def midpointIdentity {n} (x y u v : ZT n) :=
  (normSq (x + u) (y + v) + normSq (x - u) (y - v)).eq
    ((normSq x y + normSq u v) + (normSq x y + normSq u v))

theorem gramOpen {n} {Γ : List (Fm PTm n)} (x y u v : ZT n) :
    Γ ⊢[PRAAx] gram x y u v := by
  unfold gram normSq dot wedge
  ipra_ring

theorem midpointOpen {n} {Γ : List (Fm PTm n)} (x y u v : ZT n) :
    Γ ⊢[PRAAx] midpointIdentity x y u v := by
  unfold midpointIdentity normSq
  ipra_ring

def closeFour (φ : ZT 8 → ZT 8 → ZT 8 → ZT 8 → Fm PTm 8) : Fm PTm 0 :=
  univ 8 (φ (.var2 0 1) (.var2 2 3) (.var2 4 5) (.var2 6 7))

theorem gramClosed : ([] : List (Fm PTm 0)) ⊢[PRAAx] closeFour gram :=
  closeUniv 8 (gramOpen _ _ _ _)

theorem midpointClosed : ([] : List (Fm PTm 0)) ⊢[PRAAx] closeFour midpointIdentity :=
  closeUniv 8 (midpointOpen _ _ _ _)

#print axioms gramClosed
#print axioms midpointClosed
end LeanProofs.IPRA.PlaneMetric
