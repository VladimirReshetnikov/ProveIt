module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCore
@[expose] public section
open M6.Arithmetic.PA

/-! Finite dominated-rho8 replacement, ported term-for-term from DominatedCore.v
at VladimirReshetnikov/ProveIt@6809609c61b9f2dd11c66374952cc5eb3defbd9f.
Only its generic propositional proof is reused, not a ZFC machine or endpoint.
Every row has an actual Nat inequality proof; every MP constructs the real
finite actual-fragment proof. No unrestricted row is assumed. -/
namespace M6.PA.NativeCalculus.ActualCore.Dominated
set_option autoImplicit false

abbrev below := Nat.le

def mp (a b : Nat) (major : Proof (wim a b)) (minor : Proof a) :
    Proof b := .mp minor major
def row (a b c u : Nat) (h : u ≤ a) : Proof (rho8 a b c u) :=
  .r8 a b c u h
theorem refl (a : Nat) : a ≤ a := Nat.le_refl a
theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y := by
  have hp := M6.Source.Enumeration.pair_bounds x y
  simp only [wim,M6.Source.Cantor.implication]
  omega
theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y := by
  have hp := M6.Source.Enumeration.pair_bounds x y
  simp only [wim,M6.Source.Cantor.implication]
  omega

def d1 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (hb0 : v3 ≤ v0) :
  Proof (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))) :=
  (mp _ _ (row (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0 (le_l (wim v2 v1) (le_l v1 (refl _)))) (row v0 v2 v1 v3 hb0))

def d2 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (hb0 : v2 ≤ v3) :
  Proof (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2) (le_r v0 (refl _))) (d1 v3 v1 v4 v2 v0 hb0))

def d3 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))) :=
  (mp _ _ (d2 (wim v1 (wim v1 v2)) v1 v2 (wim v1 v2) v3 v0 (le_r v1 (refl _))) (row (wim v1 v2) v3 v1 (wim v1 v2) (refl _)))

def d4 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim v0 v1) v0) (wim v2 v0)) :=
  (mp _ _ (d3 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

def d5 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))) :=
  (mp _ _ (row (wim v0 v1) v3 (wim v1 v2) v1 (le_r v0 (refl _))) (d4 v1 v2 v0))

def d6 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) :
  Proof (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2) (le_r v0 (refl _))) (d5 v3 v1 v2 v0))

def d7 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))) :=
  (mp _ _ (d6 (wim v2 (wim (wim v1 v2) v3)) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (row (wim (wim v1 v2) v3) v1 v2 (wim (wim v1 v2) v3) (refl _)))

def d8 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) :
  Proof (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2) (le_r v0 (refl _))) (d6 v3 v2 v4 v1 v0))

def d9 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)) :=
  (mp _ _ (d7 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

def d10 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))) :=
  (mp _ _ (d8 (wim v3 (wim v1 v2)) v1 v2 (wim (wim v1 v2) v3) v3 v0) (row (wim v1 v2) v2 v3 (wim v1 v2) (refl _)))

def d11 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))) :=
  (mp _ _ (row (wim v0 v1) v3 (wim (wim v0 v1) v2) v1 (le_r v0 (refl _))) (d9 v0 v1 v2))

def d12 (v0 : Nat) (v1 : Nat) :
  Proof (wim v0 (wim v1 v0)) :=
  (mp _ _ (d9 v0 (wim v1 v0) v0) (d4 v0 (wim v1 v0) v1))

def d13 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim v0 v1) v2) (wim v1 v2)) :=
  (mp _ _ (d10 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _)))

def d14 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim v0 (wim (wim (wim v1 v2) v1) v1)) :=
  (mp _ _ (d11 (wim v1 v2) v1 v1 v0) (d4 v1 v2 (wim (wim v1 v2) v1)))

def d15 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)) :=
  (mp _ _ (row (wim v0 (wim v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (refl _)))) (d12 (wim v1 v2) v0))

def d16 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim v0 (wim (wim v0 v1) (wim v2 v1))) :=
  (mp _ _ (d13 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (row v0 v2 v1 v0 (refl _)))

def d17 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim v0 (wim v1 (wim v2 v0))) :=
  (mp _ _ (d13 v2 v0 (wim v1 (wim v2 v0))) (d12 (wim v2 v0) v1))

def d18 (v0 : Nat) (v1 : Nat) :
  Proof (wim (wim (wim v0 v1) v0) v0) :=
  (mp _ _ (d14 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _)))

def d19 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) :
  Proof (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)) :=
  (mp _ _ (row (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1 (le_l (wim v3 v2) (le_l v2 (le_r v0 (refl _))))) (d16 (wim v0 v1) v2 v3))

def d20 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))) :=
  (mp _ _ (row v0 v2 (wim v0 v1) v0 (refl _)) (d18 v0 v1))

def d21 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))) :=
  (mp _ _ (d11 v1 (wim v1 v2) (wim v1 v2) v0) (d20 v1 v2 (wim v1 (wim v1 v2))))

def d22 (v0 : Nat) (v1 : Nat) :
  Proof (wim (wim v0 (wim v0 v1)) (wim v0 v1)) :=
  (mp _ _ (d21 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _)))

def d23 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim v0 (wim v1 v2)) v1) v1) :=
  (mp _ _ (d22 (wim (wim v0 (wim v1 v2)) v1) v1) (d15 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))

def d24 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) :=
  (mp _ _ (d22 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (d19 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))

def d25 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))) :=
  (mp _ _ (row v0 v3 (wim v1 (wim v0 v2)) v0 (refl _)) (d23 v1 v0 v2))

def d26 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) :
  Proof (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))) :=
  (mp _ _ (row v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 (refl _)) (d24 v0 v1 v2 v3))

def d27 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) :=
  (mp _ _ (d22 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (d25 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))

def d28 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) :
  Proof (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)) :=
  (mp _ _ (row (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) (le_r v0 (refl _))) (d26 v1 v2 v3 v4 v0))

def d29 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) :
  Proof (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) :=
  (mp _ _ (d22 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (d28 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))

def d30 (v0 : Nat) (v1 : Nat) (v2 : Nat) (hb0 : v2 ≤ v0) :
  Proof (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)) :=
  (mp _ _ (d27 (wim (wim v1 v2) v0) (wim v0 v1) v1) (row v0 (wim (wim v1 v2) v0) v1 v2 hb0))

def d31 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (hb0 : v3 ≤ v0) :
  Proof (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))) :=
  (mp _ _ (d30 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (d16 v0 v1 v2))

def d32 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))) :=
  (mp _ _ (d31 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (refl _)) (d29 (wim v0 (wim v1 v2)) v0 v3 v2 v1))

def d33 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))) :=
  (mp _ _ (d32 v0 (wim v0 v3) (wim v2 v3) v1) (d16 v0 v3 v2))

def d34 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (hb0 : v3 ≤ v2) :
  Proof (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))) :=
  (mp _ _ (d30 v2 (wim v0 (wim v1 v2)) v3 hb0) (d17 v2 v0 v1))

def d35 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))) :=
  (mp _ _ (d34 v0 v1 (wim (wim v0 v2) (wim v3 v2)) (wim v3 v2) (le_r (wim v0 v2) (refl _))) (d33 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v3 v2))

def d36 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (hb0 : below v3 (wim v1 (wim v1 v2))) :
  Proof (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))) :=
  (mp _ _ (d30 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (d20 v1 v2 v0))

def d37 (v0 : Nat) (v1 : Nat) :
  Proof (wim v0 (wim (wim v0 v1) v1)) :=
  (mp _ _ (d36 v0 (wim v0 v1) v1 (wim (wim v0 v1) v1) (le_r (wim v0 v1) (refl _))) (d33 v0 (wim (wim v0 v1) v1) (wim v0 v1) v1))

def d38 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim v0 (wim (wim (wim v1 v0) v2) v2)) :=
  (mp _ _ (d13 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (d37 (wim v1 v0) v2))

def d39 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)) :=
  (mp _ _ (d32 v0 (wim v0 v2) v2 v1) (d37 v0 v2))

def d40 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)) :=
  (mp _ _ (d32 v0 (wim (wim v3 v0) v2) v2 v1) (d38 v0 v3 v2))

def d41 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)) :=
  (mp _ _ (d33 v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1) (d38 (wim v0 v3) v2 v1))

def d42 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) :=
  (mp _ _ (d39 v0 v3 (wim v1 (wim v2 (wim v0 v3)))) (d17 (wim v0 v3) v1 v2))

def d43 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)) :=
  (mp _ _ (d39 v0 v1 (wim (wim (wim v0 v1) v2) v2)) (d37 (wim v0 v1) v2))

def d44 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1) :=
  (mp _ _ (d43 (wim v0 v1) (wim v0 v2) v1) (d41 v0 v1 (wim v0 v1) v2))

def d45 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2) :=
  (mp _ _ (d40 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (d44 v1 v2 v3))

def d46 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))) :=
  (mp _ _ (d31 v0 (wim v1 v2) (wim v1 v0) v0 (refl _)) (d45 (wim v0 (wim v1 v2)) v1 v0 v2))

def d47 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))) :=
  (mp _ _ (d46 v1 v0 (wim (wim v1 v2) (wim v3 v2))) (d35 v1 v0 v2 v3))

def d48 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) :=
  (mp _ _ (d47 v0 (wim (wim v0 v1) v1) v2 v3) (d37 v0 v1))

def d49 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)) :=
  (mp _ _ (d27 v0 (wim (wim (wim v0 v1) v1) v2) v2) (d48 v0 v1 v2 v0))

def d50 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) :=
  (mp _ _ (d49 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (d47 (wim v0 v1) v1 v2 v3))

def d51 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))) :=
  (mp _ _ (d42 v0 (wim v0 v1) (wim v1 v2) v2) (d50 v0 v1 v2 v0))

def d52 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)) :=
  (mp _ _ (d51 (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (d51 v2 v0 v1))

def d53 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))) :=
  (mp _ _ (d52 v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (d46 (wim v1 v2) v0 v2))

def d54 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))) :=
  (mp _ _ (d52 (wim v1 v2) v2 v0 (wim v1 (wim v0 v2))) (d49 v1 v2 (wim v0 v2)))

def d55 (v0 : Nat) (v1 : Nat) (v2 : Nat) :
  Proof (wim (wim v0 v1) (wim (wim v2 v0) (wim v2 v1))) :=
  (mp _ _ (d49 (wim v0 v1) (wim v2 v1) (wim (wim v2 v0) (wim v2 v1))) (d52 v0 v1 v2 (wim v2 v1)))

def d57 (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) :
  Proof (wim (wim v0 (wim (wim v1 v2) v1)) (wim v0 (wim v3 v1))) :=
  (mp _ _ (d55 (wim (wim v1 v2) v1) (wim v3 v1) v0) (d4 v1 v2 v3))

def rho8_all (a : Nat) (b : Nat) (c : Nat) (u : Nat) :
  Proof (rho8 a b c u) :=
  (mp _ _ (d52 a c (wim c u) (wim (wim a c) (wim b c))) (d57 (wim a c) c u b))

def composition (a : Nat) (b : Nat) (c : Nat) :
  Proof (wim (wim a b) (wim (wim b c) (wim a c))) :=
  (d51 a b c)

def lift_right (a : Nat) (b : Nat) (hab : Proof (wim a b)) (x : Nat) :
  Proof (wim (wim x a) (wim x b)) :=
  (mp _ _ (d55 a b x) hab)

def k (a : Nat) (b : Nat) :
  Proof (wim a (wim b a)) :=
  (d12 a b)

def peirce (a : Nat) (b : Nat) :
  Proof (wim (wim (wim a b) a) a) :=
  (d18 a b)

def s (a : Nat) (b : Nat) (c : Nat) :
  Proof (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  (mp _ _ (d54 (wim a b) (wim a (wim b c)) (wim a c)) (d53 a b c))

#print axioms rho8_all
#print axioms composition
#print axioms k
#print axioms peirce
#print axioms s
end M6.PA.NativeCalculus.ActualCore.Dominated

