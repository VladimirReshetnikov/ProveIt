import FirstOrder.Fol

/-!
Profile equality for the equality-free closure kernels. This file uses the
repository's actual first-order syntax and Tarski semantics. It proves the
one-sided congruence simplification and invariance of equality-erased formulas.
It does not prove a theory interpretation or a machine consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.Profile

universe u
variable {V : Type u} (mem : V → V → Prop)

def Same (x y : V) : Prop := ∀ z, mem z x ↔ mem z y

def OneWay : Prop := ∀ x y, Same mem x y → ∀ z, mem x z → mem y z

def Full : Prop := ∀ x y, Same mem x y → ∀ z, mem x z ↔ mem y z

theorem same_refl (x : V) : Same mem x x := fun _ => Iff.rfl

theorem same_symm {x y : V} (h : Same mem x y) : Same mem y x :=
  fun z => (h z).symm

theorem same_trans {x y z : V} (hxy : Same mem x y) (hyz : Same mem y z) :
    Same mem x z := fun w => (hxy w).trans (hyz w)

theorem oneWay_iff_full : OneWay mem ↔ Full mem :=
  ⟨fun h x y hxy z => ⟨h x y hxy z, h y x (same_symm mem hxy) z⟩,
    fun h x y hxy z => (h x y hxy z).mp⟩

theorem mem_congr (h : OneWay mem) {x x' y y' : V}
    (hx : Same mem x x') (hy : Same mem y y') :
    mem x y ↔ mem x' y' :=
  ((oneWay_iff_full mem).mp h x x' hx y).trans (hy x')

/-- The equality-free formula saying that variables `i,j` have equal members. -/
def sameForm (i j : Nat) : Form :=
  .fAll (fIff (.fMem 0 (i + 1)) (.fMem 0 (j + 1)))

def eraseEquality : Form → Form
  | .fMem i j => .fMem i j
  | .fEq i j => sameForm i j
  | .fBot => .fBot
  | .fImp a b => .fImp (eraseEquality a) (eraseEquality b)
  | .fAnd a b => .fAnd (eraseEquality a) (eraseEquality b)
  | .fOr a b => .fOr (eraseEquality a) (eraseEquality b)
  | .fAll a => .fAll (eraseEquality a)
  | .fEx a => .fEx (eraseEquality a)

/-- Tarski semantics with equality interpreted as predecessor-profile equality. -/
def ProfileSat (env : Nat → V) : Form → Prop
  | .fMem i j => mem (env i) (env j)
  | .fEq i j => Same mem (env i) (env j)
  | .fBot => False
  | .fImp a b => ProfileSat env a → ProfileSat env b
  | .fAnd a b => ProfileSat env a ∧ ProfileSat env b
  | .fOr a b => ProfileSat env a ∨ ProfileSat env b
  | .fAll a => ∀ x, ProfileSat (scons x env) a
  | .fEx a => ∃ x, ProfileSat (scons x env) a

theorem sat_sameForm (env : Nat → V) (i j : Nat) :
    Sat mem env (sameForm i j) ↔ Same mem (env i) (env j) := by
  simp only [sameForm, Sat, fIff, scons, Same]
  exact ⟨fun h z => ⟨(h z).1, (h z).2⟩, fun h z => ⟨(h z).mp, (h z).mpr⟩⟩

theorem sat_eraseEquality (f : Form) (env : Nat → V) :
    Sat mem env (eraseEquality f) ↔ ProfileSat mem env f := by
  induction f generalizing env with
  | fMem i j | fBot => rfl
  | fEq i j => exact sat_sameForm mem env i j
  | fImp a b iha ihb | fAnd a b iha ihb | fOr a b iha ihb =>
      simp only [eraseEquality, Sat, ProfileSat, iha, ihb]
  | fAll a ih | fEx a ih => simp only [eraseEquality, Sat, ProfileSat, ih]

/-- Profile-congruent assignments give the same truth value after equality erasure. -/
theorem profileSat_congr (h : OneWay mem) (f : Form) (e e' : Nat → V)
    (he : ∀ i, Same mem (e i) (e' i)) :
    ProfileSat mem e f ↔ ProfileSat mem e' f := by
  induction f generalizing e e' with
  | fMem i j => exact mem_congr mem h (he i) (he j)
  | fEq i j =>
      exact ⟨fun hij => same_trans mem (same_symm mem (he i)) (same_trans mem hij (he j)),
        fun hij => same_trans mem (he i) (same_trans mem hij (same_symm mem (he j)))⟩
  | fBot => rfl
  | fImp a b iha ihb | fAnd a b iha ihb | fOr a b iha ihb =>
      simp only [ProfileSat, iha e e' he, ihb e e' he]
  | fAll a ih =>
      have hc : ∀ x i, Same mem (scons x e i) (scons x e' i) := by
        intro x i
        cases i with
        | zero => exact same_refl mem x
        | succ i => exact he i
      simp only [ProfileSat]
      exact forall_congr' fun x => ih _ _ (hc x)
  | fEx a ih =>
      have hc : ∀ x i, Same mem (scons x e i) (scons x e' i) := by
        intro x i
        cases i with
        | zero => exact same_refl mem x
        | succ i => exact he i
      simp only [ProfileSat]
      exact exists_congr fun x => ih _ _ (hc x)

theorem sat_eraseEquality_congr (h : OneWay mem) (f : Form) (e e' : Nat → V)
    (he : ∀ i, Same mem (e i) (e' i)) :
    Sat mem e (eraseEquality f) ↔ Sat mem e' (eraseEquality f) :=
  (sat_eraseEquality mem f e).trans
    ((profileSat_congr mem h f e e' he).trans (sat_eraseEquality mem f e').symm)

#print axioms oneWay_iff_full
#print axioms sat_eraseEquality_congr

end SetTheory.BusyBeaver.ZFC.Profile
