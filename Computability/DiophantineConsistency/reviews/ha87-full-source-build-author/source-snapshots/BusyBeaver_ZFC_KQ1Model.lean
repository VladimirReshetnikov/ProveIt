import BusyBeaver.ZFC.KQHyp

/-!
The actual quotient structure of a `KQHyp.QHyp` structure, for instance an
equality-free CP/GIC model (`QuotientModel.ofCPGIC`).

Bisimilarity is an equivalence and interpreted membership respects it in
both arguments. The quotient has actual equality and satisfies Extensionality.
A computable formula translation replaces membership/equality atoms by their
fixed equality-free definitions, with checked satisfaction in the quotient.
The remaining ZF axioms and all compiler/consistency endpoints are separate.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Model

open KQHyp

open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileSyntax
open ProfileModel CompositionModel DeepPositiveClosure

universe u
variable {V : Type u}

theorem member_left_congr (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    {x x' y : V} (hxx' : Eqv mem x x') : Member mem x y ↔ Member mem x' y := by
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, hz, h.trans (h.symm hxx') hxz⟩
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, hz, h.trans hxx' hxz⟩

theorem member_right_congr (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    {x y y' : V} (hyy' : Eqv mem y y') : Member mem x y ↔ Member mem x y' := by
  obtain ⟨r, hr, hEdge⟩ := hyy'
  obtain ⟨hForth, hBack⟩ := hr y y' hEdge
  constructor
  · rintro ⟨z, hz, hxz⟩
    obtain ⟨z', hz', hzz'⟩ := hForth z hz
    exact ⟨z', hz', h.trans hxz ⟨r, hr, hzz'⟩⟩
  · rintro ⟨z', hz', hxz'⟩
    obtain ⟨z, hz, hzz'⟩ := hBack z' hz'
    exact ⟨z, hz, h.trans hxz' (h.symm ⟨r, hr, hzz'⟩)⟩

theorem member_congr (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    {x x' y y' : V} (hxx' : Eqv mem x x') (hyy' : Eqv mem y y') :
    Member mem x y ↔ Member mem x' y' :=
  (member_left_congr mem witness h hxx').trans (member_right_congr mem witness h hyy')

def memberForm (i j : Nat) : Form :=
  fEx (fAnd (fMem 0 (j + 1)) (eqvForm (i + 1) 0))

theorem sat_memberForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (memberForm i j) ↔ Member mem (env i) (env j) := by
  constructor
  · rintro ⟨z, hz, hE⟩
    exact ⟨z, hz, (sat_eqvForm mem _ (i + 1) 0).mp hE⟩
  · rintro ⟨z, hz, hE⟩
    exact ⟨z, hz, (sat_eqvForm mem _ (i + 1) 0).mpr hE⟩

def translate : Form → Form
  | fMem i j => memberForm i j
  | fEq i j => eqvForm i j
  | fBot => fBot
  | fImp a b => fImp (translate a) (translate b)
  | fAnd a b => fAnd (translate a) (translate b)
  | fOr a b => fOr (translate a) (translate b)
  | fAll a => fAll (translate a)
  | fEx a => fEx (translate a)

def RelSat (mem : V → V → Prop) (env : Nat → V) : Form → Prop
  | fMem i j => Member mem (env i) (env j)
  | fEq i j => Eqv mem (env i) (env j)
  | fBot => False
  | fImp a b => RelSat mem env a → RelSat mem env b
  | fAnd a b => RelSat mem env a ∧ RelSat mem env b
  | fOr a b => RelSat mem env a ∨ RelSat mem env b
  | fAll a => ∀ x, RelSat mem (scons x env) a
  | fEx a => ∃ x, RelSat mem (scons x env) a

theorem sat_translate (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (translate phi) ↔ RelSat mem env phi := by
  induction phi generalizing env with
  | fMem i j => exact sat_memberForm mem env i j
  | fEq i j => exact sat_eqvForm mem env i j
  | fBot => exact Iff.rfl
  | fImp a b iha ihb => exact imp_congr (iha env) (ihb env)
  | fAnd a b iha ihb => exact and_congr (iha env) (ihb env)
  | fOr a b iha ihb => exact or_congr (iha env) (ihb env)
  | fAll a ih => exact forall_congr' (fun x => ih (scons x env))
  | fEx a ih => exact exists_congr (fun x => ih (scons x env))

theorem equalityFree_translate (phi : Form) : EqualityFree (translate phi) := by
  induction phi with
  | fMem i j => exact ⟨True.intro, equalityFree_eqvForm (i + 1) 0⟩
  | fEq i j => exact equalityFree_eqvForm i j
  | fBot => trivial
  | fImp _ _ iha ihb => exact ⟨iha, ihb⟩
  | fAnd _ _ iha ihb => exact ⟨iha, ihb⟩
  | fOr _ _ iha ihb => exact ⟨iha, ihb⟩
  | fAll _ ih => exact ih
  | fEx _ ih => exact ih

def modelSetoid (mem : V → V → Prop) (witness : V) (h : QHyp mem) : Setoid V where
  r := Eqv mem
  iseqv := ⟨h.refl, h.symm, h.trans⟩

abbrev Domain (mem : V → V → Prop) (witness : V) (h : QHyp mem) :=
  Quotient (modelSetoid mem witness h)

def mk (mem : V → V → Prop) (witness : V) (h : QHyp mem) (x : V) : Domain mem witness h :=
  Quotient.mk (modelSetoid mem witness h) x

def quotientMember (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (x y : Domain mem witness h) : Prop :=
  Quotient.liftOn₂ x y (Member mem) (fun _ _ _ _ hx hy =>
    propext (member_congr mem witness h hx hy))

theorem mk_eq_iff (mem : V → V → Prop) (witness : V) (h : QHyp mem) (x y : V) :
    mk mem witness h x = mk mem witness h y ↔ Eqv mem x y := by
  exact ⟨fun he => Quotient.exact he,
    fun he => Quotient.sound (s := modelSetoid mem witness h) he⟩

theorem mk_scons (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (x : V) (env : Nat → V) :
    (fun i => mk mem witness h (scons x env i)) =
      scons (mk mem witness h x) (fun i => mk mem witness h (env i)) := by
  funext i
  cases i <;> rfl

theorem sat_quotient (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → V) :
    Sat (quotientMember mem witness h) (fun i => mk mem witness h (env i)) phi ↔
      RelSat mem env phi := by
  induction phi generalizing env with
  | fMem i j => exact Iff.rfl
  | fEq i j => exact mk_eq_iff mem witness h (env i) (env j)
  | fBot => exact Iff.rfl
  | fImp a b iha ihb => exact imp_congr (iha env) (ihb env)
  | fAnd a b iha ihb => exact and_congr (iha env) (ihb env)
  | fOr a b iha ihb => exact or_congr (iha env) (ihb env)
  | fAll a ih =>
    constructor
    · intro hall x
      apply (ih (scons x env)).mp
      rw [mk_scons]
      exact hall (mk mem witness h x)
    · intro hall q
      induction q using Quotient.ind with
      | _ x =>
        have hx := (ih (scons x env)).mpr (hall x)
        rwa [mk_scons] at hx
  | fEx a ih =>
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      refine ⟨x, (ih (scons x env)).mp ?_⟩
      rw [mk_scons]
      exact hq
    · rintro ⟨x, hx⟩
      refine ⟨mk mem witness h x, ?_⟩
      have hqx := (ih (scons x env)).mpr hx
      rwa [mk_scons] at hqx

/-- Satisfaction respects bisimilar environments, via their equal quotient images. -/
theorem relSat_congr (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env env' : Nat → V) (he : ∀ i, Eqv mem (env i) (env' i)) :
    RelSat mem env phi ↔ RelSat mem env' phi := by
  have henv : (fun i => mk mem witness h (env i)) =
      (fun i => mk mem witness h (env' i)) :=
    funext fun i => (mk_eq_iff mem witness h (env i) (env' i)).mpr (he i)
  rw [← sat_quotient mem witness h phi env,
    ← sat_quotient mem witness h phi env', henv]

theorem quotient_extensional (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (x y : Domain mem witness h)
    (hMembers : ∀ z, quotientMember mem witness h z x ↔ quotientMember mem witness h z y) :
    x = y := by
  induction x, y using Quotient.ind₂ with
  | _ a b =>
    apply Quotient.sound
    apply h.ext a b
    intro z
    exact hMembers (mk mem witness h z)

#print axioms sat_quotient
#print axioms quotient_extensional
#print axioms equalityFree_translate

end SetTheory.BusyBeaver.ZFC.KQ1Model

