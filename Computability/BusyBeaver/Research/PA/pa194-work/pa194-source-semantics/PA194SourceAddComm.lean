import PA194SourceAddCoherence
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Commutativity of addition in the source theory

`sAC`: a sum of `a, b` and a sum of `b, a` are isomorphic.

The traces recurse in the first summand, so two laws for the second summand come first, each
by `letter_induction` on the first summand, and each stated up to isomorphism:

* `sem_r0` (`psiR0`): a sum of `b` and an empty `z` is isomorphic to `b`;
* `sem_rs` (`psiRS`): if `a` is a successor of `x`, `c'` a sum of `b, a`, `d'` a sum of
  `b, x` and `c''` a successor of `d'`, then `c' ≅ c''`;
* `sem_ac` (`psiAC`): commutativity, by induction on `a`.

They use the predecessor law and, of the ten known facts, symmetry and transitivity of
isomorphism, isomorphism of empty representatives, existence and compatibility of
successors, and existence of sums. Coherence of addition is not used.

`ac_supply`: `T ⊢ tHyp sAC` for the adjunctive source theory with full separation, from
`TenFacts`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

/-- Right zero: variables `b, z, c' = #2, #1, #0`. -/
def psiR0 : SF 1 :=
  ∀⁰ ∀⁰ (sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sZero #1 🡒 sAdd #2 #1 #0 🡒 sIso #0 #2)
/-- Right successor: variables `b, x, a, c', d', c'' = #5, …, #0`. -/
def psiRS : SF 1 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sSucc #4 #3 🡒 sAdd #5 #3 #2 🡒 sAdd #5 #4 #1 🡒 sSucc #1 #0 🡒 sIso #2 #0)
/-- The body of `sAC` with its first variable free. -/
def psiAC : SF 1 :=
  ∀⁰ ∀⁰ ∀⁰ (sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sAdd #3 #2 #1 🡒 sAdd #2 #3 #0 🡒
    sIso #1 #0)

section semantics
variable {M : Type} [s : Structure NL M]

theorem ev_psiR0 (x : M) : ev ![x] psiR0 ↔
    ∀ z c' : M, mD x → mD z → mD c' → mZ z → mA x z c' → mI c' x := by
  simp [psiR0]
theorem ev_psiRS (y : M) : ev ![y] psiRS ↔
    ∀ x a c' d' c'' : M, mD y → mD x → mD a → mD c' → mD d' → mD c'' →
      mS x a → mA y a c' → mA y x d' → mS d' c'' → mI c' c'' := by
  simp [psiRS]
theorem ev_psiAC (a : M) : ev ![a] psiAC ↔
    ∀ c d d' : M, mD a → mD c → mD d → mD d' → mA a c d → mA c a d' → mI d d' := by
  simp [psiAC]

end semantics
end PA194GuardedCompiler

namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

def PR0 (x : N) : Prop :=
  ∀ z c' : N, SDom x → SDom z → SDom c' → SZero z → SAdd x z c' → SIso c' x
def PRS (y : N) : Prop :=
  ∀ x a c' d' c'' : N, SDom y → SDom x → SDom a → SDom c' → SDom d' → SDom c'' →
    SSucc x a → SAdd y a c' → SAdd y x d' → SSucc d' c'' → SIso c' c''
def PAC (a : N) : Prop :=
  ∀ c d d' : N, SDom a → SDom c → SDom d → SDom d' → SAdd a c d → SAdd c a d' → SIso d d'

theorem ev_psiR0_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiR0 ↔ PR0 x := by
  rw [@ev_psiR0 N (sourceLetters s f) x]
  simp only [mD_iff, mZ_iff, mA_iff, mI_iff, PR0]
theorem ev_psiRS_iff (f : ℕ → N) (y : N) :
    @ev N (sourceLetters s f) 1 ![y] psiRS ↔ PRS y := by
  rw [@ev_psiRS N (sourceLetters s f) y]
  simp only [mD_iff, mS_iff, mA_iff, mI_iff, PRS]
theorem ev_psiAC_iff (f : ℕ → N) (a : N) :
    @ev N (sourceLetters s f) 1 ![a] psiAC ↔ PAC a := by
  rw [@ev_psiAC N (sourceLetters s f) a]
  simp only [mD_iff, mA_iff, mI_iff, PAC]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem sem_r0 (f : ℕ → N) (K : Known N) : ∀ x : N, SDom x → PR0 x := by
  have key := letter_induction hsep f psiR0
    (by
      intro b db zb
      refine (ev_psiR0_iff f b).mpr ?_
      intro z c' _ dz _ zz h
      have e : c' = z := add_zero_left zb h
      rw [e]
      exact K.z2 z b dz zz db zb)
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiR0_iff f x).mp ih
      refine (ev_psiR0_iff f y).mpr ?_
      intro z c' _ dz dc' zz h
      obtain ⟨d, dd, ad, sd⟩ := add_predecessor hsep dx sxy h
      have i : SIso d x := ih' z d dx dz dd zz ad
      exact K.s2 d c' x y dd dc' dx dy sd sxy i)
  intro x hx
  exact (ev_psiR0_iff f x).mp (key x hx)

theorem sem_rs (f : ℕ → N) (K : Known N) : ∀ y : N, SDom y → PRS y := by
  have key := letter_induction hsep f psiRS
    (by
      intro b _ zb
      refine (ev_psiRS_iff f b).mpr ?_
      intro x a c' d' c'' _ dx da _ _ dc'' sxa h1 h2 sd
      have e1 : c' = a := add_zero_left zb h1
      have e2 : d' = x := add_zero_left zb h2
      rw [e1]
      rw [e2] at sd
      exact K.s2 x a x c'' dx da dx dc'' sxa sd (K.irefl x dx))
    (by
      intro y0 b0 dy0 _ syb ih
      have ih' := (ev_psiRS_iff f y0).mp ih
      refine (ev_psiRS_iff f b0).mpr ?_
      intro x a c' d' c'' _ dx da dc' dd' dc'' sxa h1 h2 sd
      obtain ⟨e, de, ae, se⟩ := add_predecessor hsep dy0 syb h1
      obtain ⟨e', de', ae', se'⟩ := add_predecessor hsep dy0 syb h2
      have i : SIso e d' := ih' x a e e' d' dy0 dx da de de' dd' sxa ae ae' se'
      exact K.s2 e c' d' c'' de dc' dd' dc'' se sd i)
  intro y hy
  exact (ev_psiRS_iff f y).mp (key y hy)

theorem sem_ac (f : ℕ → N) (K : Known N) : ∀ a : N, SDom a → PAC a := by
  have R0 := sem_r0 hsep f K
  have RS := sem_rs hsep f K
  have key := letter_induction hsep f psiAC
    (by
      intro a da za
      refine (ev_psiAC_iff f a).mpr ?_
      intro c d d' _ dc _ dd' h1 h2
      have e : d = c := add_zero_left za h1
      rw [e]
      exact K.isym d' c dd' dc (R0 c dc a d' dc da dd' za h2))
    (by
      intro x a dx da sxa ih
      have ih' := (ev_psiAC_iff f x).mp ih
      refine (ev_psiAC_iff f a).mpr ?_
      intro c d d' _ dc dd dd' h1 h2
      obtain ⟨p, dp, ap, sp⟩ := add_predecessor hsep dx sxa h1
      obtain ⟨q, dq, aq⟩ := K.a1 c x dc dx
      have i1 : SIso p q := ih' c p q dx dc dp dq ap aq
      obtain ⟨r, dr, sr⟩ := K.s1 q dq
      have i2 : SIso d' r := RS c dc x a d' q r dc dx da dd' dq dr sxa h2 aq sr
      have i3 : SIso d r := K.s2 p d q r dp dd dq dr sp sr i1
      exact K.itrans d r d' dd dr dd' i3 (K.isym d' r dd' dr i2))
  intro a ha
  exact (ev_psiAC_iff f a).mp (key a ha)

/-- Commutativity of addition in a structure, under the ten known facts. -/
theorem valid_ac (f : ℕ → N) :
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) (sWith10 sAC) := by
  refine (@ev_sWith10 N (sourceLetters s f) sAC).mpr fun H => ?_
  refine (@ev_sAC N (sourceLetters s f)).mpr ?_
  intro a c d d' d1 d2 d3 d4 h1 h2
  have K := known_of f H
  exact (mI_iff f d d').mpr
    (sem_ac hsep f K a ((mD_iff f a).mp d1) c d d' ((mD_iff f a).mp d1) ((mD_iff f c).mp d2)
      ((mD_iff f d).mp d3) ((mD_iff f d').mp d4) ((mA_iff f a c d).mp h1)
      ((mA_iff f c a d').mp h2))

#print axioms sem_r0
#print axioms sem_rs
#print axioms sem_ac
end model

section supply
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] adjunctiveFullSepTheoryDelta

/-- Commutativity of addition is internally provable in the source theory. -/
theorem ac_supply (K : TenFacts (V := V) adjunctiveFullSepTheory) :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp sAC : Bootstrapping.Semiformula V SourceL 0) := by
  apply with_ten K
  apply source_supply
  intro N _ s _ _ hsep f
  exact valid_ac hsep f

#print axioms ac_supply
end supply
end PA194SourceModel
