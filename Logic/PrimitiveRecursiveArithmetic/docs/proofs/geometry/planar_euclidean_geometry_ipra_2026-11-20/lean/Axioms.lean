import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic

/-!
Constructive coordinate proofs of three of Tarski's axioms.  A point is
a pair of elements of a decidably ordered field.  An affine parameter in [0,1]
witnesses inclusive betweenness.  No real closure or square root is used.
-/
namespace PlanarIPRA.Synthetic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev Point (K : Type*) := K × K

def affine (a b t : K) : K := (1 - t) * a + t * b

def mix (A B : Point K) (t : K) : Point K :=
  (affine A.1 B.1 t, affine A.2 B.2 t)

def Bet (A X B : Point K) : Prop :=
  ∃ t : K, 0 ≤ t ∧ t ≤ 1 ∧ X = mix A B t

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem mix_zero (A B : Point K) : mix A B 0 = A := by
  rcases A with ⟨a, a'⟩
  simp [mix, affine]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem mix_one (A B : Point K) : mix A B 1 = B := by
  rcases B with ⟨b, b'⟩
  simp [mix, affine]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem pasch_coordinate (a b c p q h : K)
    (hh : h ≠ 0) (eqn : h = p + q - p*q) :
    affine (affine a c p) b (p*(1-q)/h) =
    affine (affine b c q) a (q*(1-p)/h) := by
  subst h
  unfold affine
  field_simp
  ring

theorem inner_pasch {A B C P Q : Point K}
    (hP : Bet A P C) (hQ : Bet B Q C) :
    ∃ X, Bet P X B ∧ Bet Q X A := by
  obtain ⟨p, hp, hp', rfl⟩ := hP
  obtain ⟨q, hq, hq', rfl⟩ := hQ
  let h := p + q - p*q
  have ph : p ≤ h := by dsimp [h]; nlinarith [mul_nonneg (sub_nonneg.mpr hp') hq]
  have qh : q ≤ h := by dsimp [h]; nlinarith [mul_nonneg (sub_nonneg.mpr hq') hp]
  by_cases hz : h = 0
  · have pz : p = 0 := le_antisymm (hz ▸ ph) hp
    have qz : q = 0 := le_antisymm (hz ▸ qh) hq
    simp only [pz, qz, mix_zero]
    exact ⟨A, ⟨0, le_rfl, zero_le_one, (mix_zero A B).symm⟩,
               ⟨1, zero_le_one, le_rfl, (mix_one B A).symm⟩⟩
  · have hh : 0 < h := lt_of_le_of_ne (hp.trans ph) (Ne.symm hz)
    let r := p*(1-q)/h
    let s := q*(1-p)/h
    have hr : 0 ≤ r := div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq')) hh.le
    have hs : 0 ≤ s := div_nonneg (mul_nonneg hq (sub_nonneg.mpr hp')) hh.le
    have hr' : r ≤ 1 := by
      apply (div_le_one hh).2
      dsimp [h]; nlinarith
    have hs' : s ≤ 1 := by
      apply (div_le_one hh).2
      dsimp [h]; nlinarith
    refine ⟨mix (mix A C p) B r, ⟨r, hr, hr', rfl⟩, s, hs, hs', ?_⟩
    apply Prod.ext
    · exact pasch_coordinate _ _ _ _ _ h hz rfl
    · exact pasch_coordinate _ _ _ _ _ h hz rfl

private def extendFrom (A B : Point K) (s : K) : Point K :=
  (A.1 + (B.1 - A.1)/s, A.2 + (B.2 - A.2)/s)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem extend_coordinate (a b s : K) (hs : s ≠ 0) :
    affine a (a + (b-a)/s) s = b := by
  unfold affine
  field_simp
  ring

omit [IsStrictOrderedRing K] in
private theorem extend_bet (A B : Point K) {s : K} (hs : 0 < s) (hs' : s ≤ 1) :
    Bet A B (extendFrom A B s) := by
  refine ⟨s, hs.le, hs', ?_⟩
  apply Prod.ext
  · exact (extend_coordinate _ _ _ hs.ne').symm
  · exact (extend_coordinate _ _ _ hs.ne').symm

private theorem euclid_coordinate {a b c z s t : K} (hs : s ≠ 0)
    (eqn : affine a z s = affine b c t) :
    z = affine (a+(b-a)/s) (a+(c-a)/s) t := by
  unfold affine at *
  field_simp
  nlinarith only [eqn]

theorem euclid {A B C D T : Point K}
    (h₁ : Bet A D T) (h₂ : Bet B D C) (hd : A ≠ D) :
    ∃ X Y, Bet A B X ∧ Bet A C Y ∧ Bet X T Y := by
  obtain ⟨s, hs, hs', es⟩ := h₁
  obtain ⟨t, ht, ht', et⟩ := h₂
  have hsn : s ≠ 0 := by
    intro hz
    rw [hz, mix_zero] at es
    exact hd es.symm
  have hp := lt_of_le_of_ne hs (Ne.symm hsn)
  refine ⟨extendFrom A B s, extendFrom A C s, extend_bet A B hp hs',
    extend_bet A C hp hs', t, ht, ht', ?_⟩
  have eqn := es.symm.trans et
  apply Prod.ext
  · exact euclid_coordinate hsn (congrArg Prod.fst eqn)
  · exact euclid_coordinate hsn (congrArg Prod.snd eqn)


def distSq (A B : Point K) : K := (B.1-A.1)^2 + (B.2-A.2)^2

def Cong (A B C D : Point K) : Prop := distSq A B = distSq C D

private def past (A B : Point K) (k : K) : Point K :=
  (B.1+k*(B.1-A.1), B.2+k*(B.2-A.2))

private theorem past_coordinate {a b c t : K} (ht : t ≠ 0)
    (h : b = affine a c t) : c = b + ((1-t)/t)*(b-a) := by
  unfold affine at h
  field_simp
  nlinarith only [h]

private theorem past_of_bet {A B C : Point K} (h : Bet A B C) (hne : A ≠ B) :
    ∃ k, 0 ≤ k ∧ C = past A B k := by
  obtain ⟨t, ht, ht', eqn⟩ := h
  have htn : t ≠ 0 := by
    intro hz
    rw [hz, mix_zero] at eqn
    exact hne eqn.symm
  refine ⟨(1-t)/t, div_nonneg (sub_nonneg.mpr ht') ht, Prod.ext ?_ ?_⟩
  · exact past_coordinate htn (congrArg Prod.fst eqn)
  · exact past_coordinate htn (congrArg Prod.snd eqn)

private theorem dist_pos {A B : Point K} (hne : A ≠ B) : 0 < distSq A B := by
  by_contra! h
  unfold distSq at h
  apply hne
  apply Prod.ext
  · have hx : (B.1-A.1)^2 = 0 := by nlinarith [sq_nonneg (B.2-A.2), sq_nonneg (B.1-A.1)]
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm
  · have hy : (B.2-A.2)^2 = 0 := by nlinarith [sq_nonneg (B.1-A.1), sq_nonneg (B.2-A.2)]
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hy)).symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem past_dist (A B : Point K) (k : K) :
    distSq B (past A B k) = k^2*distSq A B := by
  simp only [distSq, past]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem five_identity (A B D : Point K) (k : K) :
    distSq (past A B k) D = (1+k)*distSq B D - k*distSq A D
      + k*(1+k)*distSq A B := by
  simp only [distSq, past]
  ring

theorem five_segment {A B C D A' B' C' D' : Point K}
    (hab : Cong A B A' B') (hbc : Cong B C B' C')
    (had : Cong A D A' D') (hbd : Cong B D B' D')
    (bet : Bet A B C) (bet' : Bet A' B' C') (hne : A ≠ B) :
    Cong C D C' D' := by
  unfold Cong at *
  have hp := dist_pos hne
  have hne' : A' ≠ B' := by
    intro eqn
    rw [hab, eqn] at hp
    simp [distSq] at hp
  obtain ⟨k, hk, rfl⟩ := past_of_bet bet hne
  obtain ⟨k', hk', rfl⟩ := past_of_bet bet' hne'
  rw [past_dist, past_dist, ← hab] at hbc
  have eqsq := mul_right_cancel₀ hp.ne' hbc
  have factor : (k-k')*(k+k') = 0 := by nlinarith only [eqsq]
  have eqn : k = k' := by
    rcases mul_eq_zero.mp factor with f | f <;> linarith
  rw [five_identity, five_identity, eqn, hab, had, hbd]


/-- Polynomial test, with coordinate ordering identical to the formula translator. -/
def polyBet (A P B : Point K) : Prop :=
  (B.1-A.1)*(P.2-A.2) = (B.2-A.2)*(P.1-A.1) ∧
  (P.1-A.1)*(P.1-B.1) + (P.2-A.2)*(P.2-B.2) ≤ 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem mix_dot (A B : Point K) (t : K) :
    ((mix A B t).1-A.1)*((mix A B t).1-B.1)
    + ((mix A B t).2-A.2)*((mix A B t).2-B.2) =
    t*(t-1)*distSq A B := by
  simp only [mix, affine, distSq]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem affine_pivot {a b : K} (p : K) (hn : b-a ≠ 0) :
    p = affine a b ((p-a)/(b-a)) := by
  unfold affine
  field_simp
  ring

private theorem affine_other {a b p a' b' p' : K} (hn : b-a ≠ 0)
    (hd : (b-a)*(p'-a') = (b'-a')*(p-a)) :
    p' = affine a' b' ((p-a)/(b-a)) := by
  unfold affine
  field_simp
  nlinarith only [hd]

private theorem scaled_of_cross {A P B : Point K} (hne : A ≠ B)
    (hd : (B.1-A.1)*(P.2-A.2) = (B.2-A.2)*(P.1-A.1)) :
    ∃ t : K, P = mix A B t := by
  by_cases hx : B.1-A.1 = 0
  · have hy : B.2-A.2 ≠ 0 := by
      intro hz
      exact hne (Prod.ext (sub_eq_zero.mp hx).symm (sub_eq_zero.mp hz).symm)
    exact ⟨_, Prod.ext (affine_other hy hd.symm) (affine_pivot _ hy)⟩
  · exact ⟨_, Prod.ext (affine_pivot _ hx) (affine_other hx hd)⟩

theorem bet_iff_polyBet (A P B : Point K) : Bet A P B ↔ polyBet A P B := by
  constructor
  · rintro ⟨t, ht, ht', rfl⟩
    constructor
    · dsimp [mix, affine]; ring
    · rw [mix_dot]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr ht'))
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · rintro ⟨hd, hdot⟩
    by_cases hne : A = B
    · subst B
      have eqn : P = A := by
        by_contra hp
        have pos := dist_pos (Ne.symm hp)
        unfold distSq at pos
        nlinarith only [hdot, pos]
      exact ⟨0, le_rfl, zero_le_one, eqn.trans (mix_zero A A).symm⟩
    obtain ⟨t, rfl⟩ := scaled_of_cross hne hd
    rw [mix_dot] at hdot
    have hs : t*(t-1) ≤ 0 := nonpos_of_mul_nonpos_left hdot (dist_pos hne)
    rcases mul_nonpos_iff.mp hs with h | h
    · exact ⟨t, h.1, by linarith [h.2], rfl⟩
    · exact ⟨t, by linarith [h.2], by linarith [h.1], rfl⟩

end PlanarIPRA.Synthetic
