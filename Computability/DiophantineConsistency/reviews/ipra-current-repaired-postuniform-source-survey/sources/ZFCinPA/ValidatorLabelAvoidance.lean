import ZFCinPA.ValidatorEnvironmentLabels254

set_option autoImplicit false
noncomputable section

/-! Syntax-only label avoidance shared by the C222 and C254 encoders. -/
namespace LeanProofs.ZFCinPA.ValidatorLabelAvoidance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorEnvironmentLabels254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Avoid every stored label; all indices and the vector length are internal. -/
def Avoid (z env : V) : Prop := ∀ i<len env, z≠env.[i]
/-- The finite free vector has the additional fallback label 1. -/
def FreeAvoid (z env : V) : Prop := z≠1 ∧ Avoid z env
/-- Avoid all labels that the encoder may allocate below a binder. -/
def StreamAvoid (z fresh : V) : Prop := ∀ k : V, z≠fresh+2*k

lemma avoid_nil (z : V) : Avoid z (0 : V) := by simp [Avoid]
lemma avoid_cons {z env x : V} (he : Avoid z env) (hx : z≠x) : Avoid z (x∷env) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simpa using hx
  · simpa using he i (by simpa using hi)
lemma free_label_avoids {z env : V} (he : FreeAvoid z env) (i : V) :
    z≠freeLabel env i := by
  classical
  by_cases hi : i<len env
  · simpa [freeLabel,hi] using he.2 i hi
  · simpa [freeLabel,hi] using he.1
lemma stream_head {z fresh : V} (h : StreamAvoid z fresh) : z≠fresh := by
  simpa using h 0
lemma stream_next {z fresh : V} (h : StreamAvoid z fresh) : StreamAvoid z (fresh+2) := by
  intro k
  rw [show (fresh+2)+2*k=fresh+2*(k+1) by ring]
  exact h (k+1)
lemma stream_of_lt {z fresh : V} (h : z<fresh) : StreamAvoid z fresh := by
  intro k
  exact ne_of_lt (lt_of_lt_of_le h (le_add_of_nonneg_right (Arithmetic.zero_le _)))

lemma term_label_avoids {n t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (F B z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    z≠TermLabels.term F B t := by
  rcases ht.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [TermLabels.term_bvar]
    exact hB i (by rwa [hlen])
  · rw [TermLabels.term_fvar]
    exact free_label_avoids hF i
  · exact hf.elim


def StreamEnv (s B : V) : Prop := ∀ k : V, Avoid (s+2*k) B
def StreamFree (s F : V) : Prop := ∀ k : V, FreeAvoid (s+2*k) F
def Apart (s t : V) : Prop := ∀ i j : V, s+2*i ≠ t+2*j

def FreshPair (F B B' s t : V) : Prop :=
  StreamFree s F ∧ StreamFree t F ∧
  StreamEnv s B ∧ StreamEnv s B' ∧
  StreamEnv t B ∧ StreamEnv t B' ∧ Apart s t

private lemma next_label (s k : V) : (s+2)+2*k=s+2*(k+1) := by ring

lemma streamFree_next {s F : V} (h : StreamFree s F) : StreamFree (s+2) F := by
  intro k
  rw [next_label]
  exact h (k+1)

lemma streamEnv_cons_next {s B x : V} (h : StreamEnv s B)
    (hx : ∀ k : V, (s+2)+2*k≠x) : StreamEnv (s+2) (x∷B) := by
  intro k
  apply avoid_cons _ (hx k)
  rw [next_label]
  exact h (k+1)

lemma freshPair_next {F B B' s t : V} (h : FreshPair F B B' s t) :
    FreshPair F (s∷B) (t∷B') (s+2) (t+2) := by
  rcases h with ⟨hsF,htF,hsB,hsB',htB,htB',hap⟩
  have hss : ∀ k : V, (s+2)+2*k≠s := fun k =>
    ((stream_of_lt (z := s) (fresh := s+2) (by simp)) k).symm
  have htt : ∀ k : V, (t+2)+2*k≠t := fun k =>
    ((stream_of_lt (z := t) (fresh := t+2) (by simp)) k).symm
  have hst : ∀ k : V, (s+2)+2*k≠t := by
    intro k
    rw [next_label]
    simpa using hap (k+1) 0
  have hts : ∀ k : V, (t+2)+2*k≠s := by
    intro k
    rw [next_label]
    simpa using (hap 0 (k+1)).symm
  refine ⟨streamFree_next hsF,streamFree_next htF,
    streamEnv_cons_next hsB hss,streamEnv_cons_next hsB' hst,
    streamEnv_cons_next htB hts,streamEnv_cons_next htB' htt,?_⟩
  intro i j
  rw [next_label,next_label]
  exact hap (i+1) (j+1)

/-- Avoidance assumptions for the two cross-bound bodies, uniformly for any
encoder whose vacuity follows from the three label-avoidance conditions. -/
lemma cross_body_vac {P : V → V → Prop} {enc : V → V → V → V → V}
    (hv : ∀ {n p : V}, IsSemiformula ℒₛₑₜ n p → ∀ F B fresh z : V,
      len B=n → FreeAvoid z F → Avoid z B → StreamAvoid z fresh → P z (enc F B fresh p))
    {n p : V} (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (h : FreshPair F B B' s t) :
    P s (enc F (t∷B') (t+2) p) ∧ P t (enc F (s∷B) (s+2) p) := by
  rcases h with ⟨hsF,htF,hsB,hsB',htB,htB',hap⟩
  have hst : s≠t := by simpa using hap 0 0
  constructor
  · apply hv hp F (t∷B') (t+2) s (by simp [hB'])
    · simpa using hsF 0
    · exact avoid_cons (by simpa using hsB' 0) hst
    · intro k
      rw [next_label]
      simpa using hap 0 (k+1)
  · apply hv hp F (s∷B) (s+2) t (by simp [hB])
    · simpa using htF 0
    · exact avoid_cons (by simpa using htB 0) hst.symm
    · intro k
      rw [next_label]
      simpa using (hap (k+1) 0).symm


def alternateStartDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out bound seed. ∃ r < 2, !remDef r seed 2 ∧
    ((r = 0 ∧ out = 2 * (bound + 2) + 1) ∨
     (r ≠ 0 ∧ out = 2 * (bound + 2)))”
noncomputable def alternateStart (bound seed : V) : V := by
  classical
  exact if seed % 2=0 then 2*(bound+2)+1 else 2*(bound+2)

theorem alternateStartGraph : 𝚺₀-Function₂[V] alternateStart via alternateStartDef :=
  .mk fun v => by
    classical
    by_cases hs : v 2 % 2=0 <;>
      simp [alternateStartDef,alternateStart,hs,mod_lt (v 2) (b := 2) (by simp)]

lemma streamEnv_of_lt {s B : V} (hB : B<s) : StreamEnv s B := by
  intro k i _hi
  exact ne_of_gt (lt_of_le_of_lt (nth_le B i)
    (lt_of_lt_of_le hB (le_add_of_nonneg_right (Arithmetic.zero_le _))))

lemma streamFree_of_bounds {s F : V} (hF : F<s) (h1 : 1<s) : StreamFree s F := by
  intro k
  exact ⟨ne_of_gt (lt_of_lt_of_le h1 (le_add_of_nonneg_right (Arithmetic.zero_le _))),
    streamEnv_of_lt hF k⟩

lemma apart_of_mod_ne {s t : V} (h : s % 2≠t % 2) : Apart s t := by
  intro i j hij
  apply h
  simpa using congrArg (fun x : V => x % 2) hij

private lemma double_bound (bound : V) : bound+2≤2*(bound+2) := by
  simp

private lemma double_le_alternateStart (bound seed : V) :
    2*(bound+2)≤alternateStart bound seed := by
  classical
  unfold alternateStart
  split <;> simp

lemma bound_lt_alternateStart (bound seed : V) : bound<alternateStart bound seed :=
  lt_of_lt_of_le (lt_of_lt_of_le (by simp) (double_bound bound))
    (double_le_alternateStart bound seed)

lemma one_lt_alternateStart (bound seed : V) : 1<alternateStart bound seed :=
  lt_of_lt_of_le (lt_of_lt_of_le (by simp : (1:V)<2) (by simp))
    (le_trans (double_bound bound) (double_le_alternateStart bound seed))

lemma alternateStart_mod_ne (bound seed : V) : seed % 2≠alternateStart bound seed % 2 := by
  classical
  by_cases hs : seed % 2=0
  · simp [alternateStart,hs]
  · have hs1 : seed % 2=1 := mod_two_not_zero_iff.mp hs
    simp [alternateStart,hs1]

lemma alternateStart_apart (bound seed : V) : Apart seed (alternateStart bound seed) :=
  apart_of_mod_ne (alternateStart_mod_ne bound seed)

lemma alternateStart_env (bound seed B : V) (hB : B≤bound) :
    StreamEnv (alternateStart bound seed) B :=
  streamEnv_of_lt (lt_of_le_of_lt hB (bound_lt_alternateStart bound seed))

lemma alternateStart_free (bound seed F : V) (hF : F≤bound) :
    StreamFree (alternateStart bound seed) F :=
  streamFree_of_bounds (lt_of_le_of_lt hF (bound_lt_alternateStart bound seed))
    (one_lt_alternateStart bound seed)

/-- A concrete stream avoiding F, fallback1 and both bound stacks. The sum
bound uses existing nth_le, and requires no new maximum-fold computation. -/
lemma alternateStart_resources (F B B' seed : V) :
    StreamFree (alternateStart (F+B+B') seed) F ∧
    StreamEnv (alternateStart (F+B+B') seed) B ∧
    StreamEnv (alternateStart (F+B+B') seed) B' ∧
    Apart seed (alternateStart (F+B+B') seed) := by
  refine ⟨alternateStart_free _ _ _ ?_,alternateStart_env _ _ _ ?_,
    alternateStart_env _ _ _ ?_,alternateStart_apart _ _⟩
  · exact le_trans (le_add_of_nonneg_right (Arithmetic.zero_le B))
      (le_add_of_nonneg_right (Arithmetic.zero_le B'))
  · exact le_trans (le_add_of_nonneg_left (Arithmetic.zero_le F))
      (le_add_of_nonneg_right (Arithmetic.zero_le B'))
  · exact le_add_of_nonneg_left (Arithmetic.zero_le (F+B))


/-- Opposite-parity bridging extends a symmetric transport relation from
apart streams to any two streams avoiding the same free environment. -/
lemma stream_relabel {R : V → V → Prop} (F s t : V)
    (compose : ∀ {a b c}, R a b → R b c → R a c)
    (alpha : ∀ a b, StreamFree a F → StreamFree b F → Apart a b → R a b ∧ R b a)
    (hs : StreamFree s F) (ht : StreamFree t F) : R s t ∧ R t s := by
  classical
  by_cases hmod : s % 2=t % 2
  · let u := alternateStart F s
    have hu : StreamFree u F := alternateStart_free F s F (le_refl F)
    have hsu : Apart s u := alternateStart_apart F s
    have htu : Apart t u := apart_of_mod_ne (by
      rw [← hmod]
      exact alternateStart_mod_ne F s)
    have hsu' := alpha s u hs hu hsu
    have htu' := alpha t u ht hu htu
    exact ⟨compose hsu'.1 htu'.2,compose htu'.1 hsu'.2⟩
  · exact alpha s t hs ht (apart_of_mod_ne hmod)


/-- Transport labels of any typed set term from coordinate transport and
reflexivity. The set language has no function-symbol case. -/
lemma term_labels_related {P : V → V → Prop} {n u : V}
    (hu : IsSemiterm ℒₛₑₜ n u) (F B B' : V) (hB : len B=n)
    (hcoord : ∀ i<len B, P B.[i] B'.[i]) (hrefl : ∀ x, P x x) :
    P (TermLabels.term F B u) (TermLabels.term F B' u) := by
  rcases hu.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [TermLabels.term_bvar,TermLabels.term_bvar]
    exact hcoord i (by rwa [hB])
  · rw [TermLabels.term_fvar,TermLabels.term_fvar]
    exact hrefl _
  · exact hf.elim


/-- Every internal relation symbol of the set language has arity two. -/
lemma set_relation_arity {arity R : V} (hr : (ℒₛₑₜ).IsRel arity R) : arity=2 := by
  have hr' : V ⊧/![arity,R] (LeanProofs.ZFCinPA.instLORDefinableSet.rel).val := hr
  rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.rel : 𝚺₀.Semisentence 2) =
    .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” from rfl] at hr'
  have hc : (arity=2 ∧ R=0) ∨ (arity=2 ∧ R=1) := by simpa using hr'
  exact hc.elim And.left And.left

end LeanProofs.ZFCinPA.ValidatorLabelAvoidance
