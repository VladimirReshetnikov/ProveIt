import BusyBeaver.ZFC.KSeed222
import BusyBeaver.ZFC.ConstructibleReflect
import BusyBeaver.ZFC.ConstructibleChoice
import BusyBeaver.ZFC.NamedForm254

/-!
The upper consistency bound for the 222/221 calculus: if ZF is consistent, the code 1 is not
derivable.

Elliot Glazer's K holds in the constructible universe. In a model of ZF with `V = L`, take the
parameters, the input and the power-set formula into a stage `L_β` that reflects the matrix
and the power-set formula (`ConstructibleReflect.reflect`, `closed_exists`). `L_β` is then
transitive and closed under subsets of its members, and the container

  `C = {y ∈ L_β : ∃ x ∈ L_β, φ(y, x)}`

witnesses the seed property for every definable relation (`seed_in_VL`). Hence every decoded
seed bundle holds in the constructible model of any model of ZF (`bundles_in_L`), which is
irreflexive, and `c222_sound` refutes the code 1 there (`zf_refutation_of_c222`).
-/

namespace SetTheory.BusyBeaver.ZFC.KUpper222

open InternalOrd Constructible ConstructibleZF ConstructibleReflect LeanProofs.BoundedZFCConsistency
open SetTheory.BusyBeaver.ZFC.KCode222 SetTheory.BusyBeaver.ZFC.KSeed222
open Form

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The power-set formula at `u = 0`, and its body at `P = 0, u = 1`. -/
def powBody : Form := fAll (fIff (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 3))))
def powF : Form := fEx powBody

theorem sat_powBody (e : Nat → V) :
    Sat mem e powBody ↔ ∀ z, (mem z (e 0) ↔ ∀ w, mem w z → mem w (e 1)) := by
  simp only [powBody, Sat, Sat_fIff, scons]

section VL

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
  (hVL : ∀ x, InL H hP x)
include H hR hP hVL

omit hR in

/-- Under `V = L`, satisfaction relative to `L` is satisfaction. -/
theorem csat_iff_sat : ∀ (φ : Form) (e : Nat → V), CSat mem (InL H hP) e φ ↔ Sat mem e φ
  | .fMem _ _, _ => Iff.rfl
  | .fEq _ _, _ => Iff.rfl
  | .fBot, _ => Iff.rfl
  | .fImp a b, e | .fAnd a b, e | .fOr a b, e => by
      simp only [CSat, Sat]; rw [csat_iff_sat a e, csat_iff_sat b e]
  | .fAll a, e => by
      simp only [CSat, Sat]
      exact forall_congr' fun d => ⟨fun h => (csat_iff_sat a _).1 (h (hVL d)),
        fun h _ => (csat_iff_sat a _).2 h⟩
  | .fEx a, e => by
      simp only [CSat, Sat]
      exact exists_congr fun d => ⟨fun h => (csat_iff_sat a _).1 h.2,
        fun h => ⟨hVL d, (csat_iff_sat a _).2 h⟩⟩

/-- Finitely many values of an environment lie in one stage. -/
theorem finite_stage (v : Nat → V) :
    ∀ N, ∃ b T, Ord mem b ∧ IsL H hP b T ∧ ∀ k, k < N → mem (v k) T
  | 0 => by
      have hb : Ord mem (vempty H) := ord_of_mem (ord_omega H) (vempty_in_omega H)
      obtain ⟨T, hT⟩ := isL_exists H hR hP hb
      exact ⟨_, T, hb, hT, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | N + 1 => by
      obtain ⟨b, T, hb, hT, hv⟩ := finite_stage v N
      obtain ⟨b', T', hb', hT', hTT, hvN⟩ :=
        stage_bound2 H hR hP (inL_stage H hR hP hb hT) (hVL (v N))
      refine ⟨b', T', hb', hT', fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact isL_trans H hR hP hb' hT' T hTT _ (hv k hk)
      · exact hvN

/-- **Glazer's K, seed form, holds in models of `ZF + V = L`**, for every definable relation. -/
theorem seed_in_VL (φ : Form) (e : Nat → V) (A : V) :
    SeedProp mem (fun x y => Sat mem (scons y (scons x e)) φ) A := by
  -- truncate the parameters to the free variables of φ
  let N := bound φ
  let e' : Nat → V := fun k => if k + 2 < N then e k else A
  have hQ : ∀ x y, Sat mem (scons y (scons x e)) φ ↔ Sat mem (scons y (scons x e')) φ := by
    intro x y
    apply Sat_ext_free
    intro n hn
    have := free_lt_bound φ n hn
    match n, this with
    | 0, _ => rfl
    | 1, _ => rfl
    | k + 2, h => simp only [scons, e']; rw [if_pos h]
  have hQfun : (fun x y => Sat mem (scons y (scons x e)) φ) =
      (fun x y => Sat mem (scons y (scons x e')) φ) :=
    funext fun x => funext fun y => propext (hQ x y)
  rw [hQfun]
  -- one stage holding A and the parameters, then a closed stage above it
  let v : Nat → V := scons A e'
  obtain ⟨a0, T0, ha0, hT0, hv0⟩ := finite_stage H hR hP hVL v (N + 1)
  have hvT0 : ∀ n, mem (v n) T0 := by
    intro n
    by_cases hn : n < N + 1
    · exact hv0 n hn
    · match n, hn with
      | 0, h => exact absurd (Nat.zero_lt_succ N) h
      | k + 1, h =>
          have : ¬ k + 2 < N := by omega
          have hk : v (k + 1) = A := by simp only [v, scons, e']; rw [if_neg this]
          rw [hk]; exact hv0 0 (Nat.zero_lt_succ N)
  let Θ : List Form := qbodies (fEx φ) ++ qbodies powF
  obtain ⟨β, haβ, hC⟩ := closed_exists H hR hP Θ ha0
  have hβ : Ord mem β := hC.1
  obtain ⟨Tβ, hTβ⟩ := isL_exists H hR hP hβ
  have hT0β : Sub mem T0 Tβ := isL_mono H hR hP hβ haβ hT0 hTβ
  have htrans : Trans mem Tβ := isL_trans H hR hP hβ hTβ
  have hA : mem A Tβ := hT0β _ (hvT0 0)
  have he' : ∀ k, mem (e' k) Tβ := fun k => hT0β _ (hvT0 (k + 1))
  have hscons : ∀ x y, mem x Tβ → mem y Tβ → ∀ n, mem (scons y (scons x e') n) Tβ :=
    fun _ _ hx hy n => match n with | 0 => hy | 1 => hx | k + 2 => he' k
  have hscons1 : ∀ x, mem x Tβ → ∀ n, mem (scons x e' n) Tβ :=
    fun _ hx n => match n with | 0 => hx | k + 1 => he' k
  have hΘ1 : ∀ θ ∈ qbodies (fEx φ), θ ∈ Θ := fun θ h => List.mem_append_left _ h
  have hΘφ : ∀ θ ∈ qbodies φ, θ ∈ Θ := fun θ h =>
    hΘ1 θ (by simp only [qbodies]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hΘp : ∀ θ ∈ qbodies powF, θ ∈ Θ := fun θ h => List.mem_append_right _ h
  have hΘb : ∀ θ ∈ qbodies powBody, θ ∈ Θ := fun θ h =>
    hΘp θ (by simp only [powF, qbodies]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  -- reflection of the matrix and of its existential closure
  have reflφ : ∀ x y, mem x Tβ → mem y Tβ →
      (Sat mem (scons y (scons x e')) φ ↔ RSat mem Tβ (scons y (scons x e')) φ) := by
    intro x y hx hy
    rw [← csat_iff_sat H hP hVL]
    exact reflect H hR hP hC hTβ φ hΘφ _ (hscons x y hx hy)
  -- the request of an input in Tβ is answered in Tβ
  have answer : ∀ x, mem x Tβ → ∀ y, Sat mem (scons y (scons x e')) φ →
      ∃ z, mem z Tβ ∧ Sat mem (scons z (scons x e')) φ := by
    intro x hx y hy
    have hex : Sat mem (scons x e') (fEx φ) := ⟨y, hy⟩
    rw [← csat_iff_sat H hP hVL] at hex
    have hr := (reflect H hR hP hC hTβ (fEx φ) hΘ1 _ (hscons1 x hx)).1 hex
    obtain ⟨z, hz, hrz⟩ := hr
    exact ⟨z, hz, (reflφ x z hx hz).2 hrz⟩
  -- Tβ is closed under subsets of its members
  have subclosed : ∀ u, mem u Tβ → ∀ x', (∀ w, mem w x' → mem w u) → mem x' Tβ := by
    intro u hu x' hsub
    obtain ⟨p, hp⟩ := hP u
    have hpow : Sat mem (scons u e') powF := by
      refine ⟨p, (sat_powBody _).2 fun z => ?_⟩
      simp only [scons]; exact hp z
    rw [← csat_iff_sat H hP hVL] at hpow
    obtain ⟨P', hP'T, hP'⟩ := (reflect H hR hP hC hTβ powF hΘp _ (hscons1 u hu)).1 hpow
    have henv : ∀ n, mem (scons P' (scons u e') n) Tβ := fun n =>
      match n with | 0 => hP'T | k + 1 => hscons1 u hu k
    have hreal := (reflect H hR hP hC hTβ powBody hΘb _ henv).2 hP'
    rw [csat_iff_sat H hP hVL, sat_powBody] at hreal
    have hx'P : mem x' P' := (hreal x').2 hsub
    exact htrans P' hP'T x' hx'P
  -- the container, by Separation over Tβ
  let r : Nat → Nat := fun n => match n with | 0 => 1 | 1 => 0 | k + 2 => k + 3
  let σ : Form := fEx (fAnd (fMem 0 2) (rename r φ))
  obtain ⟨C, hCspec⟩ := H.sep σ (scons Tβ e') Tβ
  have hmemC : ∀ y, mem y C ↔ mem y Tβ ∧ ∃ x, mem x Tβ ∧ Sat mem (scons y (scons x e')) φ := by
    intro y
    rw [hCspec y]
    refine and_congr_right fun _ => ?_
    simp only [σ, Sat, scons]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [Sat_rename]
    exact Sat_ext _ _ _ fun n => by rcases n with _ | _ | _ <;> rfl
  refine ⟨C, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hzφ⟩ := answer A hA y hy
    exact ⟨z, hzφ, (hmemC z).2 ⟨hz, A, hA, hzφ⟩⟩
  · intro y hy
    obtain ⟨hyT, x, hxT, hxy⟩ := (hmemC y).1 hy
    refine ⟨x, hxy, fun x' hsub y' hy' => ?_⟩
    have hx'T := subclosed y hyT x' hsub
    obtain ⟨z, hz, hzφ⟩ := answer x' hx'T y' hy'
    exact ⟨z, hzφ, (hmemC z).2 ⟨hz, x', hx'T, hzφ⟩⟩

end VL

/-! ## Every decoded seed bundle holds in the constructible model -/

/-- Slots: the output name `b` to 0, the input name `a` to 1, the rest shifted by two. -/
def roleSlots (a b i : Nat) : Nat := if i = b then 0 else if i = a then 1 else i + 2

theorem roleSlots_env {W : Type u} (e : Nat → W) (a b : Nat) (x y : W) :
    (fun i => scons y (scons x e) (roleSlots a b i)) = Tarski.update (Tarski.update e a x) b y := by
  funext i
  by_cases hb : i = b
  · simp [roleSlots, hb, Tarski.update, scons]
  · by_cases ha : i = a
    · subst ha; simp [roleSlots, hb, Tarski.update, scons]
    · simp [roleSlots, hb, ha, Tarski.update, scons]

section Model

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

theorem bundles_in_L (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) (e : Nat → {x // InL H hP x}) :
    Tarski.Sat (memL H hP) e (Code254.dec (bundle222 a b c)) := by
  have hirr : ∀ x : {x // InL H hP x}, ¬ memL H hP x x := fun x => mem_irrefl H hR x.1
  apply bundle_of_seed (memL H hP) hirr e a b c hca hcb
  have hS := seed_in_VL (L_zfAxioms H hR hP) (L_regular H hR hP) (L_power H hR hP)
    (ConstructibleAbs.vEqL H hR hP) (NamedForm254.translate (roleSlots a b) (Code254.dec c)) e (e a)
  have hQ : (fun x y => Sat (memL H hP) (scons y (scons x e))
        (NamedForm254.translate (roleSlots a b) (Code254.dec c))) = matrixRel (memL H hP) e a b c := by
    funext x y
    apply propext
    rw [NamedForm254.sat_translate, roleSlots_env]
    rfl
  exact hQ ▸ hS

end Model

/-- **Upper bound.** A derivation of the code 1 refutes ZF. -/
theorem zf_refutation_of_c222 (h : C222 Code254.F) : BProv ZFax_s [] Form.fBot :=
  completeness_inf_context ZFax_s [] Form.fBot Sentences_ZF fun _ m v hZF _ => by
    obtain ⟨H, hP, hR⟩ := ZFNative.models_ZF m v hZF
    have h0 : InL H hP (vempty H) :=
      inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))
    exact False.elim (no_model_of_c222_one h (memL H hP) (fun x => mem_irrefl H hR x.1)
      (bundles_in_L H hR hP) (fun _ => ⟨vempty H, h0⟩))

#print axioms seed_in_VL
#print axioms zf_refutation_of_c222

end SetTheory.BusyBeaver.ZFC.KUpper222
