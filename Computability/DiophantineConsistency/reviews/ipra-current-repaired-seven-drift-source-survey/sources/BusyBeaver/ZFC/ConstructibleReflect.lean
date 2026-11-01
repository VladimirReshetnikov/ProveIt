import BusyBeaver.ZFC.Constructible
import BusyBeaver.ZFC.ZFRank

/-!
Reflection for the constructible hierarchy, inside a model of ZF.

Separation in `L` needs, for each formula `φ`, a stage `L_β` that reflects
`φ`: truth in `L` (quantifiers over the constructible class) agrees with
truth with quantifiers bounded by `L_β`. This module builds the machinery:

* `CSat P`: satisfaction with quantifiers over a class `P`, which depends only
  on the free variables (`csat_ext_free`);
* `relT`: the named translation of a De Bruijn formula with every quantifier
  guarded by a class formula, with fresh binder names (`nsat_relT`);
* internal numerals (`natF`) and formulas that read the values of an internal
  environment (`valF`, `envSatF`), so that "`φ` holds in `L` at
  `x, E(0), E(1), …`" is itself a named formula.
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleReflect

open NamedZF NForm InternalOrd InternalRank TransRec ConstructibleDef Constructible
  LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Satisfaction relativized to a class -/

def CSat (mem : V → V → Prop) (P : V → Prop) : (Nat → V) → Form → Prop
  | e, .fMem i j => mem (e i) (e j)
  | e, .fEq i j => e i = e j
  | _, .fBot => False
  | e, .fImp a b => CSat mem P e a → CSat mem P e b
  | e, .fAnd a b => CSat mem P e a ∧ CSat mem P e b
  | e, .fOr a b => CSat mem P e a ∨ CSat mem P e b
  | e, .fAll a => ∀ d, P d → CSat mem P (scons d e) a
  | e, .fEx a => ∃ d, P d ∧ CSat mem P (scons d e) a

theorem csat_ext_free (P : V → Prop) :
    ∀ (φ : Form) (e1 e2 : Nat → V), (∀ n, Free n φ → e1 n = e2 n) →
      (CSat mem P e1 φ ↔ CSat mem P e2 φ)
  | .fMem i j, e1, e2, h | .fEq i j, e1, e2, h => by
      simp only [CSat]; rw [h i (Or.inl rfl), h j (Or.inr rfl)]
  | .fBot, _, _, _ => Iff.rfl
  | .fImp a b, e1, e2, h | .fAnd a b, e1, e2, h | .fOr a b, e1, e2, h => by
      simp only [CSat]
      rw [csat_ext_free P a e1 e2 fun n hn => h n (Or.inl hn),
        csat_ext_free P b e1 e2 fun n hn => h n (Or.inr hn)]
  | .fAll a, e1, e2, h => by
      simp only [CSat]
      refine forall_congr' fun d => imp_congr_right fun _ => csat_ext_free P a _ _ fun n hn => ?_
      cases n with
      | zero => rfl
      | succ m => exact h m hn
  | .fEx a, e1, e2, h => by
      simp only [CSat]
      refine exists_congr fun d => and_congr_right fun _ => csat_ext_free P a _ _ fun n hn => ?_
      cases n with
      | zero => rfl
      | succ m => exact h m hn

/-! ## Relativized translation into named formulas -/

def consSlot (f : Nat) (s : Nat → Nat) : Nat → Nat
  | 0 => f
  | i + 1 => s i

/-- Translate a De Bruijn formula, reading slot `i` at name `s i`, binding
quantified variables at the fresh names `f, f + 1, …`, and guarding every
quantifier by the class formula `C`. -/
def relT (C : Nat → NForm) : (Nat → Nat) → Nat → Form → NForm
  | s, _, .fMem i j => .mem (s i) (s j)
  | s, _, .fEq i j => .eq (s i) (s j)
  | _, _, .fBot => .bot
  | s, f, .fImp a b => .imp (relT C s f a) (relT C s f b)
  | s, f, .fAnd a b => .and (relT C s f a) (relT C s f b)
  | s, f, .fOr a b => .or (relT C s f a) (relT C s f b)
  | s, f, .fAll a => .all f (.imp (C f) (relT C (consSlot f s) (f + 1) a))
  | s, f, .fEx a => .ex f (.and (C f) (relT C (consSlot f s) (f + 1) a))

theorem nsat_relT (P : V → Prop) (C : Nat → NForm) (hC : ∀ ρ x, NSat mem ρ (C x) ↔ P (ρ x)) :
    ∀ (φ : Form) (s : Nat → Nat) (f : Nat) (ρ : Nat → V), (∀ i, s i < f) →
      (NSat mem ρ (relT C s f φ) ↔ CSat mem P (fun i => ρ (s i)) φ)
  | .fMem _ _, _, _, _, _ | .fEq _ _, _, _, _, _ | .fBot, _, _, _, _ => Iff.rfl
  | .fImp a b, s, f, ρ, hs | .fAnd a b, s, f, ρ, hs | .fOr a b, s, f, ρ, hs => by
      simp only [relT, NSat, CSat, nsat_relT P C hC a s f ρ hs, nsat_relT P C hC b s f ρ hs]
  | .fAll a, s, f, ρ, hs => by
      simp only [relT, NSat, CSat, hC, upd_same]
      refine forall_congr' fun d => imp_congr_right fun _ => ?_
      rw [nsat_relT P C hC a (consSlot f s) (f + 1) _ fun i => by
        cases i with
        | zero => simp [consSlot]
        | succ i => simp only [consSlot]; have := hs i; omega]
      refine Iff.of_eq (congrArg (fun e => CSat mem P e a) (funext fun i => ?_))
      cases i with
      | zero => simp [consSlot, scons]
      | succ i => simp only [consSlot, scons]; exact upd_other _ _ (by have := hs i; omega)
  | .fEx a, s, f, ρ, hs => by
      simp only [relT, NSat, CSat, hC, upd_same]
      refine exists_congr fun d => and_congr_right fun _ => ?_
      rw [nsat_relT P C hC a (consSlot f s) (f + 1) _ fun i => by
        cases i with
        | zero => simp [consSlot]
        | succ i => simp only [consSlot]; have := hs i; omega]
      refine Iff.of_eq (congrArg (fun e => CSat mem P e a) (funext fun i => ?_))
      cases i with
      | zero => simp [consSlot, scons]
      | succ i => simp only [consSlot, scons]; exact upd_other _ _ (by have := hs i; omega)

/-! ## Internal numerals and environment values -/

/-- `n = natV k`. -/
def natF (n : Nat) : Nat → NForm
  | 0 => .all (n + 1) (.imp (.mem (n + 1) n) .bot)
  | k + 1 => .ex (n + 1) (.and (natF (n + 1) k) (succF n (n + 1)))

theorem nsat_natF (H : ZFAxioms mem) : ∀ (k : Nat) (ρ : Nat → V) (n : Nat),
    NSat mem ρ (natF n k) ↔ ρ n = natV H k
  | 0, ρ, n => by
      simp only [natF, NSat]
      simp (disch := omega) only [upd_same, upd_other]
      constructor
      · intro h
        exact H.ext _ _ fun d => ⟨fun hd => absurd hd (h d), fun hd => absurd hd (vempty_spec H d)⟩
      · intro h d hd; rw [h] at hd; exact vempty_spec H d hd
  | k + 1, ρ, n => by
      simp only [natF, NSat, nsat_natF H k, nsat_succF H]
      simp (disch := omega) only [upd_same, upd_other]
      constructor
      · rintro ⟨m, rfl, h⟩; exact h
      · intro h; exact ⟨_, rfl, h⟩

/-- `v = E(k)`: `⟨k, v⟩ ∈ E`. -/
def valF (E k v : Nat) : NForm :=
  .ex (E + v + 1) (.and (natF (E + v + 1) k) (pmemF E (E + v + 1) v))

theorem nsat_valF (H : ZFAxioms mem) (ρ : Nat → V) (E k v : Nat) {A : V}
    (hE : IsEnvOn H A (ρ E)) : NSat mem ρ (valF E k v) ↔ ρ v = applyV H (ρ E) (natV H k) := by
  simp only [valF, NSat, nsat_natF H, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨m, rfl, h⟩; exact (applyV_eq H hE.1.1 h).symm
  · intro h
    exact ⟨_, rfl, h ▸ applyV_mem H (hE.1.2.1 _ (natV_mem_omega H k))⟩

/-! ## Truth in a class at an internal environment -/

/-- Bind the names `b + k, …, b + k + j - 1` to the values `E(k), …, E(k + j - 1)`. -/
def bindVals (E b : Nat) : Nat → Nat → NForm → NForm
  | 0, _, body => body
  | j + 1, k, body => .ex (b + k) (.and (valF E k (b + k)) (bindVals E b j (k + 1) body))

/-- The environment after `bindVals`. -/
noncomputable def fillVals (H : ZFAxioms mem) (E b : Nat) : Nat → Nat → (Nat → V) → (Nat → V)
  | 0, _, ρ => ρ
  | j + 1, k, ρ => fillVals H E b j (k + 1) (upd ρ (b + k) (applyV H (ρ E) (natV H k)))

/-- `fillVals` touches only the names `b + k, …, b + k + j - 1`. -/
theorem fillVals_out (H : ZFAxioms mem) (E b : Nat) :
    ∀ (j k : Nat) (ρ : Nat → V) (n : Nat), (n < b + k ∨ b + k + j ≤ n) →
      fillVals H E b j k ρ n = ρ n
  | 0, _, _, _, _ => rfl
  | j + 1, k, ρ, n, h => by
      simp only [fillVals]
      rw [fillVals_out H E b j (k + 1) _ n (by omega), upd_other _ _ (by omega)]

theorem fillVals_low (H : ZFAxioms mem) (E b j k : Nat) (ρ : Nat → V) {n : Nat} (hn : n < b) :
    fillVals H E b j k ρ n = ρ n :=
  fillVals_out H E b j k ρ n (Or.inl (by omega))

theorem fillVals_val (H : ZFAxioms mem) (E b : Nat) (hE : E < b) :
    ∀ (j k : Nat) (ρ : Nat → V) (i : Nat), k ≤ i → i < k + j →
      fillVals H E b j k ρ (b + i) = applyV H (ρ E) (natV H i)
  | 0, _, _, _, h1, h2 => by omega
  | j + 1, k, ρ, i, h1, h2 => by
      simp only [fillVals]
      by_cases hi : i = k
      · subst hi
        rw [fillVals_out H E b j (i + 1) _ (b + i) (Or.inl (by omega)), upd_same]
      · rw [fillVals_val H E b hE j (k + 1) _ i (by omega) (by omega), upd_other _ _ (by omega)]

theorem bindVals_spec (H : ZFAxioms mem) (E b : Nat) (hE : E < b) {A : V} :
    ∀ (j k : Nat) (ρ : Nat → V) (body : NForm), IsEnvOn H A (ρ E) →
      (NSat mem ρ (bindVals E b j k body) ↔ NSat mem (fillVals H E b j k ρ) body)
  | 0, _, _, _, _ => Iff.rfl
  | j + 1, k, ρ, body, hEnv => by
      have hE' : ∀ v, upd ρ (b + k) v E = ρ E := fun v => upd_other _ _ (by omega)
      have hEnv' : ∀ v, IsEnvOn H A (upd ρ (b + k) v E) := fun v => by rwa [hE' v]
      simp only [bindVals, NSat, fillVals]
      constructor
      · rintro ⟨v, hv, hb⟩
        rw [nsat_valF H _ E k (b + k) (hEnv' v), upd_same, hE'] at hv
        subst hv
        exact (bindVals_spec H E b hE j (k + 1) _ body (hEnv' _)).1 hb
      · intro h
        refine ⟨applyV H (ρ E) (natV H k), ?_, (bindVals_spec H E b hE j (k + 1) _ body (hEnv' _)).2 h⟩
        rw [nsat_valF H _ E k (b + k) (hEnv' _), upd_same, hE']

def envSlots (x b m : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => if k < m then b + k else b

/-- "`φ` holds in the class `C` at `x, E(0), E(1), …`", with fresh names from `b` on. -/
def envSatF (C : Nat → NForm) (φ : Form) (x E b : Nat) : NForm :=
  bindVals E b (bound φ) 0 (relT C (envSlots x b (bound φ)) (b + bound φ + 1) φ)

theorem nsat_envSatF (H : ZFAxioms mem) (P : V → Prop) (C : Nat → NForm)
    (hC : ∀ ρ x, NSat mem ρ (C x) ↔ P (ρ x)) (φ : Form) {x E b : Nat} (hx : x < b) (hEb : E < b)
    (ρ : Nat → V) {A : V} (hEnv : IsEnvOn H A (ρ E)) :
    NSat mem ρ (envSatF C φ x E b) ↔ CSat mem P (scons (ρ x) (envVals H (ρ E))) φ := by
  unfold envSatF
  rw [bindVals_spec H E b hEb _ 0 ρ _ hEnv, nsat_relT P C hC φ _ _ _ fun i => by
    cases i with
    | zero => simp only [envSlots]; omega
    | succ k => simp only [envSlots]; split <;> omega]
  refine csat_ext_free P φ _ _ fun n hn => ?_
  have hlt := free_lt_bound φ n hn
  cases n with
  | zero => simp only [envSlots, scons]; exact fillVals_low H E b _ 0 ρ hx
  | succ k =>
      simp only [envSlots, scons, show k < bound φ by omega, if_true]
      exact fillVals_val H E b hEb _ 0 ρ k (by omega) (by omega)

/-! ## Sets of environments -/

section Envs

variable (H : ZFAxioms mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hP

/-- The internal environments over a set form a set. -/
theorem envs_exists (T : V) : ∃ Es, ∀ E, mem E Es ↔ IsEnvOn H T E := by
  let B := vcup H (omegaV H) T
  obtain ⟨P1, hP1⟩ := hP B
  obtain ⟨P2, hP2⟩ := hP P1
  obtain ⟨P3, hP3⟩ := hP P2
  obtain ⟨Es, hEs⟩ := sep_of H (fun E => IsEnvOn H T E) (envOnF 0 1) (fun _ => T)
    (fun E => by rw [nsat_envOnF H]; rfl) P3
  refine ⟨Es, fun E => ?_⟩
  rw [hEs E]
  refine ⟨fun h => h.2, fun h => ⟨(hP3 E).2 fun p hp => ?_, h⟩⟩
  obtain ⟨n, y, hn, rfl⟩ := h.1.2.2 p hp
  have hy : mem y T := h.2 n y hp
  refine (hP2 _).2 fun q hq => (hP1 q).2 ?_
  rcases (kpair_mem H n y q).1 hq with rfl | rfl
  · intro z hz; rw [(vsingle_spec H n z).1 hz]; exact (vcup_spec H _ _ n).2 (Or.inl hn)
  · intro z hz
    rcases (vpair_spec H n y z).1 hz with rfl | rfl
    · exact (vcup_spec H _ _ _).2 (Or.inl hn)
    · exact (vcup_spec H _ _ _).2 (Or.inr hy)

end Envs

/-! ## Least witness stages -/

section Witness

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)

/-- Some `x ∈ L_c` satisfies `θ` in `L` at `x, E(0), E(1), …`. -/
def Wit (θ : Form) (E c : V) : Prop :=
  ∃ T x, IsL H hP c T ∧ mem x T ∧ CSat mem (InL H hP) (scons x (envVals H E)) θ

/-- `c` is the least such stage. -/
def LeastWit (θ : Form) (E c : V) : Prop :=
  Ord mem c ∧ Wit H hP θ E c ∧ ∀ c', Ord mem c' → Wit H hP θ E c' → c = c' ∨ mem c c'

/-- The named formula for `Wit` (names `c`, `E` below `10`; binders `10`, `11`, `50…`). -/
noncomputable def witF (θ : Form) (c E : Nat) : NForm :=
  .ex 10 (.ex 11 (.and (isStageF (defOp H hP) c 10) (.and (.mem 11 10)
    (envSatF (inLF H hP) θ 11 E 50))))

noncomputable def leastWitF (θ : Form) (c E : Nat) : NForm :=
  .and (ordF c) (.and (witF H hP θ c E)
    (.all 9 (.imp (.and (ordF 9) (witF H hP θ 9 E)) (.or (.eq c 9) (.mem c 9)))))

theorem nsat_witF (θ : Form) {c E : Nat} (hc : c < 10) (hE : E < 10) (ρ : Nat → V) {A : V}
    (hEnv : IsEnvOn H A (ρ E)) : NSat mem ρ (witF H hP θ c E) ↔ Wit H hP θ (ρ E) (ρ c) := by
  simp only [witF, NSat, nsat_isStageF H (defOp H hP)]
  refine exists_congr fun T => exists_congr fun x => ?_
  have hEnv' : IsEnvOn H A (upd (upd ρ 10 T) 11 x E) := by
    rwa [upd_other _ _ (by omega), upd_other _ _ (by omega)]
  rw [nsat_envSatF H (InL H hP) (inLF H hP) (nsat_inLF H hP) θ (by omega) (by omega) _ hEnv']
  simp (disch := omega) only [upd_same, upd_other]
  rfl

theorem nsat_leastWitF (θ : Form) {c E : Nat} (hc : c < 9) (hE : E < 9) (ρ : Nat → V) {A : V}
    (hEnv : IsEnvOn H A (ρ E)) :
    NSat mem ρ (leastWitF H hP θ c E) ↔ LeastWit H hP θ (ρ E) (ρ c) := by
  simp only [leastWitF, NSat, nsat_ordF]
  rw [nsat_witF H hP θ (by omega) (by omega) ρ hEnv]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun c' => ?_
  have hEnv' : IsEnvOn H A (upd ρ 9 c' E) := by rwa [upd_other _ _ (by omega)]
  rw [nsat_witF H hP θ (by omega) (by omega) _ hEnv']
  simp (disch := omega) only [upd_same, upd_other, and_imp]

include hR in
/-- The least witness stages over all environments on `T` form a set. -/
theorem wst_exists (θ : Form) (T : V) :
    ∃ W, ∀ z, mem z W ↔ ∃ E c, IsEnvOn H T E ∧ LeastWit H hP θ E c ∧ mem z c := by
  obtain ⟨Es, hEs⟩ := envs_exists H hP T
  obtain ⟨Cs, hCs⟩ := repl_of H (fun E c => IsEnvOn H T E ∧ LeastWit H hP θ E c)
    (.and (envOnF 1 2) (leastWitF H hP θ 0 1)) (fun _ => T)
    (fun E c => by
      simp only [NSat, nsat_envOnF H]
      simp (disch := omega) only [upd_same, upd_other]
      refine and_congr_right fun hE => ?_
      have hEnv : IsEnvOn H T (upd (upd (fun _ => T) 1 E) 0 c 1) := by
        simp (disch := omega) only [upd_same, upd_other]; exact hE
      rw [nsat_leastWitF H hP θ (c := 0) (E := 1) (by omega) (by omega) _ hEnv]
      simp (disch := omega) only [upd_same, upd_other])
    (fun E c1 c2 h1 h2 => ZFRank.least_unique H hR h1.2.1 h2.2.1 h1.2.2.2 h2.2.2.2 h1.2.2.1 h2.2.2.1) Es
  refine ⟨vunion H Cs, fun z => ?_⟩
  rw [vunion_spec H Cs z]
  constructor
  · rintro ⟨c, hzc, hc⟩
    obtain ⟨E, hE, hE', hl⟩ := (hCs c).1 hc
    exact ⟨E, c, hE', hl, hzc⟩
  · rintro ⟨E, c, hE, hl, hzc⟩
    exact ⟨c, hzc, (hCs c).2 ⟨E, (hEs E).2 hE, hE, hl⟩⟩

end Witness

/-! ## The closing step -/

section Step

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)

/-- `u = x ∪ ⋃ {least witness stages of the formulas of Θ over environments on `L_x`}`. -/
def USpec (Θ : List Form) (x u : V) : Prop :=
  ∀ z, mem z u ↔ (mem z x ∨ (Ord mem x ∧ ∃ θ ∈ Θ, ∃ T E c, IsL H hP x T ∧ IsEnvOn H T E ∧
    LeastWit H hP θ E c ∧ mem z c))

include hR in
theorem uspec_exists (Θ : List Form) (x : V) : ∃ u, USpec H hP Θ x u := by
  induction Θ with
  | nil => exact ⟨x, fun z => by simp⟩
  | cons θ Θ ih =>
      obtain ⟨u, hu⟩ := ih
      by_cases hx : Ord mem x
      · obtain ⟨T, hT⟩ := isL_exists H hR hP hx
        obtain ⟨W, hW⟩ := wst_exists H hR hP θ T
        refine ⟨vcup H u W, fun z => ?_⟩
        rw [vcup_spec H u W z, hu z, hW z]
        constructor
        · rintro ((h | ⟨-, θ', hθ', T', E, c, h⟩) | ⟨E, c, hE, hl, hz⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hx, θ', List.mem_cons_of_mem _ hθ', T', E, c, h⟩
          · exact Or.inr ⟨hx, θ, List.mem_cons_self .., T, E, c, hT, hE, hl, hz⟩
        · rintro (h | ⟨-, θ', hθ', T', E, c, hT', hE, hl, hz⟩)
          · exact Or.inl (Or.inl h)
          · rcases List.mem_cons.1 hθ' with rfl | hθ'
            · rw [isL_unique H hR hP hx hT' hT] at hE
              exact Or.inr ⟨E, c, hE, hl, hz⟩
            · exact Or.inl (Or.inr ⟨hx, θ', hθ', T', E, c, hT', hE, hl, hz⟩)
      · exact ⟨u, fun z => by rw [hu z]; simp [hx]⟩

omit hR in
theorem uspec_unique {Θ : List Form} {x u u' : V} (h : USpec H hP Θ x u) (h' : USpec H hP Θ x u') :
    u = u' :=
  H.ext _ _ fun z => (h z).trans (h' z).symm

/-- The disjunction over `Θ` in `USpec` (names: `z = 3`, `x = 1`, binders `4, 5, 6`). -/
noncomputable def wstDisj : List Form → NForm
  | [] => .bot
  | θ :: Θ => .or (.ex 4 (.ex 5 (.ex 6 (.and (isStageF (defOp H hP) 1 4) (.and (envOnF 5 4)
      (.and (leastWitF H hP θ 6 5) (.mem 3 6))))))) (wstDisj Θ)

theorem nsat_wstDisj (Θ : List Form) (ρ : Nat → V) :
    NSat mem ρ (wstDisj H hP Θ) ↔ ∃ θ ∈ Θ, ∃ T E c, IsL H hP (ρ 1) T ∧ IsEnvOn H T E ∧
      LeastWit H hP θ E c ∧ mem (ρ 3) c := by
  induction Θ with
  | nil => simp [wstDisj, NSat]
  | cons θ Θ ih =>
      simp only [wstDisj, NSat, ih, List.mem_cons, exists_eq_or_imp]
      refine or_congr ?_ Iff.rfl
      simp only [nsat_isStageF H (defOp H hP), nsat_envOnF H]
      refine exists_congr fun T => exists_congr fun E => exists_congr fun c => ?_
      simp (disch := omega) only [upd_same, upd_other]
      refine and_congr_right fun _ => and_congr_right fun hE => ?_
      have hEnv : IsEnvOn H T (upd (upd (upd ρ 4 T) 5 E) 6 c 5) := by
        simp (disch := omega) only [upd_same, upd_other]; exact hE
      rw [nsat_leastWitF H hP θ (c := 6) (E := 5) (by omega) (by omega) _ hEnv]
      simp (disch := omega) only [upd_same, upd_other]

/-- `u = U(x)` (names `u`, `x` = `2`, `1`). -/
noncomputable def uspecF (Θ : List Form) : NForm :=
  .all 3 ((NForm.mem 3 2).iff (.or (.mem 3 1) (.and (ordF 1) (wstDisj H hP Θ))))

theorem nsat_uspecF (Θ : List Form) (ρ : Nat → V) :
    NSat mem ρ (uspecF H hP Θ) ↔ USpec H hP Θ (ρ 1) (ρ 2) := by
  simp only [uspecF, NSat, nsat_iff, nsat_ordF, nsat_wstDisj H hP]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

/-- The closing step `G(x) = U(x) ∪ {U(x)}`. -/
noncomputable def Gstep (hR : Regular mem) (Θ : List Form) (x : V) : V :=
  vsucc H (uspec_exists H hR hP Θ x).choose

/-- The graph of `Gstep` (output name `0`, input name `1`). -/
noncomputable def gstepF (Θ : List Form) : NForm := .ex 2 (.and (uspecF H hP Θ) (succF 0 2))

theorem nsat_gstepF (Θ : List Form) (ρ : Nat → V) (x y : V) :
    NSat mem (upd (upd ρ 1 x) 0 y) (gstepF H hP Θ) ↔ y = Gstep H hP hR Θ x := by
  simp only [gstepF, NSat, nsat_uspecF H hP, nsat_succF H]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Gstep, uspec_unique H hP hu (uspec_exists H hR hP Θ x).choose_spec]
  · rintro rfl
    exact ⟨_, (uspec_exists H hR hP Θ x).choose_spec, rfl⟩

end Step

/-! ## Reflection -/

/-- The bodies of the quantified subformulas, and their negations. -/
def qbodies : Form → List Form
  | .fImp a b => qbodies a ++ qbodies b
  | .fAnd a b => qbodies a ++ qbodies b
  | .fOr a b => qbodies a ++ qbodies b
  | .fAll a => a :: .fImp a .fBot :: qbodies a
  | .fEx a => a :: .fImp a .fBot :: qbodies a
  | _ => []

section Reflect

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

/-- `β` is a limit ordinal containing every least witness stage, for the
formulas of `Θ`, of every environment on a stage below `β`. -/
def Closed (Θ : List Form) (β : V) : Prop :=
  Ord mem β ∧ (∀ γ, mem γ β → mem (vsucc H γ) β) ∧
    ∀ γ, mem γ β → ∀ T E c, ∀ θ ∈ Θ, IsL H hP γ T → IsEnvOn H T E → LeastWit H hP θ E c → mem c β

omit hR hP in
/-- An internal environment over `T` with prescribed first values. -/
theorem mk_env {T d : V} (hd : mem d T) :
    ∀ (m : Nat) (v : Nat → V), (∀ k, k < m → mem (v k) T) →
      ∃ E, IsEnvOn H T E ∧ ∀ k, k < m → envVals H E k = v k
  | 0, _, _ => ⟨_, constEnv_isEnvOn H hd, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | m + 1, v, hv => by
      obtain ⟨E, hE, hval⟩ := mk_env hd m (fun k => v (k + 1)) fun k hk => hv (k + 1) (by omega)
      refine ⟨econs H (v 0) E, econs_isEnvOn H hE (hv 0 (by omega)), fun k hk => ?_⟩
      rw [envVals_econs H hE (v 0) k]
      cases k with
      | zero => rfl
      | succ k => exact hval k (by omega)

/-- Finitely many members of `L_β` (β a limit) lie in one earlier stage. -/
theorem common_stage {β Tβ : V} (hβ : Ord mem β) (hlim : ∀ γ, mem γ β → mem (vsucc H γ) β)
    (hTβ : IsL H hP β Tβ) (v : Nat → V) :
    ∀ m, (∀ k, k < m + 1 → mem (v k) Tβ) →
      ∃ γ T, mem γ β ∧ IsL H hP γ T ∧ ∀ k, k < m + 1 → mem (v k) T := by
  -- one member lies in a successor stage below β
  have one : ∀ x, mem x Tβ → ∃ γ T, mem γ β ∧ IsL H hP γ T ∧ mem x T := by
    intro x hx
    obtain ⟨c, T, hc, hT, hxT⟩ := (isL_spec H hR hP hβ hTβ x).1 hx
    have hoc := ord_of_mem hβ hc
    obtain ⟨T', hT'⟩ := isL_exists H hR hP (ord_succ H hoc)
    exact ⟨_, T', hlim c hc, hT', (isL_spec H hR hP (ord_succ H hoc) hT' x).2
      ⟨c, T, vsucc_self H c, hT, hxT⟩⟩
  intro m
  induction m with
  | zero =>
      intro hv
      obtain ⟨γ, T, hγ, hT, hx⟩ := one (v 0) (hv 0 (by omega))
      exact ⟨γ, T, hγ, hT, fun k hk => by rwa [show k = 0 by omega]⟩
  | succ m ih =>
      intro hv
      obtain ⟨γ1, T1, hγ1, hT1, h1⟩ := ih fun k hk => hv k (by omega)
      obtain ⟨γ2, T2, hγ2, hT2, h2⟩ := one (v (m + 1)) (hv (m + 1) (by omega))
      have ho1 := ord_of_mem hβ hγ1
      have ho2 := ord_of_mem hβ hγ2
      rcases trichotomy H hR γ1 ho1 γ2 ho2 with h | rfl | h
      · exact ⟨γ2, T2, hγ2, hT2, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact isL_mono H hR hP ho2 h hT1 hT2 _ (h1 k hk)
          · exact h2⟩
      · exact ⟨γ1, T1, hγ1, hT1, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h1 k hk
          · rwa [isL_unique H hR hP ho1 hT2 hT1] at h2⟩
      · exact ⟨γ1, T1, hγ1, hT1, fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h1 k hk
          · exact isL_mono H hR hP ho1 h hT2 hT1 _ h2⟩

/-- **Witnesses reflect into a closed stage.** -/
theorem closure_witness {Θ : List Form} {β Tβ : V} (hC : Closed H hP Θ β) (hTβ : IsL H hP β Tβ)
    {θ : Form} (hθ : θ ∈ Θ) {e : Nat → V} (he : ∀ n, mem (e n) Tβ)
    (hw : ∃ d, InL H hP d ∧ CSat mem (InL H hP) (scons d e) θ) :
    ∃ x, mem x Tβ ∧ CSat mem (InL H hP) (scons x e) θ := by
  obtain ⟨hβ, hlim, hcl⟩ := hC
  obtain ⟨γ, T, hγ, hT, hvals⟩ := common_stage H hR hP hβ hlim hTβ e (bound θ) fun k _ => he k
  have hoγ := ord_of_mem hβ hγ
  obtain ⟨E, hE, hEv⟩ := mk_env H (hvals 0 (by omega)) (bound θ) e fun k hk => hvals k (by omega)
  -- the formula only sees the first values
  have agree : ∀ x, CSat mem (InL H hP) (scons x (envVals H E)) θ ↔
      CSat mem (InL H hP) (scons x e) θ := fun x =>
    csat_ext_free _ θ _ _ fun n hn => by
      cases n with
      | zero => rfl
      | succ k => exact hEv k (by have := free_lt_bound θ _ hn; omega)
  obtain ⟨d, hd, hdθ⟩ := hw
  obtain ⟨c0, S0, hc0, hS0, hdS0⟩ := hd
  obtain ⟨c, hc, hWc, hmin⟩ := least_ord H hR (Wit H hP θ E) (witF H hP θ 0 1) (upd (fun _ => E) 1 E)
    (fun c => by
      rw [nsat_witF H hP θ (by omega) (by omega) _ (A := T)
        (by simp (disch := omega) only [upd_same, upd_other]; exact hE)]
      simp (disch := omega) only [upd_same, upd_other]) hc0
    ⟨S0, d, hS0, hdS0, (agree d).2 hdθ⟩
  have hcβ := hcl γ hγ T E c θ hθ hT hE ⟨hc, hWc, hmin⟩
  obtain ⟨Tc, x, hTc, hxTc, hxθ⟩ := hWc
  exact ⟨x, isL_mono H hR hP hβ hcβ hTc hTβ x hxTc, (agree x).1 hxθ⟩

/-- **Reflection.** A closed stage reflects every formula whose quantifier
bodies are among `Θ`. -/
theorem reflect {Θ : List Form} {β Tβ : V} (hC : Closed H hP Θ β) (hTβ : IsL H hP β Tβ) :
    ∀ φ : Form, (∀ θ ∈ qbodies φ, θ ∈ Θ) → ∀ e : Nat → V, (∀ n, mem (e n) Tβ) →
      (CSat mem (InL H hP) e φ ↔ RSat mem Tβ e φ)
  | .fMem _ _, _, _, _ | .fEq _ _, _, _, _ | .fBot, _, _, _ => Iff.rfl
  | .fImp a b, hq, e, he | .fAnd a b, hq, e, he | .fOr a b, hq, e, he => by
      simp only [CSat, RSat]
      rw [reflect hC hTβ a (fun θ h => hq θ (List.mem_append_left _ h)) e he,
        reflect hC hTβ b (fun θ h => hq θ (List.mem_append_right _ h)) e he]
  | .fEx a, hq, e, he => by
      have hqa : ∀ θ ∈ qbodies a, θ ∈ Θ := fun θ h => hq θ (by simp [qbodies, h])
      have hext : ∀ x, mem x Tβ → ∀ n, mem (scons x e n) Tβ := fun x hx n => by
        cases n with
        | zero => exact hx
        | succ n => exact he n
      simp only [CSat, RSat]
      constructor
      · intro hw
        obtain ⟨x, hx, hxa⟩ := closure_witness H hR hP hC hTβ (hq a (by simp [qbodies])) he hw
        exact ⟨x, hx, (reflect hC hTβ a hqa _ (hext x hx)).1 hxa⟩
      · rintro ⟨x, hx, hxa⟩
        exact ⟨x, ⟨β, Tβ, hC.1, hTβ, hx⟩, (reflect hC hTβ a hqa _ (hext x hx)).2 hxa⟩
  | .fAll a, hq, e, he => by
      have hqa : ∀ θ ∈ qbodies a, θ ∈ Θ := fun θ h => hq θ (by simp [qbodies, h])
      have hext : ∀ x, mem x Tβ → ∀ n, mem (scons x e n) Tβ := fun x hx n => by
        cases n with
        | zero => exact hx
        | succ n => exact he n
      simp only [CSat, RSat]
      constructor
      · intro hall x hx
        exact (reflect hC hTβ a hqa _ (hext x hx)).1 (hall x ⟨β, Tβ, hC.1, hTβ, hx⟩)
      · intro hall d hd
        refine Classical.byContradiction fun hnd => ?_
        obtain ⟨x, hx, hxa⟩ := closure_witness H hR hP hC hTβ (θ := .fImp a .fBot)
          (hq _ (by simp [qbodies])) he ⟨d, hd, hnd⟩
        exact hxa ((reflect hC hTβ a hqa _ (hext x hx)).2 (hall x hx))

end Reflect

/-! ## Closed ordinals exist -/

section ClosedExists

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include H hR hP

omit hR in
theorem uspec_ord {Θ : List Form} {x u : V} (hx : Ord mem x) (hu : USpec H hP Θ x u) :
    Ord mem u ∧ Sub mem x u := by
  have hmemOrd : ∀ z, mem z u → Ord mem z := by
    intro z hz
    rcases (hu z).1 hz with h | ⟨-, θ, -, T, E, c, -, -, hc, hzc⟩
    · exact ord_of_mem hx h
    · exact ord_of_mem hc.1 hzc
  refine ⟨⟨fun z hz w hw => ?_, fun z hz => (hmemOrd z hz).1⟩, fun z hz => (hu z).2 (Or.inl hz)⟩
  rcases (hu z).1 hz with h | ⟨hxo, θ, hθ, T, E, c, hT, hE, hc, hzc⟩
  · exact (hu w).2 (Or.inl (hx.1 z h w hw))
  · exact (hu w).2 (Or.inr ⟨hxo, θ, hθ, T, E, c, hT, hE, hc, hc.1.1 z hzc w hw⟩)

theorem gstep_ord {Θ : List Form} {x : V} (hx : Ord mem x) :
    Ord mem (Gstep H hP hR Θ x) ∧ mem x (Gstep H hP hR Θ x) := by
  have hu := (uspec_exists H hR hP Θ x).choose_spec
  obtain ⟨huo, hxu⟩ := uspec_ord H hP hx hu
  exact ⟨ord_succ H huo, (vsucc_spec H _ x).2 (le_of_sub H hR hx huo hxu).symm⟩

theorem gstep_wit {Θ : List Form} {x T E c : V} (hx : Ord mem x) {θ : Form} (hθ : θ ∈ Θ)
    (hT : IsL H hP x T) (hE : IsEnvOn H T E) (hc : LeastWit H hP θ E c) :
    mem c (Gstep H hP hR Θ x) := by
  have hu := (uspec_exists H hR hP Θ x).choose_spec
  obtain ⟨huo, -⟩ := uspec_ord H hP hx hu
  have hcu := le_of_sub H hR hc.1 huo fun z hz => (hu z).2 (Or.inr ⟨hx, θ, hθ, T, E, c, hT, hE, hc, hz⟩)
  exact (vsucc_spec H _ c).2 hcu.symm

omit hR hP in
theorem isEnvOn_mono {T T' E : V} (hE : IsEnvOn H T E) (h : Sub mem T T') : IsEnvOn H T' E :=
  ⟨hE.1, fun n y hy => h y (hE.2 n y hy)⟩

/-- **Closed ordinals exist** above every ordinal. -/
theorem closed_exists (Θ : List Form) {a : V} (ha : Ord mem a) : ∃ β, mem a β ∧ Closed H hP Θ β := by
  obtain ⟨F, hF, h0, hs⟩ := ZFRank.iterate H (Gstep H hP hR Θ) (gstepF H hP Θ) (fun _ => vempty H)
    (fun x y => nsat_gstepF H hR hP Θ _ x y) (vsucc H a)
  obtain ⟨Rg, hRg⟩ := ZFRank.values H hF
  let Pn : V → Prop := fun n => ∀ y, mem (kpair H n y) F → Ord mem y
  have hP' : ∀ n, Sat mem (scons n (fun _ => F)) (toForm id (.all 2 (.imp (pmemF 1 0 2) (ordF 2)))) ↔
      Pn n := by
    intro n
    rw [sat_toForm]
    simp only [NSat, nsat_pmemF H, nsat_ordF]
    simp (disch := omega) only [upd_same, upd_other]
    rfl
  have hPall : ∀ n, mem n (omegaV H) → Pn n := by
    intro n hn
    refine (hP' n).1 (omega_ind H _ (fun _ => F) ((hP' _).2 ?_) (fun m hm ih => (hP' _).2 ?_) n hn)
    · intro y hy
      rw [← applyV_eq H hF.1 hy, h0]; exact ord_succ H ha
    · intro y hy
      rw [← applyV_eq H hF.1 hy, hs m hm]
      exact (gstep_ord H hR hP ((hP' m).1 ih _ (applyV_mem H (hF.2.1 m hm)))).1
  have hord : ∀ n, mem n (omegaV H) → Ord mem (applyV H F n) :=
    fun n hn => hPall n hn _ (applyV_mem H (hF.2.1 n hn))
  have hRgOrd : ∀ y, mem y Rg → Ord mem y := by
    intro y hy; obtain ⟨n, hn, rfl⟩ := (hRg y).1 hy; exact hord n hn
  have hβ := ord_vunion H hRgOrd
  have hmemRg : ∀ n, mem n (omegaV H) → mem (applyV H F n) Rg := fun n hn => (hRg _).2 ⟨n, hn, rfl⟩
  -- every member of β lies in some value, and the next value lies in β
  have hin : ∀ z, mem z (vunion H Rg) → ∃ n, mem n (omegaV H) ∧ mem z (applyV H F n) := by
    intro z hz
    obtain ⟨y, hzy, hyR⟩ := (vunion_spec H Rg z).1 hz
    obtain ⟨n, hn, rfl⟩ := (hRg y).1 hyR
    exact ⟨n, hn, hzy⟩
  have hnext : ∀ n, mem n (omegaV H) → ∀ z, mem z (Gstep H hP hR Θ (applyV H F n)) →
      mem z (vunion H Rg) := by
    intro n hn z hz
    refine (vunion_spec H Rg z).2 ⟨_, ?_, hmemRg _ (omega_succ H n hn)⟩
    rwa [hs n hn]
  refine ⟨vunion H Rg, (vunion_spec H Rg a).2 ⟨_, ?_, hmemRg _ (vempty_in_omega H)⟩, hβ, ?_, ?_⟩
  · rw [h0]; exact vsucc_self H a
  · intro γ hγ
    obtain ⟨n, hn, hγn⟩ := hin γ hγ
    have hFn := hord n hn
    have hsγ := ord_succ H (ord_of_mem hFn hγn)
    have hle := le_of_sub H hR hsγ hFn fun w hw => by
      rcases (vsucc_spec H γ w).1 hw with hw | rfl
      · exact hFn.1 γ hγn w hw
      · exact hγn
    obtain ⟨hGo, hFG⟩ := gstep_ord H hR hP (Θ := Θ) hFn
    refine hnext n hn _ ?_
    rcases hle with h | h
    · rwa [h]
    · exact hGo.1 _ hFG _ h
  · intro γ hγ T E c θ hθ hT hE hc
    obtain ⟨n, hn, hγn⟩ := hin γ hγ
    have hFn := hord n hn
    obtain ⟨Tn, hTn⟩ := isL_exists H hR hP hFn
    have hE' := isEnvOn_mono H hE (isL_mono H hR hP hFn hγn hT hTn)
    exact hnext n hn c (gstep_wit H hR hP hFn hθ hTn hE' hc)

end ClosedExists

end SetTheory.BusyBeaver.ZFC.ConstructibleReflect
