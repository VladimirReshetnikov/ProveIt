import BusyBeaver.ZFC.Constructible

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
  | .fMem i j, e1, e2, h => by
      simp only [CSat]; rw [h i (Or.inl rfl), h j (Or.inr rfl)]
  | .fEq i j, e1, e2, h => by
      simp only [CSat]; rw [h i (Or.inl rfl), h j (Or.inr rfl)]
  | .fBot, _, _, _ => Iff.rfl
  | .fImp a b, e1, e2, h => by
      simp only [CSat]
      rw [csat_ext_free P a e1 e2 fun n hn => h n (Or.inl hn),
        csat_ext_free P b e1 e2 fun n hn => h n (Or.inr hn)]
  | .fAnd a b, e1, e2, h => by
      simp only [CSat]
      rw [csat_ext_free P a e1 e2 fun n hn => h n (Or.inl hn),
        csat_ext_free P b e1 e2 fun n hn => h n (Or.inr hn)]
  | .fOr a b, e1, e2, h => by
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
  | .fMem _ _, _, _, _, _ => Iff.rfl
  | .fEq _ _, _, _, _, _ => Iff.rfl
  | .fBot, _, _, _, _ => Iff.rfl
  | .fImp a b, s, f, ρ, hs => by
      simp only [relT, NSat, CSat, nsat_relT P C hC a s f ρ hs, nsat_relT P C hC b s f ρ hs]
  | .fAnd a b, s, f, ρ, hs => by
      simp only [relT, NSat, CSat, nsat_relT P C hC a s f ρ hs, nsat_relT P C hC b s f ρ hs]
  | .fOr a b, s, f, ρ, hs => by
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
      have hEnv' : ∀ v, IsEnvOn H A (upd ρ (b + k) v E) := fun v => by rw [hE' v]; exact hEnv
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

end SetTheory.BusyBeaver.ZFC.ConstructibleReflect
