import BusyBeaver.ZFC.ConstructibleZF

/-!
Uniform finite support of internal satisfaction.

`SatIn H A R c e` reads an internal environment `e`, a function on the
internal `ω`. For a standard code only the finitely many variables of the
formula matter, but a model may contain nonstandard codes, and the
definable well-order of `L` (Choice in `L`) needs the statement for every
internal code: **each internal code `c` has an internal natural `n` such that
`SatIn` at `c` is unchanged by any change of the environment at indices
`≥ n`** (`sat_support`).

The proof is internal induction on codes (`isFormCodeSem_ind'`) for a
property written as a named formula (`supF`). Atoms take the successor of
the larger index, connectives the larger bound, and a quantifier keeps the
bound of its body: two environments that agree below `n` still agree below
`n` after the shift `econs d`, since index `k + 1 < n` reads index `k < n`.
-/

namespace SetTheory.BusyBeaver.ZFC.SatSupport

open NamedZF NForm InternalRank ConstructibleDef LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- `x ∈ ω`. -/
def inOmegaF (x : Nat) : NForm := .atom (fNatF 0) (argsOf [x])

theorem nsat_inOmegaF (H : ZFAxioms mem) (ρ : Nat → V) (x : Nat) :
    NSat mem ρ (inOmegaF x) ↔ mem (ρ x) (omegaV H) := by
  simp only [inOmegaF, NSat]; rw [fNatF_spec H]; rfl

/-- The graphs `e` and `e'` agree at every index in `n`. -/
def AgreeP (H : ZFAxioms mem) (n e e' : V) : Prop :=
  ∀ i u u', mem i n → mem (kpair H i u) e → mem (kpair H i u') e' → u = u'

def agreeF (n e e' : Nat) : NForm :=
  let k := n + e + e' + 1
  .all k (.all (k + 1) (.all (k + 2) (.imp (.mem k n) (.imp (pmemF e k (k + 1))
    (.imp (pmemF e' k (k + 2)) (.eq (k + 1) (k + 2)))))))

theorem nsat_agreeF (H : ZFAxioms mem) (ρ : Nat → V) (n e e' : Nat) :
    NSat mem ρ (agreeF n e e') ↔ AgreeP H (ρ n) (ρ e) (ρ e') := by
  simp only [agreeF, NSat, nsat_pmemF H]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

/-- For environments and `n ∈ ω`, agreement of graphs is agreement of values. -/
theorem agreeP_iff (H : ZFAxioms mem) {A n e e' : V} (hn : mem n (omegaV H))
    (he : IsEnvOn H A e) (he' : IsEnvOn H A e') :
    AgreeP H n e e' ↔ ∀ i, mem i n → applyV H e i = applyV H e' i := by
  have hω : ∀ i, mem i n → mem i (omegaV H) := ConstructibleZF.omega_trans H n hn
  constructor
  · intro h i hi
    exact h i _ _ hi (applyV_mem H (he.1.2.1 i (hω i hi))) (applyV_mem H (he'.1.2.1 i (hω i hi)))
  · intro h i u u' hi hu hu'
    rw [← applyV_eq H he.1.1 hu, ← applyV_eq H he'.1.1 hu']
    exact h i hi

/-- `n` bounds the variables that `SatIn` reads at `c`. -/
def Supported (H : ZFAxioms mem) (A R c n : V) : Prop :=
  ∀ e e', IsEnvOn H A e → IsEnvOn H A e' → AgreeP H n e e' →
    (SatIn H A R c e ↔ SatIn H A R c e')

/-- The induction property (names: `0` the code, `1` the carrier, `2` the relation). -/
def supF : NForm :=
  .and (isCodeF 0) (.ex 3 (.and (inOmegaF 3) (.all 4 (.all 5 (.imp (envOnF 4 1)
    (.imp (envOnF 5 1) (.imp (agreeF 3 4 5) ((satInF 1 2 0 4).iff (satInF 1 2 0 5)))))))))

theorem nsat_supF (H : ZFAxioms mem) (ρ : Nat → V) :
    NSat mem ρ supF ↔ IsFormCodeSem H (ρ 0) ∧
      ∃ n, mem n (omegaV H) ∧ Supported H (ρ 1) (ρ 2) (ρ 0) n := by
  simp only [supF, NSat, nsat_isCodeF H, nsat_inOmegaF H, nsat_envOnF H, nsat_agreeF H,
    nsat_satInF H, nsat_iff]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

section Support

variable (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
include hS

omit hS in
/-- Two naturals lie below or at a common natural. -/
theorem nat_upper {i j : V} (hi : mem i (omegaV H)) (hj : mem j (omegaV H)) :
    ∃ m, mem m (omegaV H) ∧ (mem i m ∨ i = m) ∧ (mem j m ∨ j = m) := by
  rcases nat_linear H i hi j hj with h | rfl | h
  · exact ⟨j, hj, Or.inl h, Or.inr rfl⟩
  · exact ⟨i, hi, Or.inr rfl, Or.inr rfl⟩
  · exact ⟨i, hi, Or.inr rfl, Or.inl h⟩

omit hS in
theorem agreeP_mono {n m e e' : V} (hm : mem m (omegaV H)) (hnm : mem n m ∨ n = m)
    (h : AgreeP H m e e') : AgreeP H n e e' := by
  intro i u u' hi hu hu'
  refine h i u u' ?_ hu hu'
  rcases hnm with hnm | rfl
  · exact nat_transitive H m hm n hnm i hi
  · exact hi

theorem supported_atom {t : Nat} (ht : t = 0 ∨ t = 1) {i j : V} (hi : mem i (omegaV H))
    (hj : mem j (omegaV H)) :
    ∃ n, mem n (omegaV H) ∧ Supported H A R (kpair H (natV H t) (kpair H i j)) n := by
  obtain ⟨m, hm, him, hjm⟩ := nat_upper H hi hj
  refine ⟨vsucc H m, omega_succ H m hm, fun e e' he he' hag => ?_⟩
  have hag' := (agreeP_iff H (omega_succ H m hm) he he').1 hag
  have ei : applyV H e i = applyV H e' i := hag' i ((vsucc_spec H m i).2 him)
  have ej : applyV H e j = applyV H e' j := hag' j ((vsucc_spec H m j).2 hjm)
  rcases ht with rfl | rfl
  · rw [satIn_memAtom H hS hi hj he, satIn_memAtom H hS hi hj he', ei, ej]
  · rw [satIn_eqAtom H hS hi hj he, satIn_eqAtom H hS hi hj he', ei, ej]

omit hS in
/-- The bound of a binary connective is the larger of the two bounds. -/
theorem supported_two {a b na nb c : V} (hna : mem na (omegaV H)) (hnb : mem nb (omegaV H))
    (ha : Supported H A R a na) (hb : Supported H A R b nb)
    (op : Prop → Prop → Prop)
    (hc : ∀ e, IsEnvOn H A e → (SatIn H A R c e ↔ op (SatIn H A R a e) (SatIn H A R b e))) :
    ∃ n, mem n (omegaV H) ∧ Supported H A R c n := by
  obtain ⟨m, hm, ham, hbm⟩ := nat_upper H hna hnb
  refine ⟨m, hm, fun e e' he he' hag => ?_⟩
  rw [hc e he, hc e' he', ha e e' he he' (agreeP_mono H hm ham hag),
    hb e e' he he' (agreeP_mono H hm hbm hag)]

omit hS in
/-- Agreement below `n` survives the shift by a common value. -/
theorem agreeP_econs {n e e' d : V} (hn : mem n (omegaV H)) (he : IsEnvOn H A e)
    (he' : IsEnvOn H A e') (hd : mem d A) (h : AgreeP H n e e') :
    AgreeP H n (econs H d e) (econs H d e') := by
  have hag := (agreeP_iff H hn he he').1 h
  refine (agreeP_iff H hn (econs_isEnvOn H he hd) (econs_isEnvOn H he' hd)).2 fun i hi => ?_
  rcases nat_zero_or_succ H i (ConstructibleZF.omega_trans H n hn i hi) with rfl | ⟨k, hk, rfl⟩
  · rw [econs_zero H he.1.1, econs_zero H he'.1.1]
  · rw [econs_succ H he d hk, econs_succ H he' d hk]
    exact hag k (nat_transitive H n hn _ hi k (vsucc_self H k))

omit hS in
theorem supported_quant {a na c : V} (hna : mem na (omegaV H)) (ha : Supported H A R a na)
    (all : Bool)
    (hc : ∀ e, IsEnvOn H A e → (SatIn H A R c e ↔
      if all then ∀ d, mem d A → SatIn H A R a (econs H d e)
      else ∃ d, mem d A ∧ SatIn H A R a (econs H d e))) :
    Supported H A R c na := by
  intro e e' he he' hag
  rw [hc e he, hc e' he']
  have key : ∀ d, mem d A → (SatIn H A R a (econs H d e) ↔ SatIn H A R a (econs H d e')) :=
    fun d hd => ha _ _ (econs_isEnvOn H he hd) (econs_isEnvOn H he' hd)
      (agreeP_econs H hna he he' hd hag)
  cases all
  · exact exists_congr fun d => and_congr_right fun hd => key d hd
  · exact forall_congr' fun d => imp_congr_right fun hd => key d hd

/-- **Uniform finite support.** Every internal code, standard or not, has an
internal natural bounding the environment indices that satisfaction reads. -/
theorem sat_support :
    ∀ c, IsFormCodeSem H c → ∃ n, mem n (omegaV H) ∧ Supported H A R c n := by
  have key := isFormCodeSem_ind' H
    (fun c => IsFormCodeSem H c ∧ ∃ n, mem n (omegaV H) ∧ Supported H A R c n)
    (toForm id supF) (scons A (scons R (fun _ => A)))
    (fun y => by rw [sat_toForm, nsat_supF H]; rfl)
    (fun a b ha hb => ⟨isFormCodeSem_memAtom H ha hb, supported_atom H hS (Or.inl rfl) ha hb⟩)
    (fun a b ha hb => ⟨isFormCodeSem_eqAtom H ha hb, supported_atom H hS (Or.inr rfl) ha hb⟩)
    ⟨isFormCodeSem_bot H, vempty H, vempty_in_omega H, fun e e' _ _ _ =>
      ⟨fun h => absurd h (satIn_bot H), fun h => absurd h (satIn_bot H)⟩⟩
    (fun a b ⟨ca, na, hna, ha⟩ ⟨cb, nb, hnb, hb⟩ => ⟨isFormCodeSem_imp H ca cb,
      supported_two H hna hnb ha hb (fun p q => p → q) fun e he => satIn_imp H hS ca cb he⟩)
    (fun a b ⟨ca, na, hna, ha⟩ ⟨cb, nb, hnb, hb⟩ => ⟨isFormCodeSem_and H ca cb,
      supported_two H hna hnb ha hb And fun e he => satIn_and H hS ca cb he⟩)
    (fun a b ⟨ca, na, hna, ha⟩ ⟨cb, nb, hnb, hb⟩ => ⟨isFormCodeSem_or H ca cb,
      supported_two H hna hnb ha hb Or fun e he => satIn_or H hS ca cb he⟩)
    (fun a ⟨ca, na, hna, ha⟩ => ⟨isFormCodeSem_all H ca, na, hna,
      supported_quant H hna ha true fun e he => satIn_all H hS ca he⟩)
    (fun a ⟨ca, na, hna, ha⟩ => ⟨isFormCodeSem_ex H ca, na, hna,
      supported_quant H hna ha false fun e he => satIn_ex H hS ca he⟩)
  exact fun c hc => (key c hc).2

/-- Value form: `SatIn` at an internal code depends only on finitely many
environment values. -/
theorem sat_support_apply {c : V} (hc : IsFormCodeSem H c) :
    ∃ n, mem n (omegaV H) ∧ ∀ e e', IsEnvOn H A e → IsEnvOn H A e' →
      (∀ i, mem i n → applyV H e i = applyV H e' i) →
      (SatIn H A R c e ↔ SatIn H A R c e') := by
  obtain ⟨n, hn, hsup⟩ := sat_support H hS c hc
  exact ⟨n, hn, fun e e' he he' h => hsup e e' he he' ((agreeP_iff H hn he he').2 h)⟩

end Support

end SetTheory.BusyBeaver.ZFC.SatSupport
