import BusyBeaver.ZFC.InternalRank
import BoundedZFCConsistency.OmegaRecursion

/-!
Ranks, Collection and power containers inside an arbitrary model of ZF.

From the hierarchy of `InternalRank`:

* transitive containers by recursion along the internal ω
  (`BoundedZFCConsistency.OmegaRecursion`), hence ∈-induction for
  properties defined by named formulas (`eps_induction`);
* the rank theorem `ranked`: every set lies in some `V_a`;
* **Collection** for every first-order matrix (`collection`): collect, for
  each input that has an output, the outputs of least rank, inside one
  `V_β`;
* power containers (`containers`): `V_λ` for a limit `λ` above the rank of the
  given set, with `λ` obtained by iterating the successor along ω.

These are exactly the CP and GIC resources of the native theory; see
`ZFNative`.
-/

namespace SetTheory.BusyBeaver.ZFC.ZFRank

open NamedZF NForm InternalOrd InternalRank LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

/-! ## Iteration along ω and its values -/

theorem iterate (H : ZFAxioms mem) (G : V → V) (φ : NForm) (ρ : Nat → V)
    (hG : ∀ x y, NSat mem (upd (upd ρ 1 x) 0 y) φ ↔ y = G x) (a : V) :
    ∃ F, IsFunctionOn H F (omegaV H) ∧ applyV H F (vempty H) = a ∧
      ∀ n, mem n (omegaV H) → applyV H F (vsucc H n) = G (applyV H F n) := by
  apply omega_recursion H (toForm id φ) (fun i => ρ (i + 2)) G
  intro y x
  simp only [relOf, sat_toForm, scons_shift2]
  exact hG x y

/-- The set of values of a function on a set. -/
theorem values (H : ZFAxioms mem) {F d : V} (hF : IsFunctionOn H F d) :
    ∃ Rg, ∀ y, mem y Rg ↔ ∃ n, mem n d ∧ applyV H F n = y := by
  obtain ⟨Rg, hRg⟩ := repl_of H (fun n y => mem (kpair H n y) F) (pmemF 2 1 0) (fun _ => F)
    (fun x y => by
      simp only [nsat_pmemF H]
      simp (disch := omega) only [upd_same, upd_other])
    (fun n y1 y2 h1 h2 => hF.1 n y1 y2 h1 h2) d
  exact ⟨Rg, fun y => by
    rw [hRg y]
    exact exists_congr fun n => and_congr_right fun hn => applyV_iff H hF hn y⟩

/-- `y = ⋃ x` (output name `0`, input name `1`). -/
def unionF : NForm := .all 2 ((NForm.mem 2 0).iff (.ex 3 (.and (.mem 2 3) (.mem 3 1))))

/-- Every set lies in a transitive set. -/
theorem trans_container (H : ZFAxioms mem) (x : V) : ∃ t, Trans mem t ∧ mem x t := by
  obtain ⟨F, hF, h0, hs⟩ := iterate H (vunion H) unionF (fun _ => x)
    (fun u y => by
      simp only [unionF, NSat, nsat_iff]
      simp (disch := omega) only [upd_same, upd_other]
      constructor
      · intro h; exact H.ext _ _ fun d => (h d).trans (vunion_spec H u d).symm
      · intro h d; rw [h]; exact vunion_spec H u d) (vsingle H x)
  obtain ⟨Rg, hRg⟩ := values H hF
  refine ⟨vunion H Rg, ?_, ?_⟩
  · intro y hy z hz
    obtain ⟨w, hyw, hwR⟩ := (vunion_spec H Rg y).1 hy
    obtain ⟨n, hn, rfl⟩ := (hRg w).1 hwR
    refine (vunion_spec H Rg z).2 ⟨applyV H F (vsucc H n), ?_, (hRg _).2 ⟨_, omega_succ H n hn, rfl⟩⟩
    rw [hs n hn]
    exact (vunion_spec H _ z).2 ⟨y, hz, hyw⟩
  · refine (vunion_spec H Rg x).2 ⟨applyV H F (vempty H), ?_, (hRg _).2 ⟨_, vempty_in_omega H, rfl⟩⟩
    rw [h0]; exact (vsingle_spec H x x).2 rfl

section Induction

variable (H : ZFAxioms mem) (hR : Regular mem)
include H hR

/-- **∈-induction** for a property defined by a named formula (name `0`). -/
theorem eps_induction (P : V → Prop) (φ : NForm) (ρ : Nat → V)
    (hP : ∀ x, NSat mem (upd ρ 0 x) φ ↔ P x) (step : ∀ x, (∀ z, mem z x → P z) → P x) :
    ∀ x, P x := fun x0 => Classical.byContradiction fun hn => by
  obtain ⟨t, ht, hx0⟩ := trans_container H x0
  obtain ⟨S, hS⟩ := sep_of H (fun x => ¬ P x) φ.neg ρ (fun x => by rw [nsat_neg, hP]) t
  obtain ⟨m, hm, hmin⟩ := hR S ⟨x0, (hS x0).2 ⟨hx0, hn⟩⟩
  obtain ⟨hmt, hPm⟩ := (hS m).1 hm
  exact hPm (step m fun z hz => Classical.byContradiction fun hnz =>
    hmin ⟨z, hz, (hS z).2 ⟨ht m hmt z hz, hnz⟩⟩)

/-- Least elements are unique. -/
theorem least_unique {P : V → Prop} {a b : V} (ha : Ord mem a) (hb : Ord mem b)
    (h1 : ∀ c, Ord mem c → P c → a = c ∨ mem a c) (h2 : ∀ c, Ord mem c → P c → b = c ∨ mem b c)
    (hPa : P a) (hPb : P b) : a = b :=
  (h1 b hb hPb).elim id fun h => (h2 a ha hPa).elim Eq.symm fun h' =>
    absurd (ha.1 b h' a h) (mem_irrefl H hR a)

variable (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include hP

/-- `V_a ⊆ V_b` for `a ≤ b`. -/
theorem isV_le {a b S T : V} (hb : Ord mem b) (hab : a = b ∨ mem a b) (hS : IsV H a S)
    (hT : IsV H b T) : Sub mem S T := by
  rcases hab with rfl | hab
  · rw [isV_unique H hR hb hS hT]; exact fun _ h => h
  · exact isV_mono H hR hP hb hab hS hT

/-- `x ∈ V_a` for some ordinal `a` (name `0` is `x`). -/
def rankedF : NForm := .ex 1 (.ex 2 (.and (ordF 1) (.and (isVF 1 2) (.mem 0 2))))

/-- **The rank theorem.** Every set lies in some `V_a`. -/
theorem ranked : ∀ x, ∃ a S, Ord mem a ∧ IsV H a S ∧ mem x S := by
  refine eps_induction H hR _ rankedF (fun _ => vempty H)
    (fun x => by
      simp only [rankedF, NSat, nsat_ordF, nsat_isVF H]
      simp (disch := omega) only [upd_same, upd_other]) ?_
  intro x IH
  -- the least rank of a member
  let L : V → V → Prop := fun z a => Ord mem a ∧ (∃ S, IsV H a S ∧ mem z S) ∧
    ∀ b, Ord mem b → (∃ S, IsV H b S ∧ mem z S) → a = b ∨ mem a b
  have hL : ∀ z, mem z x → ∃ a, L z a := by
    intro z hz
    obtain ⟨a, S, ha, hS, hzS⟩ := IH z hz
    exact least_ord H hR (fun a => ∃ S, IsV H a S ∧ mem z S)
      (.ex 1 (.and (isVF 0 1) (.mem 2 1))) (fun _ => z)
      (fun y => by
        simp only [NSat, nsat_isVF H]
        simp (disch := omega) only [upd_same, upd_other]) ha ⟨S, hS, hzS⟩
  obtain ⟨A, hA⟩ := repl_of H L
    (.and (ordF 0) (.and (.ex 2 (.and (isVF 0 2) (.mem 1 2)))
      (.all 3 (.imp (.and (ordF 3) (.ex 4 (.and (isVF 3 4) (.mem 1 4)))) (.or (.eq 0 3) (.mem 0 3))))))
    (fun _ => x)
    (fun z a => by
      simp only [NSat, nsat_ordF, nsat_isVF H, and_imp]
      simp (disch := omega) only [upd_same, upd_other]
      simp only [L])
    (fun z a1 a2 h1 h2 => least_unique H hR h1.1 h2.1 h1.2.2 h2.2.2 h1.2.1 h2.2.1) x
  have hAord : ∀ a, mem a A → Ord mem a := by
    intro a ha; obtain ⟨_, _, h⟩ := (hA a).1 ha; exact h.1
  have hβ := ord_vunion H hAord
  obtain ⟨Sβ, hSβ⟩ := isV_exists H hR hP hβ
  have hsub : Sub mem x Sβ := by
    intro z hz
    obtain ⟨a, haz⟩ := hL z hz
    obtain ⟨S, hS, hzS⟩ := haz.2.1
    have haA : mem a A := (hA a).2 ⟨z, hz, haz⟩
    have hle := le_of_sub H hR haz.1 hβ fun w hw => (vunion_spec H A w).2 ⟨a, hw, haA⟩
    exact isV_le H hR hP hβ hle hS hSβ z hzS
  obtain ⟨S', hS'⟩ := isV_exists H hR hP (ord_succ H hβ)
  exact ⟨_, S', ord_succ H hβ, hS', (isV_spec H hR hP (ord_succ H hβ) hS' x).2
    ⟨_, Sβ, vsucc_self H _, hSβ, hsub⟩⟩

/-! ## Collection -/

/-- The matrix with input slot read at name `x`, output slot at name `y`,
and parameter slot `k + 2` at name `100 + k`. -/
def margs (x y : Nat) : Nat → Nat
  | 0 => x
  | 1 => y
  | k + 2 => 100 + k

/-- The matrix parameters sit at names `100 + k`. -/
def Params (env ρ : Nat → V) : Prop := ∀ k, ρ (100 + k) = env k

omit H hR hP in
theorem params_upd {env ρ : Nat → V} (h : Params env ρ) {x : Nat} (hx : x < 100) (d : V) :
    Params env (upd ρ x d) := fun k => by rw [upd_other _ _ (by omega)]; exact h k

omit H hR hP in
theorem sat_margs {env ρ : Nat → V} (h : Params env ρ) (phi : Form) (x y : Nat) :
    Sat mem (fun i => ρ (margs x y i)) phi ↔ Sat mem (scons (ρ x) (scons (ρ y) env)) phi :=
  Sat_ext phi _ _ fun i => by rcases i with _ | _ | k <;> first | rfl | exact h k

/-- `∃ S y, S = V_a ∧ y ∈ S ∧ matrix(x, y)`. -/
def witF (phi : Form) (a x : Nat) : NForm :=
  .ex (a + x + 1) (.ex (a + x + 2) (.and (isVF a (a + x + 1))
    (.and (.mem (a + x + 2) (a + x + 1)) (.atom phi (margs x (a + x + 2))))))

omit hR hP in
theorem nsat_witF {env ρ : Nat → V} (h : Params env ρ) (phi : Form) (a x : Nat)
    (hax : a + x + 2 < 100) :
    NSat mem ρ (witF phi a x) ↔
      ∃ S y, IsV H (ρ a) S ∧ mem y S ∧ Sat mem (scons (ρ x) (scons y env)) phi := by
  simp only [witF, NSat]
  refine exists_congr fun S => exists_congr fun y => ?_
  rw [nsat_isVF H, sat_margs (params_upd (params_upd h (by omega) S) (by omega) y)]
  simp (disch := omega) only [upd_same, upd_other]

/-- Discharge `Params` side conditions along `upd` chains. -/
macro "params_tac" : tactic =>
  `(tactic| repeat (first | assumption | omega | apply params_upd))

/-- **Collection** for every first-order matrix: for each input in `a` that
has an output, `b` contains one, and every member of `b` is an output. -/
theorem collection (phi : Form) (env : Nat → V) (a : V) :
    ∃ b, (∀ y, mem y b → ∃ x, Sat mem (scons x (scons y env)) phi) ∧
      ∀ x, mem x a → (∃ y, Sat mem (scons x (scons y env)) phi) →
        ∃ y, mem y b ∧ Sat mem (scons x (scons y env)) phi := by
  let base : Nat → V := fun i => env (i - 100)
  have hb : Params env base := fun k => by simp [base]
  -- the inputs that have an output
  obtain ⟨D, hD⟩ := sep_of H (fun x => ∃ y, Sat mem (scons x (scons y env)) phi)
    (.ex 1 (.atom phi (margs 0 1))) base
    (fun x => by
      simp only [NSat]
      refine exists_congr fun y => ?_
      rw [sat_margs (params_upd (params_upd hb (by omega) x) (by omega) y)]
      simp (disch := omega) only [upd_same, upd_other]) a
  let W : V → V → Prop := fun x c => ∃ S y, IsV H c S ∧ mem y S ∧ Sat mem (scons x (scons y env)) phi
  let L : V → V → Prop := fun x c => Ord mem c ∧ W x c ∧ ∀ e, Ord mem e → W x e → c = e ∨ mem c e
  -- the least rank of an output, as a set over `D`
  obtain ⟨A, hA⟩ := repl_of H L
    (.and (ordF 0) (.and (witF phi 0 1)
      (.all 4 (.imp (.and (ordF 4) (witF phi 4 1)) (.or (.eq 0 4) (.mem 0 4)))))) base
    (fun x c => by
      have h1 : Params env (upd (upd base 1 x) 0 c) := by params_tac
      simp only [NSat, nsat_ordF, nsat_witF H h1 phi 0 1 (by omega)]
      simp (disch := omega) only [upd_same, upd_other]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun e => ?_
      have h2 : Params env (upd (upd (upd base 1 x) 0 c) 4 e) := by params_tac
      rw [nsat_witF H h2 phi 4 1 (by omega)]
      simp (disch := omega) only [upd_same, upd_other, and_imp]
      exact Iff.rfl)
    (fun x c1 c2 h1 h2 => least_unique H hR h1.1 h2.1 h1.2.2 h2.2.2 h1.2.1 h2.2.1) D
  have hAord : ∀ c, mem c A → Ord mem c := by
    intro c hc; obtain ⟨_, _, h⟩ := (hA c).1 hc; exact h.1
  have hβ := ord_vunion H hAord
  obtain ⟨Sβ, hSβ⟩ := isV_exists H hR hP hβ
  -- the outputs inside `V_β`
  obtain ⟨b, hbs⟩ := sep_of H (fun y => ∃ x, mem x a ∧ Sat mem (scons x (scons y env)) phi)
    (.ex 1 (.and (.mem 1 2) (.atom phi (margs 1 0)))) (upd base 2 a)
    (fun y => by
      simp only [NSat]
      refine exists_congr fun x => ?_
      rw [sat_margs (params_upd (params_upd (params_upd hb (by omega) a) (by omega) y) (by omega) x)]
      simp (disch := omega) only [upd_same, upd_other]) Sβ
  refine ⟨b, fun y hy => ?_, fun x hx hxy => ?_⟩
  · obtain ⟨-, x, -, h⟩ := (hbs y).1 hy; exact ⟨x, h⟩
  · have hxD : mem x D := (hD x).2 ⟨hx, hxy⟩
    obtain ⟨y0, hy0⟩ := hxy
    obtain ⟨c0, S0, hc0, hS0, hy0S⟩ := ranked H hR hP y0
    obtain ⟨c, hc, hWc, hmin⟩ := least_ord H hR (W x)
      (witF phi 0 1) (upd base 1 x)
      (fun c => by
        have h1 : Params env (upd (upd base 1 x) 0 c) := by params_tac
        rw [nsat_witF H h1 phi 0 1 (by omega)]
        simp (disch := omega) only [upd_same, upd_other]
        exact Iff.rfl) hc0 ⟨S0, y0, hS0, hy0S, hy0⟩
    have hcA : mem c A := (hA c).2 ⟨x, hxD, hc, hWc, hmin⟩
    obtain ⟨S, y, hS, hyS, hxy'⟩ := hWc
    have hle := le_of_sub H hR hc hβ fun w hw => (vunion_spec H A w).2 ⟨c, hw, hcA⟩
    exact ⟨y, (hbs y).2 ⟨isV_le H hR hP hβ hle hS hSβ y hyS, x, hx, hxy'⟩, hxy'⟩

/-! ## Power containers -/

omit hP in
/-- Iterating the successor from `a` along ω reaches a limit ordinal above `a`. -/
theorem limit_above {a : V} (ha : Ord mem a) :
    ∃ l, Ord mem l ∧ mem a l ∧ ∀ c, mem c l → mem (vsucc H c) l := by
  obtain ⟨F, hF, h0, hs⟩ := iterate H (vsucc H) (succF 0 1) (fun _ => a)
    (fun x y => by rw [nsat_succF H]; simp (disch := omega) only [upd_same, upd_other]) a
  obtain ⟨Rg, hRg⟩ := values H hF
  -- every value is an ordinal, by induction along ω on the pair formula
  let P : V → Prop := fun n => ∀ y, mem (kpair H n y) F → Ord mem y
  have hP' : ∀ n, Sat mem (scons n (fun _ => F)) (toForm id (.all 2 (.imp (pmemF 1 0 2) (ordF 2)))) ↔ P n := by
    intro n
    rw [sat_toForm]
    simp only [NSat, nsat_pmemF H, nsat_ordF]
    simp (disch := omega) only [upd_same, upd_other]
    rfl
  have hPall : ∀ n, mem n (omegaV H) → P n := by
    intro n hn
    refine (hP' n).1 (omega_ind H _ (fun _ => F) ((hP' _).2 ?_) (fun m hm ih => (hP' _).2 ?_) n hn)
    · intro y hy
      rw [← applyV_eq H hF.1 hy, h0]; exact ha
    · intro y hy
      have ih' := (hP' m).1 ih
      rw [← applyV_eq H hF.1 hy, hs m hm]
      exact ord_succ H (ih' _ (applyV_mem H (hF.2.1 m hm)))
  have hord : ∀ n, mem n (omegaV H) → Ord mem (applyV H F n) :=
    fun n hn => hPall n hn _ (applyV_mem H (hF.2.1 n hn))
  have hRgOrd : ∀ y, mem y Rg → Ord mem y := by
    intro y hy; obtain ⟨n, hn, rfl⟩ := (hRg y).1 hy; exact hord n hn
  have hl := ord_vunion H hRgOrd
  have hmemRg : ∀ n, mem n (omegaV H) → mem (applyV H F n) Rg := fun n hn => (hRg _).2 ⟨n, hn, rfl⟩
  refine ⟨vunion H Rg, hl, ?_, ?_⟩
  · -- `a ∈ F 1 = a ∪ {a}`
    have h1 := omega_succ H _ (vempty_in_omega H)
    refine (vunion_spec H Rg a).2 ⟨_, ?_, hmemRg _ h1⟩
    rw [hs _ (vempty_in_omega H), h0]; exact vsucc_self H a
  · intro c hc
    obtain ⟨y, hcy, hyR⟩ := (vunion_spec H Rg c).1 hc
    obtain ⟨n, hn, rfl⟩ := (hRg y).1 hyR
    have hFn := hord n hn
    have hsc := ord_succ H (ord_of_mem hFn hcy)
    have hle := le_of_sub H hR hsc hFn fun w hw => by
      rcases (vsucc_spec H c w).1 hw with hw | rfl
      · exact hFn.1 c hcy w hw
      · exact hcy
    refine (vunion_spec H Rg _).2 ⟨_, ?_, hmemRg _ (omega_succ H n hn)⟩
    rw [hs n hn]
    exact (vsucc_spec H _ _).2 (hle.elim (fun e => Or.inr e) Or.inl)

/-- **Power containers.** Every set lies in a transitive set containing, for each
member, a set of all its subsets. -/
theorem containers : ∀ a, ∃ v, mem a v ∧ Trans mem v ∧
    ∀ x, mem x v → ∃ p, mem p v ∧ ∀ z, Sub mem z x → mem z p := by
  intro a
  obtain ⟨c, S, hc, hS, haS⟩ := ranked H hR hP a
  obtain ⟨l, hl, hcl, hlim⟩ := limit_above H hR hc
  obtain ⟨v, hv⟩ := isV_exists H hR hP hl
  refine ⟨v, isV_mono H hR hP hl hcl hS hv a haS, isV_trans H hR hP hl hv, fun x hx => ?_⟩
  obtain ⟨c', T, hc', hT, hxT⟩ := (isV_spec H hR hP hl hv x).1 hx
  have hoc' := ord_of_mem hl hc'
  obtain ⟨p, hp⟩ := isV_exists H hR hP (ord_succ H hoc')
  refine ⟨p, (isV_spec H hR hP hl hv p).2 ⟨_, p, hlim c' hc', hp, fun _ h => h⟩, fun z hz => ?_⟩
  exact (isV_spec H hR hP (ord_succ H hoc') hp z).2
    ⟨c', T, vsucc_self H c', hT, fun w hw => hxT w (hz w hw)⟩

end Induction

end SetTheory.BusyBeaver.ZFC.ZFRank
