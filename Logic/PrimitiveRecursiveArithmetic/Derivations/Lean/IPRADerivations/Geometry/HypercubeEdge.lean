import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Combinatorics.IndependentSets
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Combinatorics.BinomialTwo

/-!
# The hypercube edge inequality

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15` (`thm:cube-edge`): for every set `S` of
vertices of the cube `Q_d = {0,1}^d`,

  `2^{2e(S)} ≤ |S|^{|S|}`,

with `e(S)` the number of cube edges inside `S`. Vertices are the numbers `v < 2^d` (coordinate `i`
is bit `i`), and `S` is given by an arbitrary body: `v ∈ S` iff `χ(v, x) ≠ 0`. The induction of
the packet splits `S` along the lowest coordinate. To keep it inside quantifier-free induction the
statement is generalized to the sets `S_{m,r} = {v < 2^d : χ(m v + r, x) ≠ 0}`, whose two sections
are `S_{2m, r}` and `S_{2m, m+r}`:

* `bit_succ`: `bit_{i+1}(2w + ε) = bit_i(w)`;
* `k_split`, `E_split`: `|S_{m,r}| = |S_{2m,r}| + |S_{2m,m+r}|` and
  `e(S_{m,r}) = e(S_{2m,r}) + e(S_{2m,m+r}) + c` with `c = #{w : 2w, 2w + 1 ∈ S_{m,r}}`, which is at
  most either section size;
* `P_succ`: the induction step, from `Geometry/HypercubeSplit.edge_step`;
* `cube_edge`: induction on `d` for `m = 2^{D−d}` and all `r < 2^{D−d}` at once (a violation
  count), which at `d = D` is the theorem.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.HypercubeEdge

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev)
open LeanProofs.IPRA.Combinatorics.IndependentSets (inst2_sub pairB inst2_pair sum_pairs pw_two_succ)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (fM fX fY)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrSg zo_sg)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bits -/

/-- Bit `i` of `v`. -/
abbrev bit {n : ℕ} (i v : PTm n) : PTm n := par (quo v (pw two i))

theorem two_pw_pos (i : PTm n) : Γ ⊢[PRAAx] pw two i ≐ succ (pred (pw two i)) := pw_pos one i

/-- `bit_{i+1}(2w + ε) = bit_i(w)` for `ε ≤ 1`. -/
theorem bit_succ {i w e : PTm n} (he : Γ ⊢[PRAAx] le e one) : Γ ⊢[PRAAx] bit (succ i) (two * w + e) ≐ bit i w := by
  have hP := two_pw_pos (Γ := Γ) i
  have hP' := two_pw_pos (Γ := Γ) (succ i)
  have hr := rem_lt' hP w
  have q : Γ ⊢[PRAAx] quo (two * w + e) (pw two (succ i)) ≐ quo w (pw two i) := by
    refine quo_eq hP' (r := two * rem w (pw two i) + e) ?_ ?_
    · ipra_lc 2 * natEq (div_eq (j := w) hP) - 𝔞 (quo w (pw two i)) * natEq (pw_succ (Γ := Γ) two i)
    · have w₁ := natEq (eq_add_of_le hr); have w₂ := natEq (eq_add_of_le he)
      refine le_of_eq_add (d := two * monus (pw two i) (succ (rem w (pw two i))) + monus one e) ?_
      ipra_lc natEq (pw_succ (Γ := Γ) two i) + 2 * w₁ + w₂
  exact congrAp1 parF q

theorem bit_zero (v : PTm n) : Γ ⊢[PRAAx] bit zero v ≐ par v := by
  have h1 := two_pw_pos (Γ := Γ) (zero : PTm n)
  refine congrAp1 parF (quo_eq h1 (r := zero) ?_ ?_)
  · ipra_lc -𝔞 v * natEq (pw_zero (Γ := Γ) (two : PTm n))
  · exact le_congr (.eqRefl _) (pw_zero two).eqSymm (le_refl _)

theorem bit_double (i w : PTm n) : Γ ⊢[PRAAx] bit (succ i) (two * w) ≐ bit i w :=
  (congrAp1 parF (congrAp2 quoF (add_zero _).eqSymm (.eqRefl _))).eqTrans (bit_succ (zero_le one))

/-! ## Sums split along different parameters -/

/-- If `f(i, x) = g(i, y) + h(i, z) + k(i, u)` for `i < N`, then the sums split. -/
theorem sum_lin3 (f g h k : PTm 2) (x y z u N : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 f (var 0) (Syn.shift x) ≐
      inst2 g (var 0) (Syn.shift y) + inst2 h (var 0) (Syn.shift z) + inst2 k (var 0) (Syn.shift u)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF g) N y + ap2 (sumF h) N z + ap2 (sumF k) N u := by
  let g' : PTm 2 := Syn.subst ![var 0, fstT (var 1)] g
  let h' : PTm 2 := Syn.subst ![var 0, fstT (sndT (var 1))] h
  let k' : PTm 2 := Syn.subst ![var 0, sndT (sndT (var 1))] k
  have ig : ∀ (i q : PTm (n + 1)), inst2 g' i q = inst2 g i (fstT q) := fun i q => by
    rw [inst2_sub]; simp [inst2]
  have ih : ∀ (i q : PTm (n + 1)), inst2 h' i q = inst2 h i (fstT (sndT q)) := fun i q => by
    rw [inst2_sub]; simp [inst2]
  have ik : ∀ (i q : PTm (n + 1)), inst2 k' i q = inst2 k i (sndT (sndT q)) := fun i q => by
    rw [inst2_sub]; simp [inst2]
  have e₀ : Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF (addBody (addBody g' h') k')) N (pairT y (pairT z u)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, inst2_addBody, inst2_addBody, ig, ih, ik]
    refine (Prf.impE hp.allOpen.wk Prf.hyp0).eqTrans ?_
    exact congrAdd (congrAdd (congrInst2 g (.eqRefl _) (fM _ _ _).eqSymm) (congrInst2 h (.eqRefl _) (fX _ _ _).eqSymm))
      (congrInst2 k (.eqRefl _) (fY _ _ _).eqSymm)
  have eg : Γ ⊢[PRAAx] ap2 (sumF g') N (pairT y (pairT z u)) ≐ ap2 (sumF g) N y := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, ig]
    exact congrInst2 g (.eqRefl _) (fM _ _ _)
  have eh : Γ ⊢[PRAAx] ap2 (sumF h') N (pairT y (pairT z u)) ≐ ap2 (sumF h) N z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, ih]
    exact congrInst2 h (.eqRefl _) (fX _ _ _)
  have ek : Γ ⊢[PRAAx] ap2 (sumF k') N (pairT y (pairT z u)) ≐ ap2 (sumF k) N u := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, ik]
    exact congrInst2 k (.eqRefl _) (fY _ _ _)
  exact e₀.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd ((sum_add _ _ _ _).eqTrans (congrAdd eg eh)) ek))

/-! ## The sets `S_{m,r}` -/

section Sets

variable (χ : PTm 2)

/-- The code `⟨m, ⟨r, x⟩⟩`. -/
abbrev Y {n : ℕ} (m r x : PTm n) : PTm n := pairT m (pairT r x)

/-- `[χ(m v + r, x) ≠ 0]`. -/
abbrev Mv {n : ℕ} (v m r x : PTm n) : PTm n := sg (inst2 χ (m * v + r) x)

/-- Over `0 = v`, `1 = ⟨m, ⟨r, x⟩⟩`. -/
abbrev mB : PTm 2 := sg (Syn.subst ![fstT (var 1) * var 0 + fstT (sndT (var 1)), sndT (sndT (var 1))] χ)

theorem inst2_m (v y : PTm n) : inst2 (mB χ) v y = sg (inst2 χ (fstT y * v + fstT (sndT y)) (sndT (sndT y))) := by
  have : inst2 (mB χ) v y = sg (inst2 (Syn.subst ![fstT (var 1) * var 0 + fstT (sndT (var 1)), sndT (sndT (var 1))] χ) v y) := by
    simp [inst2]
  rw [this, inst2_sub]; simp [inst2]

theorem m_at (v m r x : PTm n) : Γ ⊢[PRAAx] inst2 (mB χ) v (Y m r x) ≐ Mv χ v m r x := by
  rw [inst2_m]
  exact congrSg (congrInst2 χ (congrAdd (congrMul (fM _ _ _) (.eqRefl _)) (fX _ _ _)) (fY _ _ _))

theorem Mv_even (w m r x : PTm n) : Γ ⊢[PRAAx] Mv χ (two * w) m r x ≐ Mv χ w (two * m) r x :=
  congrSg (congrInst2 χ (by ipra_ring) (.eqRefl _))

theorem Mv_odd (w m r x : PTm n) : Γ ⊢[PRAAx] Mv χ (two * w + one) m r x ≐ Mv χ w (two * m) (m + r) x :=
  congrSg (congrInst2 χ (by ipra_ring) (.eqRefl _))

/-- `|S_{m,r}| = ∑_{v < 2^d} [v ∈ S_{m,r}]`. -/
abbrev K {n : ℕ} (d m r x : PTm n) : PTm n := ap2 (sumF (mB χ)) (pw two d) (Y m r x)

/-- `|S_{m,r}| = |S_{2m,r}| + |S_{2m,m+r}|`. -/
theorem k_split (d m r x : PTm n) :
    Γ ⊢[PRAAx] K χ (succ d) m r x ≐ K χ d (two * m) r x + K χ d (two * m) (m + r) x := by
  refine (congrAp2 (sumF (mB χ)) (pw_two_succ _) (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
  refine (sum_lin3 _ (mB χ) (mB χ) LeanProofs.IPRA.Combinatorics.Vandermonde.zB _ (Y (two * m) r x) (Y (two * m) (m + r) x)
    zero _ (.allI (.impI ?_))).eqTrans ((congrAdd (.eqRefl _) (LeanProofs.IPRA.Combinatorics.Vandermonde.zsum _ _)).eqTrans
      (add_zero _))
  have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  have e₁ : Syn.shift (Y (two * m) r x) = Y (two * Syn.shift m) (Syn.shift r) (Syn.shift x) := by simp [Syn.shift]
  have e₂ : Syn.shift (Y (two * m) (m + r) x) = Y (two * Syn.shift m) (Syn.shift m + Syn.shift r) (Syn.shift x) := by
    simp [Syn.shift]
  rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, e₁, e₂, ez, inst2_pair, LeanProofs.IPRA.Combinatorics.Vandermonde.inst2_z]
  refine (congrAdd ((m_at _ _ _ _ _).eqTrans ((Mv_even _ _ _ _ _).eqTrans (m_at _ _ _ _ _).eqSymm))
    ((m_at _ _ _ _ _).eqTrans ((Mv_odd _ _ _ _ _).eqTrans (m_at _ _ _ _ _).eqSymm))).eqTrans (add_zero _).eqSymm

end Sets

/-! ## Edges -/

section Edges

variable (χ : PTm 2)

theorem congrMv {v v' : PTm n} (m r x : PTm n) (h : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx] Mv χ v m r x ≐ Mv χ v' m r x :=
  congrSg (congrInst2 χ (congrAdd (congrMul (.eqRefl _) h) (.eqRefl _)) (.eqRefl _))

/-- `[v ∈ S] [v + 2^i ∈ S] [bit_i(v) = 0]`, over `0 = i`, `1 = ⟨v, y⟩`. -/
abbrev eiB : PTm 2 := Syn.subst ![fstT (var 1), sndT (var 1)] (mB χ) *
  Syn.subst ![fstT (var 1) + pw two (var 0), sndT (var 1)] (mB χ) * monus one (bit (var 0) (fstT (var 1)))

theorem inst2_ei (i z : PTm n) : inst2 (eiB χ) i z =
    inst2 (mB χ) (fstT z) (sndT z) * inst2 (mB χ) (fstT z + pw two i) (sndT z) * monus one (bit i (fstT z)) := by
  have : inst2 (eiB χ) i z = inst2 (Syn.subst ![fstT (var 1), sndT (var 1)] (mB χ)) i z *
      inst2 (Syn.subst ![fstT (var 1) + pw two (var 0), sndT (var 1)] (mB χ)) i z * monus one (bit i (fstT z)) := by
    simp [inst2]
  rw [this, inst2_sub, inst2_sub]; simp [inst2]

theorem ei_at (i v m r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (eiB χ) i (pairT v (Y m r x)) ≐ Mv χ v m r x * Mv χ (v + pw two i) m r x * monus one (bit i v) := by
  rw [inst2_ei]
  have f := fst_pair (Γ := Γ) v (Y m r x); have s := snd_pair (Γ := Γ) v (Y m r x)
  refine congrMul (congrMul ((congrInst2 (mB χ) f s).eqTrans (m_at _ _ _ _ _))
    ((congrInst2 (mB χ) (congrAdd f (.eqRefl _)) s).eqTrans (m_at _ _ _ _ _))) ?_
  exact congrMonus (.eqRefl _) (congrAp1 parF (congrAp2 quoF f (.eqRefl _)))

/-- `∑_{i < d} [v, v + 2^i ∈ S] [bit_i v = 0]`: the edges from `v` upward. -/
abbrev EI {n : ℕ} (d v m r x : PTm n) : PTm n := ap2 (sumF (eiB χ)) d (pairT v (Y m r x))

/-- Over `0 = v`, `1 = ⟨d, y⟩`. -/
abbrev eoB : PTm 2 := ap2 (sumF (eiB χ)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_eo (v w : PTm n) : inst2 (eoB χ) v w = ap2 (sumF (eiB χ)) (fstT w) (pairT v (sndT w)) := by simp [inst2]

theorem eo_at (v d m r x : PTm n) : Γ ⊢[PRAAx] inst2 (eoB χ) v (pairT d (Y m r x)) ≐ EI χ d v m r x := by
  rw [inst2_eo]
  exact congrAp2 (sumF (eiB χ)) (fst_pair _ _) (LeanProofs.IPRA.congrPairT (.eqRefl _) (snd_pair _ _))

/-- `e(S_{m,r})`. -/
abbrev E {n : ℕ} (d m r x : PTm n) : PTm n := ap2 (sumF (eoB χ)) (pw two d) (pairT d (Y m r x))

/-- `[2w ∈ S] [2w + 1 ∈ S]`, over `0 = w`, `1 = y`. -/
abbrev cB : PTm 2 := Syn.subst ![two * var 0, var 1] (mB χ) * Syn.subst ![two * var 0 + one, var 1] (mB χ)

theorem c_at (w m r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB χ) w (Y m r x) ≐ Mv χ (two * w) m r x * Mv χ (two * w + one) m r x := by
  have : inst2 (cB χ) w (Y m r x) = inst2 (mB χ) (two * w) (Y m r x) * inst2 (mB χ) (two * w + one) (Y m r x) := by
    have h : inst2 (cB χ) w (Y m r x) = inst2 (Syn.subst ![two * var 0, var 1] (mB χ)) w (Y m r x) *
        inst2 (Syn.subst ![two * var 0 + one, var 1] (mB χ)) w (Y m r x) := by simp [inst2]
    rw [h, inst2_sub, inst2_sub]; simp [inst2]
  rw [this]; exact congrMul (m_at _ _ _ _ _) (m_at _ _ _ _ _)

/-- `c = #{w < 2^d : 2w, 2w + 1 ∈ S}`. -/
abbrev Cc {n : ℕ} (d m r x : PTm n) : PTm n := ap2 (sumF (cB χ)) (pw two d) (Y m r x)

alias nb_of_zero := Common.monus_one_of_zero

theorem nb_of_one {b : PTm n} (h : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] monus one b ≐ zero :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_self _)

theorem EI_even (d w m r x : PTm n) :
    Γ ⊢[PRAAx] EI χ (succ d) (two * w) m r x ≐ Mv χ (two * w) m r x * Mv χ (two * w + one) m r x + EI χ d w (two * m) r x := by
  refine (sum_shift _ _ _).eqTrans (congrAdd ?_ ?_)
  · refine (ei_at _ _ _ _ _ _).eqTrans ?_
    refine (congrMul (congrMul (.eqRefl _) (congrMv χ _ _ _ (congrAdd (.eqRefl _) (pw_zero two))))
      (nb_of_zero ((bit_zero _).eqTrans (par_double w)))).eqTrans ?_
    exact (mul_comm _ _).eqTrans (one_mul _)
  · refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have e₁ : Syn.shift (pairT (two * w) (Y m r x)) = pairT (two * Syn.shift w) (Y (Syn.shift m) (Syn.shift r) (Syn.shift x)) := by
      simp [Syn.shift]
    have e₂ : Syn.shift (pairT w (Y (two * m) r x)) = pairT (Syn.shift w) (Y (two * Syn.shift m) (Syn.shift r) (Syn.shift x)) := by
      simp [Syn.shift]
    rw [e₁, e₂, inst2_shiftBody]
    refine (ei_at _ _ _ _ _ _).eqTrans (.eqTrans ?_ (ei_at _ _ _ _ _ _).eqSymm)
    have ev2 : (lt (var 0) (Syn.shift d) :: Γ.map Fm.shift) ⊢[PRAAx] two * Syn.shift w + pw two (succ (var 0)) ≐ two * (Syn.shift w + pw two (var 0)) :=
      (congrAdd (.eqRefl _) (pw_two_succ _)).eqTrans (by ipra_ring)
    exact congrMul (congrMul (Mv_even _ _ _ _ _) ((congrMv χ _ _ _ ev2).eqTrans (Mv_even _ _ _ _ _)))
      (congrMonus (.eqRefl _) (bit_double _ _))

theorem EI_odd (d w m r x : PTm n) :
    Γ ⊢[PRAAx] EI χ (succ d) (two * w + one) m r x ≐ EI χ d w (two * m) (m + r) x := by
  refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ ?_).eqTrans (zero_add _))
  · refine (ei_at _ _ _ _ _ _).eqTrans ?_
    exact (congrMul (.eqRefl _) (nb_of_one ((bit_zero _).eqTrans (par_double_succ w)))).eqTrans (mul_zero _)
  · refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have e₁ : Syn.shift (pairT (two * w + one) (Y m r x)) =
        pairT (two * Syn.shift w + one) (Y (Syn.shift m) (Syn.shift r) (Syn.shift x)) := by simp [Syn.shift]
    have e₂ : Syn.shift (pairT w (Y (two * m) (m + r) x)) =
        pairT (Syn.shift w) (Y (two * Syn.shift m) (Syn.shift m + Syn.shift r) (Syn.shift x)) := by simp [Syn.shift]
    rw [e₁, e₂, inst2_shiftBody]
    refine (ei_at _ _ _ _ _ _).eqTrans (.eqTrans ?_ (ei_at _ _ _ _ _ _).eqSymm)
    have ev2 : (lt (var 0) (Syn.shift d) :: Γ.map Fm.shift) ⊢[PRAAx] two * Syn.shift w + one + pw two (succ (var 0)) ≐ two * (Syn.shift w + pw two (var 0)) + one :=
      (congrAdd (.eqRefl _) (pw_two_succ _)).eqTrans (by ipra_ring)
    exact congrMul (congrMul (Mv_odd _ _ _ _ _) ((congrMv χ _ _ _ ev2).eqTrans (Mv_odd _ _ _ _ _)))
      (congrMonus (.eqRefl _) (bit_succ (le_refl one)))

/-- `e(S_{m,r}) = c + e(S_{2m,r}) + e(S_{2m,m+r})`. -/
theorem E_split (d m r x : PTm n) :
    Γ ⊢[PRAAx] E χ (succ d) m r x ≐ Cc χ d m r x + E χ d (two * m) r x + E χ d (two * m) (m + r) x := by
  refine (congrAp2 (sumF (eoB χ)) (pw_two_succ _) (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
  refine sum_lin3 _ (cB χ) (eoB χ) (eoB χ) _ (Y m r x) (pairT d (Y (two * m) r x)) (pairT d (Y (two * m) (m + r) x)) _
    (.allI (.impI ?_))
  have e₀ : Syn.shift (pairT (succ d) (Y m r x)) = pairT (succ (Syn.shift d)) (Y (Syn.shift m) (Syn.shift r) (Syn.shift x)) := by
    simp [Syn.shift]
  have e₁ : Syn.shift (pairT d (Y (two * m) r x)) = pairT (Syn.shift d) (Y (two * Syn.shift m) (Syn.shift r) (Syn.shift x)) := by
    simp [Syn.shift]
  have e₂ : Syn.shift (pairT d (Y (two * m) (m + r) x)) =
      pairT (Syn.shift d) (Y (two * Syn.shift m) (Syn.shift m + Syn.shift r) (Syn.shift x)) := by simp [Syn.shift]
  rw [e₀, e₁, e₂, LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, inst2_pair]
  refine (congrAdd ((eo_at _ _ _ _ _ _).eqTrans (EI_even _ _ _ _ _ _)) ((eo_at _ _ _ _ _ _).eqTrans (EI_odd _ _ _ _ _ _))).eqTrans ?_
  exact congrAdd (congrAdd (c_at _ _ _ _ _).eqSymm (eo_at _ _ _ _ _ _).eqSymm) (eo_at _ _ _ _ _ _).eqSymm

end Edges

/-! ## The inequality -/

section Ineq

variable (χ : PTm 2)

alias sg_le_one := Common.sg_le_one

theorem c_le_left (d m r x : PTm n) : Γ ⊢[PRAAx] le (Cc χ d m r x) (K χ d (two * m) r x) := by
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  have e₁ : Syn.shift (Y (two * m) r x) = Y (two * Syn.shift m) (Syn.shift r) (Syn.shift x) := by simp [Syn.shift]
  rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, e₁]
  refine le_congr (c_at _ _ _ _ _).eqSymm ((Mv_even _ _ _ _ _).eqTrans (m_at _ _ _ _ _).eqSymm) ?_
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (one_mul _))
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (sg_le_one _))

theorem c_le_right (d m r x : PTm n) : Γ ⊢[PRAAx] le (Cc χ d m r x) (K χ d (two * m) (m + r) x) := by
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  have e₁ : Syn.shift (Y (two * m) (m + r) x) = Y (two * Syn.shift m) (Syn.shift m + Syn.shift r) (Syn.shift x) := by
    simp [Syn.shift]
  rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, e₁]
  refine le_congr (c_at _ _ _ _ _).eqSymm ((Mv_odd _ _ _ _ _).eqTrans (m_at _ _ _ _ _).eqSymm) ?_
  exact le_congr (.eqRefl _) (one_mul _)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (sg_le_one _) (le_refl _))

/-- `2^{2e(S_{m,r})} ≤ |S_{m,r}|^{|S_{m,r}|}`. -/
abbrev Pd {n : ℕ} (d m r x : PTm n) : Fm PTm n := le (pw two (two * E χ d m r x)) (pw (K χ d m r x) (K χ d m r x))

theorem P_succ {d m r x : PTm n} (h₀ : Γ ⊢[PRAAx] Pd χ d (two * m) r x) (h₁ : Γ ⊢[PRAAx] Pd χ d (two * m) (m + r) x) :
    Γ ⊢[PRAAx] Pd χ (succ d) m r x := by
  have eK := k_split (Γ := Γ) χ d m r x
  have eE := E_split (Γ := Γ) χ d m r x
  refine .orE (lt_or_le (K χ d (two * m) r x) (K χ d (two * m) (m + r) x)) ?_ ?_
  · have s := LeanProofs.IPRA.Geometry.HypercubeSplit.edge_step h₁.wk h₀.wk (c_le_left χ d m r x).wk (le_of_lt Prf.hyp0)
    refine le_congr (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (.eqRefl _) (congrMul (.eqRefl _) eE.wk |>.eqTrans
      (by ipra_ring))).eqSymm (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (eK.wk.eqTrans (add_comm _ _))
      (eK.wk.eqTrans (add_comm _ _))).eqSymm s
  · have s := LeanProofs.IPRA.Geometry.HypercubeSplit.edge_step h₀.wk h₁.wk (c_le_right χ d m r x).wk Prf.hyp0
    refine le_congr (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (.eqRefl _) (congrMul (.eqRefl _) eE.wk |>.eqTrans
      (by ipra_ring))).eqSymm (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr eK.wk eK.wk).eqSymm s

theorem P_zero (m r x : PTm n) : Γ ⊢[PRAAx] Pd χ zero m r x := by
  have eE : Γ ⊢[PRAAx] E χ zero m r x ≐ zero := by
    refine (congrAp2 (sumF (eoB χ)) (pw_zero two) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
    exact (congrAdd (sum_zero _ _) ((eo_at _ _ _ _ _ _).eqTrans (sum_zero _ _))).eqTrans (zero_add _)
  have eK : Γ ⊢[PRAAx] K χ zero m r x ≐ Mv χ zero m r x := by
    refine (congrAp2 (sumF (mB χ)) (pw_zero two) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
    exact (congrAdd (sum_zero _ _) (m_at _ _ _ _ _)).eqTrans (zero_add _)
  have l : Γ ⊢[PRAAx] pw two (two * E χ zero m r x) ≐ one :=
    (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (.eqRefl _) ((congrMul (.eqRefl _) eE).eqTrans (mul_zero _))).eqTrans
      (pw_zero _)
  have r' : Γ ⊢[PRAAx] pw (K χ zero m r x) (K χ zero m r x) ≐ one := by
    refine (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr eK eK).eqTrans ?_
    refine .orE (zo_sg (inst2 χ (m * zero + r) x)) ?_ ?_
    · exact (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr Prf.hyp0 Prf.hyp0).eqTrans (pw_zero _)
    · exact (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr Prf.hyp0 Prf.hyp0).eqTrans (pw_one _)
  exact le_congr l.eqSymm r'.eqSymm (le_refl _)

theorem congrE {d m m' r r' x : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] E χ d m r x ≐ E χ d m' r' x :=
  congrAp2 (sumF (eoB χ)) (.eqRefl _) (LeanProofs.IPRA.congrPairT (.eqRefl _)
    (LeanProofs.IPRA.congrPairT hm (LeanProofs.IPRA.congrPairT hr (.eqRefl _))))

theorem congrK {d m m' r r' x : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] K χ d m r x ≐ K χ d m' r' x :=
  congrAp2 (sumF (mB χ)) (.eqRefl _) (LeanProofs.IPRA.congrPairT hm (LeanProofs.IPRA.congrPairT hr (.eqRefl _)))

theorem congrPd {d m m' r r' x : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hr : Γ ⊢[PRAAx] r ≐ r')
    (h : Γ ⊢[PRAAx] Pd χ d m r x) : Γ ⊢[PRAAx] Pd χ d m' r' x :=
  le_congr (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (.eqRefl _) (congrMul (.eqRefl _) (congrE χ hm hr)))
    (LeanProofs.IPRA.Geometry.HypercubeSplit.pw_congr (congrK χ hm hr) (congrK χ hm hr)) h

/-! ## The induction -/

/-- `sg(2^{2e} ∸ k^k)`, zero exactly when the inequality holds. -/
abbrev Vt {n : ℕ} (d D t x : PTm n) : PTm n :=
  sg (monus (pw two (two * E χ d (pw two (monus D d)) t x)) (pw (K χ d (pw two (monus D d)) t x) (K χ d (pw two (monus D d)) t x)))

/-- Over `0 = t`, `1 = ⟨d, ⟨D, x⟩⟩`. -/
abbrev vB : PTm 2 := Vt χ (fstT (var 1)) (fstT (sndT (var 1))) (var 0) (sndT (sndT (var 1)))

theorem inst2_v (t w : PTm n) : inst2 (vB χ) t w = Vt χ (fstT w) (fstT (sndT w)) t (sndT (sndT w)) := by simp [inst2]

theorem congrVt {d d' D D' x x' : PTm n} (t : PTm n) (hd : Γ ⊢[PRAAx] d ≐ d') (hD : Γ ⊢[PRAAx] D ≐ D')
    (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx] Vt χ d D t x ≐ Vt χ d' D' t x' := by
  have hm : Γ ⊢[PRAAx] pw two (monus D d) ≐ pw two (monus D' d') := congrPw (.eqRefl _) (congrMonus hD hd)
  have hE : Γ ⊢[PRAAx] E χ d (pw two (monus D d)) t x ≐ E χ d' (pw two (monus D' d')) t x' :=
    congrAp2 (sumF (eoB χ)) (congrPw (.eqRefl _) hd) (LeanProofs.IPRA.congrPairT hd
      (LeanProofs.IPRA.congrPairT hm (LeanProofs.IPRA.congrPairT (.eqRefl _) hx)))
  have hK : Γ ⊢[PRAAx] K χ d (pw two (monus D d)) t x ≐ K χ d' (pw two (monus D' d')) t x' :=
    congrAp2 (sumF (mB χ)) (congrPw (.eqRefl _) hd) (LeanProofs.IPRA.congrPairT hm
      (LeanProofs.IPRA.congrPairT (.eqRefl _) hx))
  exact congrSg (congrMonus (congrPw (.eqRefl _) (congrMul (.eqRefl _) hE)) (congrPw hK hK))

theorem v_at (t d D x : PTm n) : Γ ⊢[PRAAx] inst2 (vB χ) t (pairT d (pairT D x)) ≐ Vt χ d D t x := by
  rw [inst2_v]; exact congrVt χ t (fM _ _ _) (fX _ _ _) (fY _ _ _)

theorem viol_of_P {d D t x : PTm n} (h : Γ ⊢[PRAAx] Pd χ d (pw two (monus D d)) t x) : Γ ⊢[PRAAx] Vt χ d D t x ≐ zero :=
  (congrSg h).eqTrans sg_zero

theorem P_of_viol {d D t x : PTm n} (h : Γ ⊢[PRAAx] Vt χ d D t x ≐ zero) : Γ ⊢[PRAAx] Pd χ d (pw two (monus D d)) t x := by
  refine .orE (zero_or_succ (monus (pw two (two * E χ d (pw two (monus D d)) t x))
    (pw (K χ d (pw two (monus D d)) t x) (K χ d (pw two (monus D d)) t x)))) Prf.hyp0 ?_
  exact succ_ne_zero' _ ((sg_succ _).eqSymm.eqTrans ((congrSg Prf.hyp0).eqSymm.eqTrans h.wk))

theorem psi_base (D x N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (vB χ)) N (pairT zero (pairT D x)) ≐ zero := by
  refine sum_zero_of_all (vB χ) _ (.allI ?_) _
  have e : Syn.shift (pairT (zero : PTm n) (pairT D x)) = pairT zero (pairT (Syn.shift D) (Syn.shift x)) := by simp [Syn.shift]
  rw [e]
  exact (v_at _ _ _ _ _).eqTrans (viol_of_P χ (P_zero χ _ _ _))

theorem psi_step {d D x : PTm n}
    (ih : Γ ⊢[PRAAx] le d D ⟶ (ap2 (sumF (vB χ)) (pw two (monus D d)) (pairT d (pairT D x)) ≐ zero)) :
    Γ ⊢[PRAAx] le (succ d) D ⟶ (ap2 (sumF (vB χ)) (pw two (monus D (succ d))) (pairT (succ d) (pairT D x)) ≐ zero) := by
  refine .impI ?_
  have hle : (le (succ d) D :: Γ) ⊢[PRAAx] le (succ d) D := Prf.hyp0
  have ih' := Prf.impE ih.wk (le_trans (le_succ_self d) hle)
  -- `2^{D−d} = 2 · 2^{D−(d+1)}`.
  have eD : (le (succ d) D :: Γ) ⊢[PRAAx] pw two (monus D d) ≐ two * pw two (monus D (succ d)) := by
    have e₀ : (le (succ d) D :: Γ) ⊢[PRAAx] D ≐ succ (monus D (succ d)) + d := by
      ipra_lc natEq (eq_add_of_le hle)
    exact (congrPw (.eqRefl _) ((congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _))).eqTrans (pw_two_succ _)
  refine (sum_congr_bounded (vB χ) LeanProofs.IPRA.Combinatorics.Vandermonde.zB (pairT (succ d) (pairT D x))
    (pairT (succ d) (pairT D x)) (pw two (monus D (succ d))) (.allI (.impI ?_))).eqTrans
    (LeanProofs.IPRA.Combinatorics.Vandermonde.zsum _ _)
  rw [LeanProofs.IPRA.Combinatorics.Vandermonde.inst2_z]
  have e₁ : Syn.shift (pairT (succ d) (pairT D x)) = pairT (succ (Syn.shift d)) (pairT (Syn.shift D) (Syn.shift x)) := by
    simp [Syn.shift]
  have e₂ : Syn.shift (pw two (monus D (succ d))) = pw two (monus (Syn.shift D) (succ (Syn.shift d))) := by simp [Syn.shift]
  rw [e₁, e₂]
  refine (v_at _ _ _ _ _).eqTrans (viol_of_P χ ?_)
  -- In the binder: `t < m'`, `2^{D'−d'} = 2m'`.
  have ih'' : (le (succ d) D :: Γ).map Fm.shift ⊢[PRAAx]
      ap2 (sumF (vB χ)) (pw two (monus (Syn.shift D) (Syn.shift d))) (pairT (Syn.shift d) (pairT (Syn.shift D) (Syn.shift x))) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih'.shift
  have eD' : (le (succ d) D :: Γ).map Fm.shift ⊢[PRAAx]
      pw two (monus (Syn.shift D) (Syn.shift d)) ≐ two * pw two (monus (Syn.shift D) (succ (Syn.shift d))) := by
    simpa [Fm.shift, Syn.shift] using eD.shift
  have ht : (lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d)))) :: (le (succ d) D :: Γ).map Fm.shift) ⊢[PRAAx]
      lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d)))) := Prf.hyp0
  have h₀ : (lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d)))) :: (le (succ d) D :: Γ).map Fm.shift) ⊢[PRAAx]
      lt (var 0) (pw two (monus (Syn.shift D) (Syn.shift d))) := by
    have e := natEq (eD'.wk (ψ := lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d))))))
    refine le_of_eq_add (d := pw two (monus (Syn.shift D) (succ (Syn.shift d))) + monus (pw two (monus (Syn.shift D)
      (succ (Syn.shift d)))) (succ (var 0))) ?_
    ipra_lc e + natEq (eq_add_of_le ht)
  have h₁ : (lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d)))) :: (le (succ d) D :: Γ).map Fm.shift) ⊢[PRAAx]
      lt (pw two (monus (Syn.shift D) (succ (Syn.shift d))) + var 0) (pw two (monus (Syn.shift D) (Syn.shift d))) := by
    have e := natEq (eD'.wk (ψ := lt (var 0) (pw two (monus (Syn.shift D) (succ (Syn.shift d))))))
    refine le_of_eq_add (d := monus (pw two (monus (Syn.shift D) (succ (Syn.shift d)))) (succ (var 0))) ?_
    ipra_lc e + natEq (eq_add_of_le ht)
  have v₀ := sum_zero_elim (vB χ) ih''.wk h₀
  have v₁ := sum_zero_elim (vB χ) ih''.wk h₁
  have P₀ := congrPd χ eD'.wk (.eqRefl _) (P_of_viol χ ((v_at _ _ _ _ _).eqSymm.eqTrans v₀))
  have P₁ := congrPd χ eD'.wk (.eqRefl _) (P_of_viol χ ((v_at _ _ _ _ _).eqSymm.eqTrans v₁))
  exact P_succ χ P₀ P₁

/-- Variables: `0 = d`, `1 = D`, `2 = x`. -/
private abbrev psiF : Fm PTm 3 :=
  le (var 0) (var 1) ⟶ (ap2 (sumF (vB χ)) (pw two (monus (var 1) (var 0))) (pairT (var 0) (pairT (var 1) (var 2))) ≐ zero)

private theorem psi₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] psiF χ := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (psi_base χ _ _ _)
  · exact psi_step χ Prf.hyp0

/-- `thm:cube-edge`: for `S = {v < 2^D : χ(v, x) ≠ 0}` (as `S_{1,0}`), `2^{2e(S)} ≤ |S|^{|S|}`. -/
theorem cube_edge (D x : PTm n) : Γ ⊢[PRAAx] Pd χ D one zero x := by
  have h := inst (Γ := Γ) (psi₀ χ) (![D, D, x] : Fin 3 → PTm n)
  have h' : Γ ⊢[PRAAx] le D D ⟶ (ap2 (sumF (vB χ)) (pw two (monus D D)) (pairT D (pairT D x)) ≐ zero) := by simpa using h
  have s := Prf.impE h' (le_refl D)
  have e1 : Γ ⊢[PRAAx] pw two (monus D D) ≐ one := (congrPw (.eqRefl _) (monus_self D)).eqTrans (pw_zero _)
  have v := sum_zero_elim (vB χ) s (le_congr (.eqRefl _) e1.eqSymm (le_refl one))
  exact congrPd χ e1 (.eqRefl _) (P_of_viol χ ((v_at _ _ _ _ _).eqSymm.eqTrans v))

end Ineq

end LeanProofs.IPRA.Geometry.HypercubeEdge
