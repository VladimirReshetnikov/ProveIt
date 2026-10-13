"""Thread FinalInputs through Proofs18FinalEnvelopes; general fit lemmas (notes L.16-final)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
env_p, fin_p = GS / 'Proofs18FinalEnvelopes.lean', GS / 'Proofs18Final.lean'
env, fin = env_p.read_text(encoding='utf8'), fin_p.read_text(encoding='utf8')


def cut(s, start, end_marker):
    """Remove from `start` (inclusive) to `end_marker` (exclusive)."""
    a = s.index(start)
    b = s.index(end_marker, a + len(start))
    return s[:a] + s[b:]


def cut_decl(s, head):
    """Remove one declaration (with its doc comment) whose header line starts with `head`."""
    a = s.index(head)
    doc = s.rfind('/--', 0, a)
    if doc != -1 and s[doc:a].count('-/') == 1 and s[s.index('-/', doc) + 2:a].strip() == '':
        a = doc
    m = re.compile(r'\n\n(?=/--|theorem |def |end |namespace |/-!)').search(s, s.index(head))
    return s[:a] + s[m.start() + 2:]


# 1. remove the per-profile versions and the generated fits
for head in ['theorem tightHyp_of_profiles_fejerJT3', 'theorem envBound_allXK3', 'theorem polyEnvBound_allJT3',
             'theorem theorem_16_2_polynomial_fejerT3_of_profiles',
             'theorem corollary_16_11_polynomial_fejerJT3_of_profiles',
             'theorem theorem162At_of_polynomial_fejerT3', 'theorem uDegT3_le_uDeg68', 'theorem tightMuW_le_tightMuV',
             'theorem genMuXK3_small16', 'theorem genMuXK3_fit16']:
    env = cut_decl(env, head)
for C in (16, 32, 64):
    env = cut_decl(env, f'theorem polyGenMuJT3_small{C}')
    env = cut_decl(env, f'theorem polyGenMuJT3_fit{C}')
for C in (32, 64, 128):
    env = cut_decl(env, f'theorem genMuXK3_small{C}')
    env = cut_decl(env, f'theorem genMuXK3_fit{C}')
# empty namespace frames left behind
env = re.sub(r'namespace LeanProofs\.GowersSzemeredi\n\s*end LeanProofs\.GowersSzemeredi\n\n?', '', env)

# 2. the structure moves here from Proofs18Final
a = fin.index('/-- **The inputs of the final route**')
b = fin.index('namespace FinalInputs')
structure = fin[a:b]
fin = fin[:a] + fin[b:]

NEW = structure + r'''/-- The fit of the Theorem 18.1 envelope from `k0` on, given the dimensions `k0, …, 14`. -/
theorem polyGenMuJT3_fit {C k0 k : Nat} (hC : 16 ≤ C)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → polyGenMuJT3 j + 1 ≤ C * 2 ^ j) (hk : k0 ≤ k) :
    polyGenMuJT3 k + 1 ≤ C * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact hsmall k hk (by omega)
  · have := polyGenMuJT3_le16 k h
    have := Nat.mul_le_mul_right (2 ^ k) hC
    omega

/-- The fit of the Theorem 18.2 envelope from `k0` on, given the dimensions `k0, …, 14`. -/
theorem genMuXK3_fit {C k0 k : Nat} (hC : 16 ≤ C)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → genMuXK3 j + 2 * j + 22 ≤ C * 2 ^ j) (hk : k0 ≤ k) :
    genMuXK3 k + 2 * k + 22 ≤ C * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact hsmall k hk (by omega)
  · have := genMuXK3_le16 k h
    have := Nat.mul_le_mul_right (2 ^ k) hC
    omega

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- The parameters of the step in dimension `k`. -/
def params (k : Nat) : GenParamsJT3 := ⟨classV I.Kc I.pc k, k, I.Kc k, I.pc k, tightMu0Z k⟩

/-- The standing hypotheses of the step at the polynomial base budget. -/
theorem hyp {k : Nat} (hk : 2 ≤ k) : (I.params k).CHyp (tightMuW k) (genMuKZ k) := by
  have hKr : (I.Kc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := I.const k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (I.pc k)]
  have hpr : (I.pc k : Real) ≤ 2 ^ ((2 : Nat) ^ genMuKZ k) := by
    have := I.const k; unfold genMuKZ; linarith [Nat.cast_nonneg (α := Real) (I.Kc k)]
  refine ⟨one_le_classV I.Kc I.pc k, classV_le_poly I.Kc I.pc I.const k, le_rfl, ?_, I.two_le_Kc k,
    ?_, I.pc_pos k, ?_⟩
  · show k ≤ 2 ^ tightMu0Z k
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ tightMu0Z k := Nat.pow_le_pow_right (by norm_num) (by
          unfold tightMu0Z; have := five_k_le_pDeg k
          have := le_max_right (tightMuW k) (pDeg k); omega)
  · have : ((I.Kc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hKr
    exact_mod_cast this
  · have : ((I.pc k : Nat) : Real) ≤ ((2 ^ 2 ^ genMuKZ k : Nat) : Real) := by push_cast; exact hpr
    exact_mod_cast this

/-- The polynomial covers at the classes `tDegT3`, over the class base in dimension `l`. -/
theorem cover {l : Nat} (hl : 1 ≤ l) :
    PolyCoverAt l (uCount (classV I.Kc I.pc l) (uDegT3 l)) (uExp (classV I.Kc I.pc l) (uDegT3 l)) :=
  polyCoverAt_classT3 I.Kc I.pc (fun k => le_trans (by norm_num) (I.two_le_Kc k)) I.pc_pos
    (fun k hk => abstractFamilyLemma166At_of k (I.two_le_Kc k) (I.pc_pos k) (I.profile k hk)) hl

/-- The covers the step in dimension `k` needs. -/
theorem covers (k : Nat) : ∀ l, 1 ≤ l → l ≤ (I.params k).k →
    PolyCoverAt l (uCount (I.params k).V (uDegT3 l)) (uExp (I.params k).V (uDegT3 l)) :=
  fun _ hl1 hlk => (I.cover hl1).uniform_mono (one_le_classV I.Kc I.pc _)
    (classV_mono I.Kc I.pc hlk) le_rfl

/-- **The Theorem 18.2 envelope** in every dimension `k ≥ 2`. -/
theorem envBound : ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuXK3 k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact envBound_stepKx3 (I.params 2) (I.hyp le_rfl) (by decide) (I.covers 2)
      (I.profile 2 (by norm_num)) envBound_three
  | succ k hk ih =>
    rw [genMuXK3_succ (by omega)]
    exact envBound_stepKx3 (I.params (k + 1)) (I.hyp (by omega)) (by show 1 ≤ k + 1; omega)
      (I.covers (k + 1)) (I.profile (k + 1) (by omega)) ih

/-- **The Theorem 18.1 envelope** in every dimension `k ≥ 2`. -/
theorem polyEnvBound : ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuJT3 k) := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyEnvBound_stepJT3 (I.params 2) (I.hyp le_rfl) (by decide) (I.covers 2)
      (I.profile 2 (by norm_num)) (polyEnvBound_three_of_phase_partition hpp hp hK hpB)
  | succ k hk ih =>
    rw [polyGenMuJT3_succ (by omega)]
    exact polyEnvBound_stepJT3 (I.params (k + 1)) (I.hyp (by omega)) (by show 1 ≤ k + 1; omega)
      (I.covers (k + 1)) (I.profile (k + 1) (by omega)) ih

/-- **Theorem 16.2 with polynomial controls** at the classes `tDegT3`, in every dimension. -/
theorem theorem_16_2_polynomial {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k)) :=
  (I.cover hk).uniform_mono (one_le_classV I.Kc I.pc k) (classV_le_poly I.Kc I.pc I.const k) le_rfl

/-- **Corollary 16.11 with polynomial exponents** in dimension `k + 1`. -/
theorem corollary_16_11_polynomial {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧
        e⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsJT3.expDegJT3 k (tightMu0Z k) (genMuKZ k) + 3)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  let P := I.params k
  have H : P.CHyp (tightMuW k) (genMuKZ k) := I.hyp hk
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDegT3 l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDegT3 l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((I.profile k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := I.two_le_Kc k; omega) q) q).single
'''
# the rest of the old corollary body, from "-- the two exponents" on
s_old = Path(GS / 'Proofs18FinalEnvelopes.lean').read_text(encoding='utf8')
a = s_old.index('  -- the two exponents')
b = s_old.index('\n\n', s_old.index('_ ≤ _ := hcount', a))
tail = s_old[a:b].replace('(by show 1 ≤ k; omega) ha ha2 hcov hQb', '(by show 1 ≤ k; omega) ha ha2 (I.covers k) hQb')
assert '(I.covers k) hQb' in tail
NEW += tail + '\n\nend FinalInputs\n'
last = env.rindex('end LeanProofs.GowersSzemeredi')
env = env[:last] + NEW + '\n' + env[last:]
env_p.write_text(re.sub(r'\n{3,}', '\n\n', env), encoding='utf8', newline='\n')

# 3. Proofs18Final: use the new lemmas
fin = fin.replace('''  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
  have henv := polyEnvBound_allJT3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const hpp hp hK hpB
    (d - 2) (by omega)''', '''  have henv := I.polyEnvBound (d - 2) (by omega)''')
fin = fin.replace('''  have henv := envBound_allXK3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const (L - 4) (by omega)''',
                  '''  have henv := I.envBound (L - 4) (by omega)''')
assert 'polyEnvBound_allJT3' not in fin and 'envBound_allXK3' not in fin
for old, C, k0 in [('polyGenMuJT3_fit16 (by omega)', 16, 9), ('polyGenMuJT3_fit32 (by omega)', 32, 6),
                   ('polyGenMuJT3_fit64 (by omega)', 64, 2)]:
    assert old in fin, old
    fin = fin.replace(old, f'(polyGenMuJT3_fit (by norm_num) (k0 := {k0})\n    (fun j h1 h2 => by interval_cases j <;> decide +kernel) (by omega))')
for old, C, k0 in [('genMuXK3_fit16 (by omega)', 16, 9), ('genMuXK3_fit32 (by omega)', 32, 7),
                   ('genMuXK3_fit64 (by omega)', 64, 4), ('genMuXK3_fit128 (by omega)', 128, 2)]:
    assert old in fin, old
    fin = fin.replace(old, f'(genMuXK3_fit (by norm_num) (k0 := {k0})\n    (fun j h1 h2 => by interval_cases j <;> decide +kernel) (by omega))')
fin_p.write_text(re.sub(r'\n{3,}', '\n\n', fin), encoding='utf8', newline='\n')
print('envelopes', env.count('\n'), 'final', fin.count('\n'))
