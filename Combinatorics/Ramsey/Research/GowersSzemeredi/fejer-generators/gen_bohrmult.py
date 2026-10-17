"""One symmetric-multiples lemma for Sections 7 and 10.

`Proofs07ProgressionLinearity`, `Proofs07SimultaneousLinearity` and `Proofs10ProgressionLinearity`
each proved, privately, `{j d : |j| ≤ m} ⊆ Bohr(K, ρ)` for `d ∈ Bohr(K, ρ/m)` (the first with
`ρ = α/(32π)` written in, the last for `section10SymmetricMultiples`), with private copies of
`centeredAbs_add_le`, `centeredAbs_neg` and `centeredAbs_nsmul_le`.
- `Proofs07BohrHom`, which all three import, gets `bohr_symmetric_multiples_subset` at any radius
  `ρ ≥ 0` and `centeredAbs_nsmul_le` (with a private `centeredAbs_add_le`: a public one would clash
  with `Proofs16VarietyBoxes`'s, which does not see `Proofs00Basics` or `Proofs07BohrHom`).
- `centeredAbs_neg` moves from `Proofs16Slicing` to `Proofs00Basics` with the same signature, so
  all three can see it; `Proofs16Slicing` keeps it in the global simp set by `attribute [simp]`.
  The three private copies were `@[simp]`, which is global as well, so each of the three modules
  re-applies `attribute [simp] centeredAbs_neg`: every simp set downstream is unchanged.
- The three uses are instances; `section10SymmetricMultiples` is `symmetricMultiples` by unfolding.
- The group-valued Freiman-map lemmas of `Proofs07SimultaneousLinearity`
  (`generic_freiman_map_nat_multiple` / `_int_multiple`) move to `Proofs07BohrHom`;
  `freiman_map_int_multiple_of_zero` (ZMod-valued, used by Sections 7 and 10) is their case
  `G = ZMod N` through `zsmul_eq_mul`, and its private Nat helper is deleted.
"""
from foldlib import Fold

F = Fold()
PL, SL, P10 = 'Proofs07ProgressionLinearity', 'Proofs07SimultaneousLinearity', 'Proofs10ProgressionLinearity'
BH, B0, SLC = 'Proofs07BohrHom', 'Proofs00Basics', 'Proofs16Slicing'
ATTR = 'attribute [simp] centeredAbs_neg\n'


def sub1(m, a, b):
    s = F.get(m)
    assert s.count(a) == 1, (m, s.count(a), a[:80])
    F.text[m] = s.replace(a, b)


def replace_block(m, name, text):
    s = F.get(m)
    st, en = F._block(m, name)
    F.text[m] = s[:st] + text + '\n' + s[en:]


# the shared lemmas, from the Section 7 copies
add_le = F.take(PL, 'centeredAbs_add_le')
nsmul = F.take(PL, 'centeredAbs_nsmul_le')
F.delete_decl(PL, 'bohr_symmetric_multiples_subset')
bohr = F.take(SL, 'bohr_symmetric_multiples_subset')
F.delete_decl(SL, 'centeredAbs_add_le')
F.delete_decl(SL, 'centeredAbs_nsmul_le')
assert bohr.startswith('private lemma bohr_symmetric_multiples_subset {p : Nat} [NeZero p]\n'), bohr[:90]
assert bohr.count('(hrho : 0 < rho)') == 1
bohr = bohr.replace('(hrho : 0 < rho)', '(hrho : 0 ≤ rho)').replace('private lemma', 'theorem', 1)
bohr = ('/-- **Symmetric multiples of a small Bohr element**: if `d ∈ Bohr(K, ρ/m)` then\n'
        '`{j d : |j| ≤ m} ⊆ Bohr(K, ρ)`. -/\n' + bohr)
assert add_le.startswith('private lemma centeredAbs_add_le {N : Nat} [NeZero N]'), add_le[:80]
assert nsmul.startswith('private lemma centeredAbs_nsmul_le {N : Nat} [NeZero N]'), nsmul[:80]
nsmul = '/-- `|n x| ≤ n |x|` for the centered absolute value. -/\n' + nsmul.replace('private lemma', 'theorem', 1)
F.insert(BH, add_le + '\n' + nsmul + '\n' + bohr)

# `centeredAbs_neg`: one public copy, in Proofs00Basics, with the signature of Proofs16Slicing's
neg = '''@[simp] theorem centeredAbs_neg {N : Nat} [NeZero N] (x : ZMod N) :
    centeredAbs (-x) = centeredAbs x := ZMod.natAbs_valMinAbs_neg x
'''
sub1(SLC, neg, ATTR)
F.insert(B0, 'section\n\n' + neg.replace('@[simp] ', '') + '\nend\n')
replace_block(PL, 'centeredAbs_neg', ATTR)
replace_block(SL, 'centeredAbs_neg', ATTR)

# Section 10
for n in ['cor1014_centeredAbs_add_le', 'cor1014_centeredAbs_nsmul_le', 'cor1014_symmetric_multiples_subset']:
    F.delete_decl(P10, n)
replace_block(P10, 'cor1014_centeredAbs_neg', ATTR)
sub1(P10, 'exact cor1014_symmetric_multiples_subset K zeta',
     'exact bohr_symmetric_multiples_subset K zeta')

# Freiman maps on symmetric progressions: the group-valued lemmas of SimultaneousLinearity move to
# BohrHom; ProgressionLinearity's ZMod-valued pair is their case `G = ZMod N`
gen = (F.take(SL, 'generic_freiman_map_nat_multiple') + '\n'
       + F.take(SL, 'generic_freiman_map_int_multiple'))
assert gen.count('private lemma') == 2
gen = gen.replace('private lemma generic_freiman_map_nat_multiple',
                  '/-- A Freiman map vanishing at zero is additive along `{n d : n ≤ m}`. -/\n'
                  'theorem generic_freiman_map_nat_multiple')
gen = gen.replace('private lemma generic_freiman_map_int_multiple',
                  '/-- A Freiman map vanishing at zero is `ℤ`-linear on `{j d : |j| ≤ m}`. -/\n'
                  'theorem generic_freiman_map_int_multiple')
F.insert(BH, gen)
F.delete_decl(PL, 'freiman_map_nat_multiple')
F.reprove(PL, 'freiman_map_int_multiple_of_zero', '''
  (generic_freiman_map_int_multiple B psi hpsi hpsiZero d m hm hmem j hj).trans
    (zsmul_eq_mul _ _)''')

# the radius α/(32π) of Lemma 7.x, written as (α/(32π))/m
sub1(PL, '''    bohr_symmetric_multiples_subset K alpha halpha m hm d hd
''', '''    bohr_symmetric_multiples_subset K (alpha / (32 * Real.pi)) (by positivity) m hm d
      (by rwa [div_div])
''')
for m in (PL, SL, P10):
    s = F.get(m)
    for n in ['cor1014_centeredAbs_add_le', 'cor1014_centeredAbs_nsmul_le', 'cor1014_centeredAbs_neg']:
        assert n not in s, (m, n)
F.commit()
