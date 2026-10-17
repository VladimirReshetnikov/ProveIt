"""One copy of the phase estimates `‖e(x) − 1‖ ≤ 2π|x|/N`, `≤ 2`, and the Bohr phase bound.

`cor57_norm_exponential_sub_one_le` (public, `Proofs05PhaseRemoval`) had private copies in
`Proofs02PhasePartition` (`cor24_…`), `Proofs07BohrHom` (`lemma78_…`) and `Proofs10Main`
(`theorem1013_…`); the last two also shared `‖e(x) − 1‖ ≤ 2`, and Section 10's
`theorem1013_bohr_phase_bound` (`‖e(rd) − 1‖ ≤ 2πε` on `Bohr(K, ε)`) has Section 7's
`lemma78_bohr_phase_bound` as its case `ε = α/(32π)`. All three move to `Proofs00Basics`, which
already holds `cor24_exponential_eq_exp_valMinAbs` and `cor57_norm_exponential` and is upstream of
every user; the copies are deleted and Section 7's bound is an instance.
"""
import re

from foldlib import Fold

F = Fold()
B0, P02, P05, BH, P10 = ('Proofs00Basics', 'Proofs02PhasePartition', 'Proofs05PhaseRemoval',
                         'Proofs07BohrHom', 'Proofs10Main')


def rename(m, a, b):
    s = F.get(m)
    assert re.search(r"(?<![\w'])" + a + r"(?![\w'])", s), (m, a)
    F.text[m] = re.sub(r"(?<![\w'])" + a + r"(?![\w'])", b, s)


main = F.take(P05, 'cor57_norm_exponential_sub_one_le')
assert main.count('cor57_exponential_eq_exp_valMinAbs') == 1
main = main.replace('cor57_exponential_eq_exp_valMinAbs', 'cor24_exponential_eq_exp_valMinAbs')
main = '/-- `‖e(x) − 1‖ ≤ 2π|x|/N`, with `|x|` the centered absolute value. -/\n' + main
bohr = F.take(P10, 'theorem1013_bohr_phase_bound')
bohr = bohr.replace('private lemma theorem1013_bohr_phase_bound', 'lemma bohr_phase_bound', 1)
bohr = bohr.replace('theorem1013_norm_exponential_sub_one_le', 'cor57_norm_exponential_sub_one_le')
bohr = '/-- On `Bohr(K, ε)`, every character of `K` is within `2πε` of `1`. -/\n' + bohr
two = '''/-- `‖e(x) − 1‖ ≤ 2`. -/
lemma norm_exponential_sub_one_le_two {N : Nat} [NeZero N] (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 := by
  calc
    ‖exponential x - 1‖ ≤ ‖exponential x‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [cor57_norm_exponential]
'''
F.insert(B0, 'section\n\n' + main + '\n' + two + '\n' + bohr + '\nend\n')

F.delete_decl(P02, 'cor24_norm_exponential_sub_one_le')
rename(P02, 'cor24_norm_exponential_sub_one_le', 'cor57_norm_exponential_sub_one_le')
for m, p in [(BH, 'lemma78'), (P10, 'theorem1013')]:
    F.delete_decl(m, f'{p}_norm_exponential_sub_one_le')
    F.delete_decl(m, f'{p}_norm_exponential_sub_one_le_two')
    rename(m, f'{p}_norm_exponential_sub_one_le_two', 'norm_exponential_sub_one_le_two')
rename(BH, 'lemma78_norm_exponential_sub_one_le', 'cor57_norm_exponential_sub_one_le')
rename(P10, 'theorem1013_bohr_phase_bound', 'bohr_phase_bound')
s = F.get(P10)
assert not re.search(r'\btheorem1013_norm_exponential_sub_one_le\b', s)
F.reprove(BH, 'lemma78_bohr_phase_bound', '''
  (bohr_phase_bound _ _ d hd r hr).trans_eq (by
    rw [show 2 * Real.pi * (alpha / (32 * Real.pi)) = alpha / 16 * (Real.pi / Real.pi) by ring,
      div_self Real.pi_ne_zero, mul_one])''')
F.commit()
