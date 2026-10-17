"""Walsh family: the printed Lemma 15.1 / Corollary 15.2 become the ternary cases of the general
theorems of Proofs15WalshGeneral, which moves to the bottom of the Walsh stack.

  WalshGeneral : imports Sections14_15; gains parityCharacter_eq_prod, walshProduct_eq_parity
  Walsh        : imports WalshGeneral; lemma_15_1_holds is a one-line instance
  Walsh2       : corollary_15_2_holds is a one-line instance (+ the record alias)
  DegenerateRange : imports Walsh2 (same closure as before)
"""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
rd = lambda m: (GS / f'{m}.lean').read_text(encoding='utf8')


def wr(m, s):
    (GS / f'{m}.lean').write_text(s, encoding='utf8', newline='\n')


def cut(s, start, end):
    i = s.index(start)
    j = s.index(end, i)
    return s[i:j]


g, w, w2, dr = rd('Proofs15WalshGeneral'), rd('Proofs15Walsh'), rd('Proofs15Walsh2'), rd('Proofs15DegenerateRange')

# the two parity lemmas, verbatim from Walsh2
parity = cut(w2, 'theorem parityCharacter_eq_prod', '/-- **Corollary 15.2.**')
assert parity.count('theorem ') == 2

# --- WalshGeneral
assert g.startswith('import GowersSzemeredi.Proofs15Walsh2\n')
g = 'import GowersSzemeredi.Sections14_15\n' + g[len('import GowersSzemeredi.Proofs15Walsh2\n'):]
old_doc = ('This is what Lemma 15.4 needs for coefficient patterns in `[−m, m]` rather\n'
           'than `{−1, 0, 1}`, as required by the Fejér selection of L.16. -/')
new_doc = ('The printed statements are the ternary cases: `lemma_15_1_holds`\n'
           '(`Proofs15Walsh`) and `corollary_15_2_holds` (`Proofs15Walsh2`) apply these\n'
           'theorems and drop the unused hypothesis.\n\n'
           'This is what Lemma 15.4 needs for coefficient patterns in `[−m, m]` rather\n'
           'than `{−1, 0, 1}`, as required by the Fejér selection of L.16. -/')
assert old_doc in g
g = g.replace(old_doc, new_doc)
a = 'alias parityCharacter_eq_prod_general := parityCharacter_eq_prod\n\n'
assert a in g
g = g.replace(a, parity)
b = 'alias corollary_15_2_of_general := corollary_15_2_holds\n\n'
assert b in g
g = g.replace(b, '')
wr('Proofs15WalshGeneral', g)

# --- Walsh
assert w.startswith('import GowersSzemeredi.Sections14_15\n')
head = w[:w.index('/-- **Lemma 15.1 (Walsh basis).**')]
head = 'import GowersSzemeredi.Proofs15WalshGeneral\n' + head[len('import GowersSzemeredi.Sections14_15\n'):]
w = head + ('/-- **Lemma 15.1 (Walsh basis).** Constancy of all polynomial moments\n'
            'forces the coefficient function to be a scalar multiple of parity. The\n'
            'ternary hypothesis is not needed (`signedWalsh_multiple_of_invariant`). -/\n'
            'theorem lemma_15_1_holds : lemma_15_1 :=\n'
            '  fun _ _ _ hprime hodd h eta hh _ hinvariant =>\n'
            '    signedWalsh_multiple_of_invariant hprime hodd h eta hh hinvariant\n\n'
            'end LeanProofs.GowersSzemeredi\n')
wr('Proofs15Walsh', w)

# --- Walsh2
w2 = w2.replace(parity, '')
cor = cut(w2, '/-- **Corollary 15.2.**', 'lemma rangeDeg_sum_mul_sub_eq_one')
w2 = w2.replace(cor, '/-- **Corollary 15.2.** The ternary case of\n'
                     '`booleanWalsh_multiple_of_invariant`. -/\n'
                     'theorem corollary_15_2_holds : corollary_15_2 :=\n'
                     '  fun _ _ _ hprime hodd h eta hh _ hinvariant =>\n'
                     '    booleanWalsh_multiple_of_invariant hprime hodd h eta hh hinvariant\n\n'
                     'alias corollary_15_2_of_general := corollary_15_2_holds\n\n')
wr('Proofs15Walsh2', w2)

# --- DegenerateRange
assert dr.startswith('import GowersSzemeredi.Proofs15WalshGeneral\n')
wr('Proofs15DegenerateRange', 'import GowersSzemeredi.Proofs15Walsh2\n' + dr[len('import GowersSzemeredi.Proofs15WalshGeneral\n'):])
print('ok')
