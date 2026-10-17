"""Stage 13.6 at a general precision, upstream; the printed precision is its instance.

`Proofs13PolyStage136` re-proved three results of `Proofs13CommonStepSelection` and
`Proofs13AllDensityExtraction` with the Stage 13.5 precision `ε` as a parameter (hypothesis
`hprec`, budget `ε ≤ ζ/m`). The printed versions are the case `ε = |P|^(−1/2^(11q))`, whose
`hprec` is a field of `IsStage135Data`. The general versions move into the printed modules and
the printed theorems become their instances; statements are unchanged.
"""
from foldlib import Fold

F = Fold()
CS, AD, PS = 'Proofs13CommonStepSelection', 'Proofs13AllDensityExtraction', 'Proofs13PolyStage136'
F.move(PS, ['stage136_common_step_mem_bohr_at', 'lemma_13_6_of_bohr_models_at'], CS,
       'stage136_common_step_mem_bohr')
F.move(PS, ['lemma_13_6_from_initial_stages_at'], AD,
       'lemma_13_6_from_initial_stages_all_densities_with_length')
F.reprove(CS, 'stage136_common_step_mem_bohr', '''
  stage136_common_step_mem_bohr_at S theta zeta _ D E m K h134 h135.2.2.2.2.1 hK hbudget''')
F.reprove(CS, 'lemma_13_6_of_bohr_models_with_length', '''
  lemma_13_6_of_bohr_models_at S theta zeta _ D E m Y K psi h134 h135 h135.2.2.2.2.1 hm hsize hupper
    hlower hY hK hbudget hmodel''')
F.reprove(AD, 'lemma_13_6_from_initial_stages_all_densities_with_length', '''
  lemma_13_6_from_initial_stages_at S D E m _ h134 h135 h135.2.2.2.2.1 hm hsize hupper hlower
    hbudget''')
s = F.get(PS)
a = '''* `lemma_13_6_from_initial_stages_at`: the corpus construction with the
  precision `ε` as a parameter, under the budget `ε ≤ ζ/m`.'''
assert s.count(a) == 1
F.text[PS] = s.replace(a, '''* `lemma_13_6_from_initial_stages_at` (`Proofs13AllDensityExtraction`): the
  corpus construction with the precision `ε` as a parameter, under the budget
  `ε ≤ ζ/m`; the printed Stage 13.6 is its case `ε = |P|^(−1/2^(11q))`.''')
F.commit()
