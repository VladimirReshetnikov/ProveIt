# Free-coefficient83: rigorous divisor-branch obstructions

## Main result

On every unchanged genuine fixed-compiler slice, every full strictly positive zero of the exact83-operation free-coefficient polynomial has auxiliary factor

  norm_aux=z²>0, with z²|Delta and z|V,y_aux.

This excludes every negative auxiliary branch. In particular, the seemingly dangerous f=1,S=A,strong=-1,aux=-Delta branch cannot complete its literal positive auxiliary quotient, even though its two norm equations have infinitely many positive subsystem solutions.

The result is not a full factor normalization. It does not prove the candidate's ordinary-input language sound, nor produce a falsely accepted genuine input. Non-unit main/input/first/index/transport/strong possibilities remain. The established universal bound remains84.

## Proof components

1. `early_auxiliary_norm_lemma.md`: a complete elementary descent for H v²-(H-1)y², its negative minimum, exact negative-equality orbit, positive-small-norm square classification, S=1 exclusion, and the unique possible negative83 auxiliary branch. This component does not assume A even or any other factor a unit.
2. `exceptional_negative_aux_exclusion.md`: the full genuine-source exclusion of that branch. Five unit factors are recovered only inside that branch. Index/transport signs remain ±1. The proof handles both parities of main Pell rank without assuming p=R.
3. `even_parameter_divisor_classification.md`: when A is even, every represented nonzero divisor of Delta is a positive square or a negative divisor with square complementary quotient. This is a value classification only.
4. `squarefree_swapped_norm_obstructions.md`: on squarefree Delta, both input=-Delta and main=-Delta branches are impossible, including every f. A new first-coordinate divisibility lemma eliminates the large strong ranks; a small-target quotient lemma handles the two remaining ranks. The initial f=1-only version is preserved separately.

The final paragraph in the early lemma note records the chronological status before the complete exceptional-branch proof was written; component2 now supplies that proof.

## Source and reproducibility boundary

Exact target: https://github.com/VladimirReshetnikov/ProveIt/blob/0d9d1e0174df30d82d80d758e9ba8e793203126e/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_free_coefficient_scout.json

- independently fetched Git blob SHA: 71edcd445eb45561613d40fbf8908d586f5a782c
- exact JSON SHA256: 682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016
- canonical compact packet.source SHA256: 7834fa4ab4baa9faba720f572301d7f2ef5782a077c5e5adee931c89f46d240c

The separate auditor fetched and matched the immutable source; its receipt and frozen copy are in `/workspace/shared/free83-auxiliary-square-audit-20261003/source/`. The source was read as data only. No upstream Python, saved arithmetic schedule, compiler builder, or historic verifier was executed.

`independent_checks.py` is entirely new bounded code. It authenticates the saved source schedule as data and selected literal definitions, then checks the proof's elementary recurrences and modular lemmas. Run with ordinary Python or `python -O`; both modes use explicit errors rather than assertions. These are finite supplementary checks, not the general proof and not full compiled witnesses. `CHECKS.json` records the counts and proof-file hashes.

Existing research packets were untouched. All new work is confined to this new directory. No publication or upload was performed.
