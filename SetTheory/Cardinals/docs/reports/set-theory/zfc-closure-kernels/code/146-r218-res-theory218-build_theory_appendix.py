#!/usr/bin/env python3
"""Assemble the theory appendix; source and proof receipts remain separate."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).parent
intro = r'''---
title: "Formalism research below the published 219-state machine"
date: "20 October 2026"
---

# Results and proof boundaries

This appendix records new logical investigations made after the release of
K219 at ProveIt commit `26d5de6d21fa354d50e0b84fe851c289925b8d72`.
The published source has 206 DAG nodes and 4,744 primitive occurrences.
The target of this research is a machine with at most 218 working states.
A machine-level reduction that retains the published calculus does not
depend on any unproved theory change investigated here.

The new formalism results have four distinct statuses:

| Result | Status |
|---|---|
| A uniform obstruction to a large family of fourth-parameter restrictions | Proved in ZFC, using the inherited full-HC model and a new finite algebra certificate |
| The fused row D is exactly equivalent to T plus explicit explosion | Proved by an explicit 211-node implication certificate |
| A nontrivial terminal cluster in a specified Kripke semantics yields an ordinary calibrated model | Proved for that semantic class; no representation theorem is asserted |
| Replacing the original rho6 by T plus explosion preserves Con(ZFC) | Open |

No changed-calculus source in the finite hardware screens reaches 218.
Their costs are bounds inside the stated preserved-row compiler model,
not state lower bounds for arbitrary Turing machines. Bounded proof-search
failures below are reported as search outcomes, not as independence proofs.

The existing G/H calibration and older encoding-family work remain in the
previous frozen research reports. They are not repeated or relabeled as
new results here.
'''

bounded = r'''
# Eliminating a different propositional parameter

The uniform negative theorem concerns the fourth slot U of the native row

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

It does not rule out eliminating B instead. A concrete three-parameter
proposal sets B to native truth, while preserving A,C,U independently.
Once the required truth and detachment are available, its reduced form is

\[
 ((C\to U)\to A)\to((A\to C)\to C).
\]

The alternative B=A→A was also tested. No positive calibration was found.
The final bounded screen includes the arithmetic identity I(0,0)=0;
ordinary free-term unification would miss such native specializations.
The search permits a cyclic implication equation only when the complete
cyclic component can collapse to zero. A positive quantifier code cannot
collapse this way. This follows from positivity of the nonzero native
constructor codes and their strict growth above their children.

The modal runs include one fixed binder, native GEN, retained quantifier
normality, and the original rho6. Their bounds are formula size 101,
quantifier depth 8, at most 2,000 processed nodes, and 90 seconds. The
recorded results are:

| Basis and added schemes | Generated / processed | New target theorems | Search boundary |
|---|---:|---|---|
'''
labels = {
    'native_zero_b_truth_none_prop.json': ('B=truth, propositional only', 'none'),
    'native_zero_b_truth_none_modal.json': ('B=truth, modal', 'none'),
    'native_zero_b_truth_identity_modal.json': ('B=truth, modal, identity supplied', 'none beyond the supplied identity'),
    'native_zero_b_truth_explosion_modal.json': ('B=truth, modal, explosion supplied', 'none'),
    'native_zero_b_aa_none_modal.json': ('B=A→A, modal', 'none'),
    'native_zero_b_aa_identity_modal.json': ('B=A→A, modal, identity supplied', 'none beyond the supplied identity'),
    'native_zero_reduced_none_modal.json': ('Reduced row, modal', 'none'),
    'native_zero_reduced_identity_modal.json': ('Reduced row, modal, identity supplied', 'Peirce'),
}
for filename, (label, found) in labels.items():
    receipt = json.loads((ROOT / filename).read_text())
    boundary = 'saturated within bounds' if receipt['saturated_within_bounds'] else 'time bound'
    bounded += f"| {label} | {receipt['nodes']} / {receipt['processed']} | {found} | {boundary} |\n"
bounded += r'''

Identity was not independently recovered in the rows where it was supplied
as an extra assumption; those entries are not positive derivations of a
basis. The reduced row with supplied identity does derive Peirce within
the discovery system, but the remaining basis targets were not found.
This does not calibrate the complete native calculus. Positive results
from this search would still require explicit substitution/MP/GEN replay.
The finite search boundary cannot establish nonderivability.

An untested logical direction survives the uniform obstruction: allow U
to range over a sufficient family of membership atoms. Those atoms can
take value 2 in the inherited four-valued model, so the range argument
does not apply. Whether such a restriction admits a structural
completeness proof, and whether it can be emitted more cheaply than the
33-leaf fourth-argument reader, remain open. There is no claimed candidate
or calibration along that direction.

# Reproducibility and source dependencies

The finite proof and algebra checks require only Python and have no network
dependency:

```sh
python3 certify_fused_d.py --verify-only
python3 uniform_rho8_obstruction.py
```

The source screens require the vendored 219/220/221 macro dependencies and
the repaired 219 hardware objective. Their JSON receipts retain every
layout choice and every evaluated cost. Bare-cost pruning discards only
layouts whose nonnegative-overhead bound cannot improve the current best
inside this same model. Recreating these exploratory screens is separate
from replaying the accepted machine's exact literal table.

| Source-screen script | Layouts | Best protected hardware bound |
|---|---:|---:|
| `t_explosion_source_screen.py` | 72 | 226 |
| `t_explosion_chunk_screen.py` | 756 | 222 |
| `fused_d_source_screen.py` | 103 | 221 |
| `fused_d_equivalent_screen.py` | 318 | 222 |

The mathematical proofs of the uniform extension and terminal-cluster
theorem are ordinary proofs formalizable in ZFC. The finite certificates
check their explicitly identified finite premises; they do not pretend
to kernel-check the infinite-domain arguments.

Primary dependencies in the published K219 packet are:

- `report/sections/calibration.tex`: finite-refutation calibration.
- `research/theory/restricted_rho8_strong_countermodel.md`: the full HC model.
- The vendored `CD230.v`: K, S, and Peirce from rho8 alone.
- The vendored `Comp_Prop230.v`: the pure-implicational deduction theorem.

The local proofs are pinned through the supplied predecessor archives.
Public source:

- [ProveIt ZFC research, pinned new release](https://github.com/VladimirReshetnikov/ProveIt/tree/26d5de6d21fa354d50e0b84fe851c289925b8d72/Computability/BusyBeaver/Research/ZFC)
- [Inherited implicational derivations](https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/CD230.v)
- [Inherited deduction theorem](https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Comp_Prop230.v)
'''

parts = [intro]
for name in ('calibration_audit.md', 'fused_d_equivalence.md',
             't_explosion_terminal_clusters.md', 'uniform_rho8_obstruction.md'):
    fragment = (ROOT / name).read_text()
    parts.append(re.sub(r'^(##+) [0-9]+\. ', r'\1 ', fragment, flags=re.MULTILINE))
parts.append(bounded)
combined = '\n\n'.join(parts)
(ROOT / 'formalism218_appendix.md').write_text(combined)

# Preserve the rich Markdown source.  The ASCII text copy avoids missing
# mathematical glyphs inside monospaced inline code in TeX's text fonts.
replacements = {'→': '->', '↔': '<->', '⇒': '=>', '≠': '!=', '∈': ' in ',
                '⊆': ' subseteq ', '∀': 'forall ', '∃': 'exists ', '∪': ' union ',
                '≼': '<=', '∅': 'empty', 'ρ': 'rho', 'κ': 'kappa', 'χ': 'chi',
                'φ': 'phi', '⊥': 'bottom', '¬': 'not ', '∧': ' and ', '∨': ' or ',
                '∎': '(End of proof.)', '—': '--', '–': '-', '‘': "'", '’': "'",
                '“': '"', '”': '"'}
for old, new in replacements.items():
    combined = combined.replace(old, new)
(ROOT / 'formalism218_appendix_tex_input.md').write_text(combined)
print('Wrote consolidated Markdown and TeX input.')
