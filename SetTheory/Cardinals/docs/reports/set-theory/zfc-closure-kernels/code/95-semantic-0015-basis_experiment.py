#!/usr/bin/env python3
"""Cost and symbolically verify three-parameter logical-basis replacements.

The new abstract bases are mathematically equivalent to the old propositional
basis when complete. No calibrated new binary consistency machine is claimed.
Use of the existing named TMBuilder measures only that backend, and a semantic
AX word is emitted separately for the current compression backend.
"""
from __future__ import annotations

import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT
RESEARCH = OUT / 'vendor/research'
BACKEND = OUT / 'vendor/wade'
sys.path[:0] = [str(RESEARCH), str(BACKEND)]
import recover_wade_dag as recovery
import theory_backend_experiment as tb
import TMBuilder as backend

SNAPSHOT = OUT / 'vendor/busy-beaver'
tb.SNAPSHOT = SNAPSHOT
nodes, names = recovery.parse_dag((SNAPSHOT / 'ZF/m254/coq/prog/Dag254.v').read_text())
spec, spec_sha = tb.published_spec()
old_rows = spec['ax_rows']('a', 'h', 'b', 'c', 'u')[1:]
prefix = [166, 121, 180, 176]
bundle = spec['bundle']('a', 'b', 'c')
I = tb.Imp
a, b, c = 'a', 'b', 'c'
K = I(a, I(b, a))
S = I(I(a, I(b, c)), I(I(a, b), I(a, c)))
P = I(I(I(a, b), a), a)
H = I(I(a, b), I(I(b, c), I(a, c)))

data = json.loads((OUT / 'vendor/route245/research/architecture/semantic_rows.json').read_text())
macro_words = {int(k): v for k, v in data['macros'].items()}
macro_words[177] = 'V'
macro_words[218] = 'V' + macro_words[119]
fine = {k: tuple(v) for k, v in data['fine_atom_expansions'].items()}

def expansion(word):
    return tuple(i for c in word for i in fine[c])

def spelling(word):
    target = expansion(word)
    opt = [None] * (len(target) + 1)
    opt[-1] = ''
    for k in range(len(target)-1, -1, -1):
        for c, chunk in fine.items():
            end = k + len(chunk)
            if target[k:end] == chunk and opt[end] is not None:
                value = c + opt[end]
                if opt[k] is None or (len(value), value) < (len(opt[k]), opt[k]):
                    opt[k] = value
    assert opt[0] is not None and expansion(opt[0]) == target
    return opt[0]

def variant(label, basis, claim):
    rows = list(basis) + old_rows[1:]
    program = prefix + [x for row in rows for x in tb.emit(row)] + tb.emit(bundle) + tb.TAIL
    actual, _ = tb.symbolic(program)
    expected = ['old_top', spec['wal']('a', 'h')] + rows + [bundle]
    assert actual == expected, label
    assert not any(m in program for m in (158, 208)) or label == 'old'
    raw_word = ''.join(macro_words[m] for m in program)
    word = spelling(raw_word)
    builder = recovery.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    tb.lower_program(builder, nodes, program, label, shared=True)
    builder.generate()
    builder.tm.gc()
    states = {q for q, _ in builder.tm.states}
    path = OUT / ('basis_' + label + '.tm')
    builder.tm.save(str(path))
    return dict(label=label, logical_status=claim, axioms_ast=list(basis),
                axiom_rows=len(rows), AX_macro_count=len(program),
                semantic_AX_word=word, semantic_AX_calls=len(word),
                semantic_AX_fine_operations=len(expansion(word)),
                named_Wade_backend_states=len(states),
                named_table_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                exact_symbolic_stack=True,
                needs_new_program_completeness_macros=True,
                calibrated_ZFC_machine=False)

def main():
    cases = [('old', [old_rows[0]], 'Established upstream basis'),
             ('KHP', [K, H, P], 'Complete Bernays-Tarski basis; primary Pfenning 1988'),
             ('KSP', [K, S, P], 'Complete standard classical implicational basis'),
             ('KS', [K, S], 'Experimental: classicality from retained quantified rows NOT YET PROVED')]
    result = dict(spec_sha256=spec_sha,
                  complete_basis_source='https://www.cs.cmu.edu/~fp/papers/cade88.pdf',
                  results=[variant(*case) for case in cases])
    (OUT / 'basis_results.json').write_text(json.dumps(result, indent=2)+'\n')
    for r in result['results']:
        print(r['label'], r['AX_macro_count'], r['semantic_AX_calls'],
              r['semantic_AX_fine_operations'], r['named_Wade_backend_states'])

if __name__ == '__main__':
    main()
