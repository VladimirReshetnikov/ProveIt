#!/usr/bin/env python3
"""Replay the focused optional grammar-research packet, standard library only."""
from pathlib import Path
from hashlib import sha256
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'reference/theory_encoding'))
import check_dne_variants as v
import boolean_bundle_variants as b
sys.path.insert(0, str(HERE/'fine/runtime/code'))
from audit_fine_grammar import audit


def main():
    spec = v.load_spec()
    leaves = [spec['bundle_C']('a', 'b', 'c'), spec['bundle_G']('a', 'b', 'c'),
              v.imp(('rel', 'a', 'b'), ('all', 'c', ('rel', 'a', 'b'))),
              v.imp(('eq', 'a', 'b'), ('all', 'c', ('eq', 'a', 'b')))]
    _, _, rows, prefix, mapping = b.context()
    def tree(t):
        if type(t) is int:
            assert 0 <= t < 4
            return leaves[t], [t]
        assert isinstance(t, list) and len(t) == 2
        left, li = tree(t[0]); right, ri = tree(t[1])
        return v.conjunction(left, right), li+ri
    def boundary(t, path=()):
        if t in leaves or not isinstance(t, tuple):
            return []
        result = [path] if v.is_neg(t) and v.is_neg(t[1]) else []
        if t[0] == 'imp':
            result += boundary(t[1], path+(1,)) + boundary(t[2], path+(2,))
        return result
    def check_word(row, formula):
        assert v.freeze(row['bundle']) == formula and formula[0] == 'imp'
        word = prefix + v.emit(formula) + v.TAIL
        assert row['word'] == word
        stack, events = v.execute_macros(word[:-len(v.TAIL)])
        assert stack == ['old_top'] + rows + [formula]
        assert events == [(176, 2), (158, 4)]
        fine = ''.join(mapping[str(op)] for op in word)
        assert row['fine_AX'] == fine and row['fine_length'] == len(fine)
        assert row['fine_sha256'] == sha256(fine.encode()).hexdigest()
    family = json.loads((HERE/'bundle_variants.json').read_text())['variants']
    assert len(family) == 528
    masks = {}
    for row in family:
        proof = row['proof']
        formula, permutation = tree(proof['tree'])
        assert permutation == proof['permutation'] and sorted(permutation) == list(range(4))
        selected = {tuple(path) for path in proof['boundary_double_negations']}
        assert selected <= set(boundary(formula))
        formula = v.normalize(formula, selected)
        check_word(row, formula)
        assert row['mask'] not in masks
        masks[row['mask']] = formula
    deeper = json.loads((HERE/'bundle2002_dne_variants.json').read_text())['variants']
    assert len(deeper) == 32
    for row in deeper:
        proof = row['proof']
        formula = masks[proof['conjunction_source']]
        selected = {tuple(path) for path in proof['additional_DNE_original_addresses']}
        assert selected <= set(v.redexes(formula))
        check_word(row, v.normalize(formula, selected))
    chosen = json.loads((HERE/'selected/selection.json').read_text())
    grammar_results = []
    for selection in chosen:
        folder = HERE/selection['directory']
        candidates = [folder/'seed.json', folder/'search.json']
        for candidate in candidates:
            if not candidate.exists():
                continue
            report = audit(candidate, short_scan=True)
            assert report['status'] == 'PASS_FINE_GRAMMAR'
            grammar_results.append({'file': str(candidate.relative_to(HERE)),
                                    'rules': report['grammar_states'],
                                    'framework': report['framework_states'],
                                    'nominal_total': report['working_states'],
                                    'sha256': report['candidate_sha256']})
    control = audit(HERE/'reference/normalized245_grammar.json', short_scan=True)
    assert control['working_states'] == 245 and control['grammar_states'] == 128
    result = {'status': 'PASS_OPTIONAL_RESEARCH_ARTIFACTS',
              'scope': 'Exact symbolic source-family replay and independent finite grammar audits. This is separate from the primary QT244 machine proof.',
              'conjunction_variants_checked': len(family), 'additional_DNE_variants_checked': len(deeper),
              'retained_grammars_checked': len(grammar_results), 'retained_grammars': grammar_results,
              'normalized_control_total': control['working_states']}
    (HERE/'results/package_verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    assert __debug__, 'Assertions must remain enabled.'
    main()
