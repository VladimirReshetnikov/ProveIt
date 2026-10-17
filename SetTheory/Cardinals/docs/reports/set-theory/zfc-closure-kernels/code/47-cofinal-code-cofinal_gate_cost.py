#!/usr/bin/env python3
"""Full-cost controls for cofinal matrix-code generation.

Requires a pinned ProveIt source snapshot. No consistency-machine claim is
made for the generated Wade tables: this is a source/compiler cost experiment.
All original logical outputs are retained before the bundle parameters change.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import importlib
import json
from pathlib import Path
import sys
from collections import Counter


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seeds', type=int, default=32)
    args = p.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    research = repo / 'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0, str(research))
    import recover_wade_dag as recover
    import theory_backend_experiment as theory
    from full_grammar_experiment import safe_repair, expand
    from pairing_backend_experiment import execute_helper
    from register_lifetime_experiment import compile_measure, macro_word
    backend_dir = out / 'backend'
    backend_dir.mkdir(exist_ok=True)
    for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
        (backend_dir / name).write_bytes(recover.git_bytes(None, 'ZF/generator/' + name))
    sys.path.insert(0, str(backend_dir))
    backend = importlib.import_module('TMBuilder')
    raw = recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v')
    nodes, names = recover.parse_dag(raw.decode())
    original = recover.builder_from_dag(backend, nodes, names)
    word, logical, contract = theory.old_contract(nodes)
    expected_rows, _ = theory.symbolic(word[:-5])
    bundle_word = word[len(logical):-5]
    assert theory.symbolic(logical)[0] == expected_rows[:-1]
    original_result = compile_measure(backend, original, 'original-nine', out / 'original')

    helper = copy.deepcopy(original)
    helper.sequence_lookup = {s.seq: i for i, s in enumerate(helper.sequences)}
    regs = [helper.reg(n) for n in recover.REGISTERS]
    def closed(items, name):
        q = helper.add_sequence(items)
        if helper.sequences[q].name is None:
            helper.sequences[q].name = name + '().0'
        return q
    def move(i, j):
        return helper.while_decnz(regs[i], regs[j].inc)
    def clear(i):
        return helper.while_decnz(regs[i], ())
    def addcopy(i):
        return [helper.while_decnz(regs[i], [regs[3].inc, regs[6].inc]), move(6, i)]
    shift = closed(addcopy(4) + addcopy(5) + [regs[3].inc], 'cofinal_shift')
    cleanup = closed([clear(3), clear(4), clear(5)], 'cofinal_cleanup')
    # The specialized C/G templates bind labels 0 and 1.  The extra increment
    # is essential: a=b=c=0 would otherwise produce the forbidden label 1.
    shift_fixed = closed([shift, regs[3].inc], 'cofinal_fixed_shift')
    helper.reduce_to_cons(); helper.name_sequences()
    counts = Counter()
    for a in range(9):
        for b in range(9):
            for c in range(9):
                before = [11, 13, 17, c, a, b, 0, 0, 19]
                values = before[:]
                expected = before[:]; expected[3] = a + b + c + 1
                if execute_helper(helper, shift, values) != ('normal',) or values != expected:
                    raise ValueError(('shift', before, values, expected))
                counts['shift_general'] += 1
                values = before[:]
                expected = before[:]; expected[3] = a + b + c + 2
                if execute_helper(helper, shift_fixed, values) != ('normal',) or values != expected:
                    raise ValueError(('shift_fixed_cg', before, values, expected))
                assert values[3] > max(a, b, 1)
                counts['shift_fixed_cg'] += 1
                expected[3] = expected[4] = expected[5] = 0
                if execute_helper(helper, cleanup, values) != ('normal',) or values != expected:
                    raise ValueError(('cleanup', before, values, expected))
                counts['cleanup'] += 1

    spec, _ = theory.published_spec()
    fixed = theory.And(theory.And(spec['bundle_C'](0, 1, 'c'),
                                 spec['bundle_G'](0, 1, 'c')),
                       theory.And(theory.Imp(theory.Rel('a','b'), theory.All('c',theory.Rel('a','b'))),
                                  theory.Imp(theory.Eq('a','b'), theory.All('c',theory.Eq('a','b')))))
    variants = {
        'cofinal_general': logical + [shift] + bundle_word + [cleanup],
        'cofinal_fixed_cg': logical + [shift_fixed] + theory.emit(fixed) + [cleanup],
    }
    boundary = set(theory.MACROS) | {shift, shift_fixed, cleanup}
    results = {}
    for name, program in variants.items():
        directory = out / name; directory.mkdir(exist_ok=True)
        unshared = copy.deepcopy(helper)
        q = unshared.add_sequence(theory.reuse_published_subsequences(nodes, program))
        unshared.sequences[1].seq = unshared.sequences[q].seq
        unshared.reduce_to_cons(); unshared.name_sequences()
        assert macro_word(unshared, 1, boundary) == program
        unshared_result = compile_measure(backend, unshared, 'original-nine', directory / 'unshared')
        vocab = sorted(set(program)); ids = {v:i for i,v in enumerate(vocab)}
        compact = [ids[v] for v in program]
        records, best, best_builder = [], None, None
        for seed in range(args.seeds):
            b = copy.deepcopy(helper)
            residual, productions, _ = safe_repair(compact, seed, 2)
            assert expand(residual, productions) == compact
            nonterminals = {}
            def token(v):
                return nonterminals[v] if v >= 300 else vocab[v]
            for i, pair in enumerate(productions):
                nonterminals[300+i] = b.add_sequence([token(v) for v in pair])
            q = b.add_sequence([token(v) for v in residual])
            b.sequences[1].seq = b.sequences[q].seq
            b.reduce_to_cons(); b.name_sequences()
            assert macro_word(b, 1, boundary) == program
            measure = compile_measure(backend, b, 'original-nine', None)
            measure['seed'] = seed; records.append(measure)
            key = (measure['total_states'], measure['decision_states'], seed)
            if best is None or key < best:
                best, best_builder = key, b
        measured_best = compile_measure(backend, best_builder, 'original-nine', directory / 'best')
        measured_best['seed'] = best[2]
        results[name] = dict(unshared=unshared_result, best=measured_best,
            histogram=dict(Counter(x['total_states'] for x in records)), candidates=records,
            macro_word=program, macro_expansion_exact=True)
        print(name, unshared_result['total_states'], measured_best['total_states'], flush=True)
    data = dict(proveit_commit='fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
        original=original_result, source_contract=contract, helper_tests=dict(counts),
        variants=results, seeds=args.seeds,
        shift_nodes={'general': shift, 'fixed_cg': shift_fixed}, cleanup_node=cleanup,
        full_original_logical_prefix_preserved=True, new_machine_theorem=False,
        note='Both variants are uncalibrated compiler controls. General c=a+b+d+1; fixed C/G uses c=a+b+d+2 to avoid its reserved labels 0,1. The earlier +1 fixed-label experiment was invalid and is superseded.',
        attribution='Mira-Cult source; Jeff proof; Andrew Wade MIT-0 backend; ProveIt source reconstruction and Re-Pair helpers.',
        source_DAG_sha256=hashlib.sha256(raw).hexdigest())
    (out/'results.json').write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')


if __name__ == '__main__':
    main()
