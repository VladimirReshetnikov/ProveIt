#!/usr/bin/env python3
"""Reconstruct PA194 and verify its literal refinement certificates.

Python 3, standard library only. Run without -O. The default includes all
4,780 universal primitive-branch contracts for both the unfolded202 table
and the final194 table. --quick omits only these two runtime contract lists.
The inherited register-box lemmas remain part of the proof basis. This
executable certificate does not claim a new Lean or Rocq kernel theorem.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

P = Path(__file__).resolve().parent
ROOT = P.parent
REFERENCE = ROOT / 'reference/pa195_conpa/pa195'
spec = importlib.util.spec_from_file_location('pa195_reference_checker', REFERENCE / 'build_verify.py')
need_loader = spec is not None and spec.loader is not None
if not need_loader:
    raise RuntimeError('Cannot load the bundled PA195 checker')
inherited = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inherited)
c = inherited.c
need = inherited.need
EXPECTED = '9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87'


def emitter_certificate(t):
    """Exact whole-stack equality in a free term algebra, with all parameters symbolic."""
    ww = inherited.word(t)
    original = inherited.word(c.read_grammar(REFERENCE / 'grammar.json'))
    need(len(original) == 191 and original[184] == 'cons', 'PA195 word binding')
    need(ww == original[:184] + original[185:], 'separate190 word binding')
    ZERO = ('zero',)
    succ = lambda x: ('succ', x)
    ONE = succ(ZERO)
    add = lambda x, y: ('add', x, y)
    I = lambda a, b: ('im', a, b)
    M = lambda a, b: succ(I(a, b))
    U = lambda a, b: succ(succ(I(b, a)))
    E = lambda a, b: succ(succ(succ(I(a, b))))
    N = lambda a: I(a, ONE)
    And = lambda a, b: N(I(a, N(b)))
    Ex = lambda a, b: N(U(a, N(b)))
    oldt, A, d, h, Y, X = [('atom', z) for z in ['t', 'a', 'd', 'h', 'y', 'x']]
    T, D, H, stack, fields = oldt, d, h, [], [Y, X]
    for op in ww[:-3]:
        if op == 'push':
            stack.append(T); T = ZERO
        elif op in ('copyD', 'copyH', 'copyA'):
            stack.append(T); T = {'copyD': D, 'copyH': H, 'copyA': A}[op]
        elif op == 'cons':
            need(bool(stack), 'symbolic stack underflow')
            T = I(stack.pop(), T)
        elif op == 'incT':
            T = succ(T)
        elif op == 'readH':
            H = add(H, fields.pop(0))
        elif op == 'readDCons':
            D = add(D, fields.pop(0)); T = I(T, D)
        else:
            raise ValueError('unknown emitter macro: ' + str(op))
    need(not fields, 'parameter fields not exhausted')
    heads = [I(Ex(D, U(D, H)), H), I(U(D, U(A, H)), U(A, U(D, H))),
             I(M(H, D), I(E(H, A), M(A, D))),
             I(E(H, D), I(M(A, H), M(A, D))), Ex(D, E(H, D)),
             I(U(D, A), I(U(D, I(A, H)), U(D, H)))]
    rho = I(I(I(H, d), D), I(I(D, H), I(A, H)))
    gamma = I(A, U(A, A))
    V = I(M(H, D), U(A, M(H, D)))
    B = I(A, M(A, D))
    S = U(D, And(I(M(H, D), B), I(M(A, D), A)))
    Q = U(A, I(S, N(B)))
    need(stack == [oldt, U(d, h), rho] + heads + [gamma], 'complete emitted stack')
    need(T == N(I(V, Q)), 'separate guarded gate')
    need(ww[-3:] == ['copyGuard', 'compareGuard', 'close'], 'guard and cleanup')
    return {'macro_tokens': len(ww), 'pa195_deleted_macro_index_zero_based': 184,
            'deleted_macro': 'cons', 'complete_stack_free_algebra_identity': True,
            'complete_top_free_algebra_identity': True, 'stack_entries_pushed': 10,
            'gamma_is_separate_stack_entry': True, 'all_six_head_parameters_unchanged': True,
            'parameter_reads_unchanged': True, 'guard_and_cleanup_unchanged': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--export', action='store_true')
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Run without Python -O')
    for name, digest in json.loads((P / 'input_hashes.json').read_text()).items():
        need(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
             'pinned input hash: ' + name)
    t = c.read_grammar(P / 'grammar.json')
    raw, node_states, shapes = c.build(t)
    need(len(raw) == 404 and len(shapes) == 68, 'unfolded202 census')
    need(raw == inherited.table(P / 'unfolded202.native.tm'), 'unfolded table reconstruction')
    folds = json.loads((P / 'folds.json').read_text())
    need(len(folds) == 8, 'eight folds required')
    folded, aliases = inherited.quotient(raw, folds)
    need(folded == inherited.table(P / 'pa194.native.tm'), 'native table reconstruction')
    local = inherited.quotient_certificate(raw, folded, folds, aliases)
    labels = json.loads((P / 'labels.json').read_text())
    need(len(labels) == 195 and len(set(labels)) == 195 and labels[0] == 74
         and labels[-1] == 254, 'dense labels')
    inverse = {q: i for i, q in enumerate(labels)}
    dense = {(inverse[q], b): (w, d, inverse[n])
             for (q, b), (w, d, n) in folded.items()}
    need(dense == inherited.table(P / 'pa194.tm'), 'literal/native conjugacy')
    need(set(dense) == {(q, b) for q in range(194) for b in (0, 1)}, 'binary literal domain')
    need(hashlib.sha256(inherited.table_bytes(dense)).hexdigest() == EXPECTED, 'literal hash')
    reached, todo = {0}, [0]
    for q in todo:
        for bit in (0, 1):
            n = dense[q, bit][2]
            need(0 <= n <= 194, 'literal target outside state domain')
            if n < 194 and n not in reached:
                reached.add(n); todo.append(n)
    need(reached == set(range(194)), 'advertised states not all graph reachable')
    sites, cfg, contracts = c.source(t)
    parent = c.read_grammar(ROOT / 'reference/separate196/grammar.json')
    oldsites, oldcfg, _ = c.source(parent)
    need(inherited.word(t) == inherited.word(parent), 'archived emitter word changed')
    need([s[1:] for s in sites] == [s[1:] for s in oldsites], 'primitive instruction word changed')
    need(cfg == oldcfg == inherited.interval_cfg(sites) == inherited.interval_cfg(oldsites),
         'ordinal successor graph or independent CFG resolver disagreement')
    need(len(sites) == 3673 and len(contracts) == 4780, 'source census')
    emission = emitter_certificate(t)
    boot = inherited.startup(dense, labels)
    old, _ = c.machine()
    need(all(folded[q, b] == old[q, b] for q in c.BOXSTATES for b in (0, 1)),
         'inherited register-box rows changed')
    source = [{'ordinal': i, 'path': ''.join(map(str, path)), 'op': op,
               'arg': arg, 'instruction': cfg[i]}
              for i, (path, op, arg) in enumerate(sites)]
    binding = {'primitive_sites': len(sites), 'symbolic_branch_contracts': len(contracts),
               'independent_cfg_resolvers': 2, 'ordered_primitive_word_equal_to_separate196': True,
               'all_ordinal_successors_equal_to_separate196': True,
               'macro_word_equal_to_separate196': True,
               'seed_ordinal': 25, 'seed_path': ''.join(map(str, sites[25][0]))}
    result = {'status': 'PASS', 'target_below195_achieved': True, 'working_states': 194,
              'binary_rows': 388, 'start_label': 0, 'halt_label': 194,
              'graph_reachable_working_states': 194, 'literal_sha256': EXPECTED,
              'unfolded_working_states': 202, 'AX_reader_nodes': 68, 'simultaneous_folds': 8,
              'quotient_local_cases': local['local_cases'], 'quotient_durations': local['durations'],
              'source': binding, 'emitter': emission, 'startup_literal_steps': 58154,
              'maximum_source_path_length': max(len(p) for p, _, _ in sites),
              'full_runtime_replayed': not args.quick, 'new_kernel_checked_theorem': False}
    if not args.quick:
        for name, rows in [('unfolded_runtime', raw), ('folded_runtime', folded)]:
            check = c.validate(rows, contracts)
            need(check['ok'], name + ' failed: ' + repr(check))
            result[name] = check
    exports = {'source.json': source, 'source_binding.json': binding,
               'local_fold_certificate.json': local, 'startup_certificate.json': boot,
               'emitter_tokens.json': inherited.word(t), 'emitter_certificate.json': emission}
    for filename, data in exports.items():
        if args.export:
            inherited.dump(P / filename, data)
        elif (P / filename).exists():
            need(json.loads((P / filename).read_text()) == json.loads(json.dumps(data)),
                 'derived export differs: ' + filename)
    if args.export and not args.quick:
        inherited.dump(P / 'validation.json', result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
