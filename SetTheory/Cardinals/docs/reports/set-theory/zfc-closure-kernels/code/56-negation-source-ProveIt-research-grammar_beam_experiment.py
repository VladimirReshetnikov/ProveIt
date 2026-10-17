"""Bounded whole-cost grammar beam search on the complete source19 word.

Only exact closed-word rebracketing/sharing changes. The attributed source08
path certificate tools, source19 layout and Wade backend remain unchanged.
This is finite register-program evidence, not a binary or ZFC endpoint.
"""
from pathlib import Path
import argparse, hashlib, importlib, json, sys, time
from collections import Counter
from types import SimpleNamespace
import layout_grammar_experiment as L
import full_grammar_experiment as C
import recover_wade_dag as R

def main():
    if not __debug__:
        raise RuntimeError('Run without -O: exact contract checks use assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--replay', type=Path, help='verify a saved search winner without repeating the beam')
    ap.add_argument('--width', type=int, default=128)
    args = ap.parse_args()
    if args.width < 1:
        ap.error('width must be positive')
    out = args.output.resolve()
    if out == C.ROOT or C.ROOT in out.parents:
        ap.error('output must be outside the checkout')
    out.mkdir(parents=True, exist_ok=True)
    nodes, names = R.parse_dag(R.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    word, contract = L.selected_word(nodes)
    words = L.tokenizations(nodes, word)
    helper = C.load_file('beam_helper', C.REPORT / 'code/08-schema-machine-rebracket_axioms.py')
    if args.replay:
        result = json.loads(args.replay.read_text())
    else:
        start = time.monotonic()
        records = []
        best = None
        seen_counts = 0
        for lane in ['coarse', 'primitive']:
            initial = words[lane]
            beam = [(initial, [])]
            visited = set()
            for depth in range(45):
                pool = {}
                for seq, rules in beam:
                    counts = Counter(zip(seq, seq[1:]))
                    for pair in counts:
                        new = []
                        i = 0
                        n = 0
                        while i < len(seq):
                            if i + 1 < len(seq) and (seq[i], seq[i + 1]) == pair:
                                new.append(300 + len(rules))
                                i += 2
                                n += 1
                            else:
                                new.append(seq[i])
                                i += 1
                        if n < 2:
                            continue
                        rr = rules + [pair]
                        nn, nm, root = L.transform(nodes, names, initial, new, rr)
                        dd = L.dispatch_depth(nn)
                        cost = len(nn) + 55 + dd
                        expanded = {}
                        for j, (a, b) in enumerate(rr):
                            expanded[300 + j] = expanded.get(a, (a,)) + expanded.get(b, (b,))
                        key = (tuple((expanded.get(a, (a,)) for a in new)), tuple(sorted(expanded.values())))
                        seen_counts += 1
                        if key in visited:
                            continue
                        visited.add(key)
                        score = (cost, len(nn), dd, len(new), tuple(new), tuple(rr))
                        pool[key] = (score, new, rr)
                        if best is None or score[:3] < best['score']:
                            assert C.expand(new, rr) == initial
                            best = dict(score=score[:3], lane=lane, residual=new, productions=rr, depth=depth + 1)
                            print('best', best['score'], lane, 'round', depth + 1, flush=True)
                if not pool:
                    break
                chosen = sorted(pool.values())[:args.width]
                beam = [(seq, rr) for _, seq, rr in chosen]
                records.append(dict(lane=lane, depth=depth + 1, candidates=len(pool), retained=len(beam), best_score=chosen[0][0][:3]))
                if depth % 5 == 0:
                    print('round', lane, depth + 1, len(pool), flush=True)
        result = dict(scope='Bounded beam search preserving exact revised complete word, whole cost nodes+55+dispatcher depth; final compilation/certification pending', beam_width=args.width, lanes=['coarse', 'primitive'], best=best, rounds=records, evaluated=seen_counts, seconds=time.monotonic() - start)
    result['pruning_key'] = 'Coarse expansion inventory; distinct binary parses may be discarded. No optimality or identical-cost claim.'
    C.write_json(out / 'search.json', result)
    b = result['best']
    assert C.expand(b['residual'], b['productions']) == words[b['lane']]
    nn, nm, root = L.transform(nodes, names, words[b['lane']], b['residual'], b['productions'])
    assert L.framework_leaves(nn) == L.framework_leaves(nodes)
    bc = helper.bounder(nodes)
    assert all((bc(f'ENode {q}') == (0, 0) for q in words[b['lane']]))
    for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
        (out / name).write_bytes(R.git_bytes(None, 'ZF/generator/' + name))
    sys.path.insert(0, str(out))
    backend = importlib.import_module('TMBuilder')
    machine = helper.compile_dag(backend, nn, nm)
    helper.reextract(machine, nn, nm)
    machine.save(str(out / 'candidate.named.tm'))
    table, labels, missing = C.normalize(machine)
    (out / 'candidate.tm').write_bytes(table)
    C.write_json(out / 'labels.json', labels)
    builder = R.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    L.theory.lower_program(builder, nodes, word, 'beam_reference', shared=True)
    reference, refnames = L.builder_dag(builder)
    cert, stats = helper.bisimulation(reference, nn)
    rp, cp, certp = (out / 'reference_dag.json', out / 'candidate_dag.json', out / 'rm_bisimulation.json')
    C.write_json(rp, dict(root=0, nodes=reference, names=refnames))
    C.write_json(cp, dict(root=0, nodes=nn, names=nm, axioms_root=root))
    C.write_json(certp, cert)
    engine = C.load_file('beam_verify', C.REPORT / 'code/08-schema-machine-verify_rm_certificate.py')
    checked = L.independent_check(engine, rp, cp, certp)
    mutations = C.mutation_checks(SimpleNamespace(verify=lambda a, b, c: L.independent_check(engine, a, b, c)), rp, cp, certp, out)
    states = {q for q, _ in machine.states}
    framework = sum((q[0].isdigit() for q in states))
    assert (len(states), len(nn), L.dispatch_depth(nn)) == tuple(b['score'])
    assert framework == 55 + L.dispatch_depth(nn)
    result.update(scope='Bounded exact-word beam search with actual compilation and independent RM certificate; not a binary/ZFC endpoint', actual_working_states=len(states), actual_framework_states=framework, actual_named_rows=len(machine.states), actual_total_rows=len(states) * 2, exact_word=True, closed_tokens=True, framework_leaf_signature=True, every_decision_edge_reextracted=True, rm_bisimulation=stats, independent_rm_check=checked, mutations=mutations, improves_268=len(states) < 268, binary_TM_or_ZFC_endpoint_proved=False)
    artifact_names = ['candidate.tm', 'candidate.named.tm', 'labels.json',
                      'candidate_dag.json', 'reference_dag.json', 'rm_bisimulation.json']
    actual_hashes = {name: hashlib.sha256((out / name).read_bytes()).hexdigest()
                     for name in artifact_names}
    expected = result.get('fast_replay_artifacts', {}) if args.replay else {}
    if expected:
        assert set(expected) == set(artifact_names), 'unexpected saved artifact set'
        assert all(actual_hashes[name] == expected[name]['sha256']
                   for name in artifact_names), 'saved replay artifact differs'
    result['this_run_artifact_sha256'] = actual_hashes
    result['this_run_saved_artifacts_match'] = True if expected else None
    result['this_run_driver_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['this_run_output'] = str(out)
    C.write_json(out / 'verified.json', result)
    print(json.dumps({k: result[k] for k in ['actual_working_states', 'actual_framework_states', 'independent_rm_check', 'rm_bisimulation']}, indent=2))
if __name__ == '__main__':
    main()
