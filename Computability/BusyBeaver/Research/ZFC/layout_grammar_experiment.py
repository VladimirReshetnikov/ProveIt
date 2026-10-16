"""Bounded exact-word grammar search on source 19's complete 268-state layout.

Only grammar sharing changes. GEN, all eight equality-bearing logical rows,
the revised C/G conjunction layout, both vacuity arms, parameter acquisition,
base-four constructors, gates, cleanup, and the public backend are retained.
The source-08 grammar/path helpers and source-19 layout functions remain
unchanged. All generated artifacts go to --output outside this checkout.
This is finite register-program evidence, not a binary-TM/ZFC endpoint.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cache
import importlib
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

import full_grammar_experiment as common
import recover_wade_dag as recover
import theory_backend_experiment as theory

ROOT, REPORT = common.ROOT, common.REPORT
RECIPE = dict(C=2, G=1, outer_order=16, tree=1)


def selected_word(nodes):
    layout = common.load_file('source19_layout', REPORT /
                             'code/19-subst-engineering-full_logic_search.py')
    spec, _ = theory.published_spec()
    rows = spec['ax_rows']('a', 'h', 'b', 'c', 'u')
    c = layout.variants(spec['bundle_C']('a', 'b', 'c'), theory)[2]
    g = layout.variants(spec['bundle_G']('a', 'b', 'c'), theory)[1]
    vacuity = [theory.Imp(rel('a', 'b'), theory.All('c', rel('a', 'b')))
               for rel in (theory.Rel, theory.Eq)]
    import itertools
    order = list(itertools.permutations(range(4)))[16]
    factors = [c, g, *vacuity]
    bundle = layout.trees([factors[i] for i in order], theory)[1]
    word = ([166, 121, 180, 176] +
            [q for row in rows[1:] for q in theory.emit(row)] +
            theory.emit(bundle) + theory.TAIL)
    stack, events = theory.symbolic(word)
    if stack != ['old_top', rows[0], *rows[1:], bundle]:
        raise ValueError('selected full logical/theory stack differs')
    stored = json.loads((REPORT / 'data/19-subst-engineering-artifacts-full_logic_results.json').read_text())
    if word != stored['macro_word']:
        raise ValueError('selected layout differs from the reviewed source-19 word')
    if word[:88] != theory.old_contract(nodes)[1] or word[-5:] != theory.TAIL:
        raise ValueError('logical prefix or cleanup changed')
    return word, dict(recipe=RECIPE, all_eight_original_logical_rows_exact=True,
                      original_GEN_exact=True, original_parameter_maps=True,
                      old_rho6=True, base4=True, events=events)


def tokenizations(nodes, word):
    patterns = [(theory.expand(nodes, q), q) for q in [*range(2, 115), 161]]
    patterns = [(p, q) for p, q in patterns if len(p) >= 2]
    def greedy(limit):
        result, i = [], 0
        while i < len(word):
            choices = [(p, q) for p, q in patterns if len(p) <= limit and word[i:i+len(p)] == p]
            if choices:
                p, q = min(choices, key=lambda x: (-len(x[0]), x[1]))
                result.append(q); i += len(p)
            else:
                result.append(word[i]); i += 1
        return result
    coarse, i = [], 0
    while i < len(word):
        if word[i:i+2] == [166, 119]:
            coarse.append(161); i += 2
        else:
            coarse.append(word[i]); i += 1
    words = dict(coarse=coarse, primitive=word, existing_short=greedy(4),
                 existing_minimum=theory.reuse_published_subsequences(nodes, word))
    for lane, tokens in words.items():
        if 1 in tokens or [q for token in tokens for q in theory.expand(nodes, token)] != word:
            raise ValueError('tokenization changed the primitive macro word: ' + lane)
    return words


def transform(nodes, names, word, residual, productions):
    """Keep original helper subgraphs used as tokens; share exact binary pairs."""
    keep = {q for q in nodes if not 1 <= q <= 114}
    pending = [q for q in word if q not in keep]
    while pending:
        q = pending.pop()
        if q in keep:
            continue
        keep.add(q)
        pending.extend(int(e.split()[1]) for e in nodes[q] if e.startswith('ENode '))
    out = {q: nodes[q] for q in keep}
    outnames = {q: names[q] for q in keep}
    intern = {edges: q for q, edges in out.items()}
    refs, next_id = {}, max(nodes) + 1
    def edge(q):
        return f'ENode {refs.get(q, q)}'
    def pair(a, b):
        nonlocal next_id
        es = a, b
        if es not in intern:
            intern[es] = next_id; out[next_id] = es
            outnames[next_id] = f'layout_grammar_{next_id}'; next_id += 1
        return intern[es]
    for i, (a, b) in enumerate(productions):
        refs[300+i] = pair(edge(a), edge(b))
    root = refs.get(residual[-1], residual[-1])
    for q in reversed(residual[:-1]):
        root = pair(edge(q), f'ENode {root}')
    for q in tuple(out):
        out[q] = tuple(f'ENode {root}' if e == 'ENode 1' else e for e in out[q])
    seen, pending = set(), [0]
    while pending:
        q = pending.pop()
        if q not in seen:
            seen.add(q)
            pending.extend(int(e.split()[1]) for e in out[q] if e.startswith('ENode '))
    order = [0] + sorted(seen - {0}); ids = {q: i for i, q in enumerate(order)}
    return ({ids[q]: tuple(f'ENode {ids[int(e.split()[1])]}' if e.startswith('ENode ') else e
                          for e in out[q]) for q in order},
            {ids[q]: outnames[q] for q in order}, ids[root])


def builder_dag(builder):
    root = builder.find_seq('main().0')
    order = [root] + sorted(set(builder.reachable()) - {root})
    ids = {q: i for i, q in enumerate(order)}
    def edge(x):
        if isinstance(x, int): return f'ENode {ids[x]}'
        if x == 'halt': return 'EHalt'
        if x.startswith('_'):
            return ('EBreak ' if x.startswith('_break.') else 'EContinue ') + x.rsplit('.', 1)[1]
        _, reg, op = x.split('.')
        return ('EInc ' if op == 'inc' else 'EDecnz ') + str(recover.REGISTERS.index(reg))
    return ({ids[q]: tuple(edge(x) for x in builder.sequences[q].seq) for q in order},
            {ids[q]: builder.sequences[q].name for q in order})


def dispatch_depth(nodes):
    """Exact max_zeros calculation in Wade's TMBuilder.generate."""
    @cache
    def zeros(q):
        first = nodes[q][0]
        return 1 + (zeros(int(first.split()[1])) if first.startswith('ENode ') else 0)
    return max(2, max(map(zeros, nodes)))


def framework_leaves(nodes):
    return {(bit, e) for es in nodes.values() for bit, e in enumerate(es)
            if not e.startswith('ENode ')}


def independent_check(engine, reference, candidate, certificate):
    """Source-19 style arbitrary-reference check using source-08 path arithmetic."""
    def machine(path):
        d = json.loads(path.read_text())
        assert d['root'] == 0
        return engine.Machine({int(q): tuple(es) for q, es in d['nodes'].items()})
    old, new = machine(reference), machine(candidate)
    cert = json.loads(certificate.read_text()); records = cert['pairs']
    assert cert['initial'] == 0 and cert['branch_order'] == 'EDecnz: zero, positive'
    assert old.contract('') == (records[0]['old'], records[0]['instruction'])
    assert new.contract('') == (records[0]['new'], records[0]['instruction'])
    seen = set()
    for rec in records:
        a, b, e = rec['old'], rec['new'], rec['instruction']
        assert (a, b) not in seen; seen.add((a, b))
        assert old.lookup(a) == (a, e) and new.lookup(b) == (b, e)
        xs, ys = old.targets(a, e), new.targets(b, e)
        assert len(rec['successors']) == len(xs) == len(ys)
        for i, x, y in zip(rec['successors'], xs, ys, strict=True):
            assert type(i) is int and 0 <= i < len(records)
            nxt = records[i]
            assert x == (nxt['old'], nxt['instruction']) and y == (nxt['new'], nxt['instruction'])
    reached, pending = set(), [0]
    while pending:
        i = pending.pop()
        if i not in reached:
            reached.add(i); pending.extend(records[i]['successors'])
    assert len(reached) == len(records)
    return dict(verified=True, reference_nodes=len(old.rows), candidate_nodes=len(new.rows),
                pairs=len(records), instructions=dict(Counter(r['instruction'].split()[0] for r in records)),
                binary_TM_and_ZFC_endpoint_proved=False)


def main():
    if not __debug__: raise RuntimeError('Run without -O: independent finite checks use assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seeds', type=int, default=1000)
    ap.add_argument('--start-seed', type=int, default=0)
    ap.add_argument('--exponents', type=int, nargs='+', default=[1, 2, 4, 8, 16])
    ap.add_argument('--lanes', nargs='+', default=['coarse', 'primitive', 'existing_short', 'existing_minimum'])
    args = ap.parse_args(); out = args.output.resolve()
    if out == ROOT or ROOT in out.parents: ap.error('output must be outside the checkout')
    if args.seeds < 1 or args.start_seed < 0 or any(a < 1 for a in args.exponents): ap.error('invalid search range')
    out.mkdir(parents=True, exist_ok=True)
    helper = common.load_file('source08_layout_helper', REPORT / 'code/08-schema-machine-rebracket_axioms.py')
    engine = common.load_file('source08_layout_independent', REPORT / 'code/08-schema-machine-verify_rm_certificate.py')
    nodes, names = recover.parse_dag(recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    word, contract = selected_word(nodes); words = tokenizations(nodes, word)
    if any(lane not in words for lane in args.lanes): ap.error('unknown tokenization')
    bc = helper.bounder(nodes)
    if any(bc(f'ENode {q}') != (0, 0) for tokens in words.values() for q in tokens):
        raise ValueError('token is not closed under break/continue')
    overlap_control = common.self_check(helper.repair)
    if [q for q, es in nodes.items() if 'ENode 1' in es] != [149]:
        raise ValueError('original AX has an unexpected external entry')
    original_leaves = framework_leaves(nodes)
    for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
        (out / name).write_bytes(recover.git_bytes(None, 'ZF/generator/' + name))
    sys.path.insert(0, str(out)); backend = importlib.import_module('TMBuilder')
    best = None; histograms = {}; changes = {}; diagnostics = Counter(); trials = 0
    depth_histograms, framework_checks = {}, {}
    def check_framework(nn, nm, depth):
        if depth not in framework_checks:
            sample = helper.compile_dag(backend, nn, nm)
            helper.reextract(sample, nn, nm)
            states = {q for q, _ in sample.states}
            actual = sum(q[0].isdigit() for q in states)
            if actual != 55+depth or len(states) != len(nn)+actual:
                raise ValueError('dispatcher cost model failed an actual compiler check')
            framework_checks[depth] = dict(decision_nodes=len(nn), framework_states=actual,
                                           total_states=len(states), every_edge_reextracted=True)
    def consider(lane, algorithm, exponent, seed, seq, grammar):
        nonlocal best
        if common.expand(seq, grammar) != words[lane]: raise ValueError('grammar changed token word')
        nn, nm, root = transform(nodes, names, words[lane], seq, grammar)
        if framework_leaves(nn) != original_leaves:
            raise ValueError('register/control leaves changed the fixed framework')
        depth = dispatch_depth(nn)
        # All other framework states are fixed by the unchanged register and
        # read-sensitive control leaves. Dispatcher states 1..depth are charged.
        # The reviewed depth7 control has55 other framework states, total62.
        cost = len(nn) + 55 + depth
        check_framework(nn, nm, depth)
        if lane in depth_histograms:
            depth_histograms[lane][depth] += 1
        key = cost, len(nn), len(grammar), len(seq), lane, algorithm, exponent, seed
        if best is None or key < best['key']:
            best = dict(key=key, lane=lane, algorithm=algorithm, exponent=exponent, seed=seed,
                        nodes=nn, names=nm, root=root, residual=seq, productions=grammar,
                        dispatch_depth=depth, predicted_framework=55+depth)
            print(json.dumps(dict(minimum_states=cost, lane=lane, algorithm=algorithm,
                                  exponent=exponent, seed=seed)), flush=True)
        return cost
    seq, grammar = helper.repair(words['coarse'], 341, 4)
    if consider('coarse', 'legacy', 4, 341, seq, grammar) != 268:
        raise ValueError('reviewed 268-state baseline did not reproduce')
    negative_seq, negative_grammar = helper.repair(words['coarse'], 445, 4)
    negative, negative_names, _ = transform(nodes, names, words['coarse'], negative_seq, negative_grammar)
    negative_depth = dispatch_depth(negative)
    check_framework(negative, negative_names, negative_depth)
    if len(negative) != 206 or negative_depth != 8:
        raise ValueError('depth-dependent framework regression changed')
    start = time.monotonic()
    for lane in args.lanes:
        histograms[lane] = {}; changes[lane] = Counter(); depth_histograms[lane] = Counter()
        for exponent in args.exponents:
            safe_hist, legacy_hist = Counter(), Counter()
            for seed in range(args.start_seed, args.start_seed + args.seeds):
                seq, grammar, diag = common.safe_repair(words[lane], seed, exponent)
                diagnostics.update(diag)
                safe = consider(lane, 'safe', exponent, seed, seq, grammar); safe_hist[safe] += 1
                ls, lg = helper.repair(words[lane], seed, exponent)
                legacy = consider(lane, 'legacy', exponent, seed, ls, lg); legacy_hist[legacy] += 1
                changes[lane]['different_grammars'] += (seq, grammar) != (ls, lg)
                changes[lane]['different_state_counts'] += safe != legacy
                changes[lane]['safe_smaller'] += safe < legacy
                changes[lane]['legacy_smaller'] += legacy < safe
                trials += 2
            histograms[lane][exponent] = dict(safe=dict(sorted(safe_hist.items())), legacy=dict(sorted(legacy_hist.items())))
            print(json.dumps(dict(lane=lane, exponent=exponent, completed_DAGs=trials,
                                  best_states=best['key'][0], seconds=time.monotonic()-start)), flush=True)
    machine = helper.compile_dag(backend, best['nodes'], best['names'])
    helper.reextract(machine, best['nodes'], best['names']); machine.save(str(out / 'candidate.named.tm'))
    table, labels, missing = common.normalize(machine); (out / 'candidate.tm').write_bytes(table)
    common.write_json(out / 'labels.json', labels)
    builder = recover.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    theory.lower_program(builder, nodes, word, 'revised_layout_reference', shared=True)
    reference, refnames = builder_dag(builder)
    cert, stats = helper.bisimulation(reference, best['nodes'])
    reference_path, candidate_path, cert_path = (out/'reference_dag.json', out/'candidate_dag.json', out/'rm_bisimulation.json')
    common.write_json(reference_path, dict(root=0, nodes=reference, names=refnames))
    common.write_json(candidate_path, dict(root=0, nodes=best['nodes'], names=best['names'], axioms_root=best['root']))
    common.write_json(cert_path, cert)
    common.write_json(out/'grammar.json', dict(primitive_word=word, token_word=words[best['lane']], residual=best['residual'], productions=best['productions']))
    checked = independent_check(engine, reference_path, candidate_path, cert_path)
    wrapper = SimpleNamespace(verify=lambda a,b,c: independent_check(engine, a,b,c))
    mutations = common.mutation_checks(wrapper, reference_path, candidate_path, cert_path, out)
    states = {q for q, _ in machine.states}; framework = sum(q[0].isdigit() for q in states)
    if framework != best['predicted_framework'] or len(states) != best['key'][0]:
        raise ValueError('measured backend disagrees with charged framework cost')
    import hashlib
    result = dict(source19_recipe=RECIPE, original_symbolic_contract=contract,
                  exact_revised_word_preserved=True, every_macro_closed=True,
                  original_source_to_revised_source_bridge='ordinary propositional conjunction transport; not the RM certificate',
                  source_upstream_commit=recover.COMMIT, driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  token_lengths={k:len(v) for k,v in words.items()}, seed_start=args.start_seed, seeds=args.seeds,
                  exponents=args.exponents, lanes=args.lanes, DAG_evaluations=trials,
                  histograms=histograms, histogram_unit='working states, including dispatcher depth',
                  dispatch_depth_histograms=depth_histograms,
                  framework_cost_model='55 fixed states plus max_zeros dispatcher states; unchanged register/control leaves checked',
                  actual_compiler_framework_checks=framework_checks,
                  depth_cost_negative_control=dict(lane='coarse', algorithm='legacy', seed=445,
                                                   exponent=4, decision_nodes=206, dispatcher_depth=8,
                                                   framework_states=63, total_states=269,
                                                   incorrectly_assumed_fixed62_total=268),
                  paired_comparisons=changes, overlap_diagnostics=dict(diagnostics),
                  overlap_self_check=overlap_control,
                  winner={k:best[k] for k in ('lane','algorithm','exponent','seed','key')},
                  decision_nodes=len(best['nodes']), framework_states=framework, working_states=len(states),
                  winner_dispatch_depth=best['dispatch_depth'],
                  named_rows=len(machine.states), total_rows=2*len(states), missing_rows=missing,
                  total_table_sha256=hashlib.sha256(table).hexdigest(),
                  named_table_sha256=hashlib.sha256((out/'candidate.named.tm').read_bytes()).hexdigest(),
                  rm_bisimulation=stats, independent_rm_check=checked, mutations=mutations,
                  improves_source19_268=len(states)<268, binary_compiler_or_ZFC_endpoint_proved=False,
                  elapsed_seconds=time.monotonic()-start)
    common.write_json(out/'results.json', result)
    print(json.dumps({k:result[k] for k in ('winner','working_states','improves_source19_268','elapsed_seconds')},indent=2))


if __name__ == '__main__': main()
