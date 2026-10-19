#!/usr/bin/env python3
"""Build and audit a literal machine from a routed semantic-word grammar.

Reuses the attributed, inherited RM certificate generator and affine checker;
their accepted rules are not changed.  No proof-assistant endpoint is claimed.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time

from audit_fine_grammar import audit, BASE, INPUTS, TABLE, make_vocabulary

REFERENCE = BASE / 'reference/context246'
sys.path.insert(0, str(REFERENCE / 'code'))
sys.path.insert(0, str(BASE / 'reference/jeff/ZF/m254/tools/prog'))
import rebuild_machines as rebuild
import review_affine_source as review
import rmpath
import parametric_prefix_affine
from generic_affine_driver import check_sites as check_parametric_sites


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def paths(tree, prefix=''):
    if tree[0] == 'L':
        return [(prefix, tree[1])]
    return paths(tree[1], prefix + '0') + paths(tree[2], prefix + '1')


def sparse_boot(table, limit=2000000, minimum_gap=40):
    """Find a concrete empty-IP six-field dirty root, then replay fixed time."""
    q, head, ones = 95, 0, set()
    used = Counter()
    for tick in range(limit + 1):
        if q == 96 and ones and min(ones) == head - 1:
            right_ones = sorted(x for x in ones if x >= head)
            if right_ones and right_ones[0] - head >= minimum_gap:
                header, maximum = right_ones[0], right_ones[-1]
                values, position, good = [], header + 1, True
                while position <= maximum:
                    if position in ones or position + 1 not in ones:
                        good = False
                        break
                    start = position + 1
                    position = start
                    while position in ones:
                        position += 1
                    values.append(position - start - 1)
                if good and len(values) >= 10:
                    logical = [values[i] for i in rebuild.PHYSICAL]
                    if logical[1] == logical[2] == logical[5] == 0:
                        # A second interpreter independently checks this exact
                        # tick count and every surviving one-cell.
                        cells = bytearray(2 * tick + 3)
                        origin = tick + 1
                        position2, q2 = origin, 95
                        for _ in range(tick):
                            w, d, q2 = table[q2, cells[position2]]
                            cells[position2] = w
                            position2 += 1 if d == 'R' else -1
                        dense_ones = [i - origin for i, bit in enumerate(cells) if bit]
                        assert (q2, position2 - origin, dense_ones) == (q, head, sorted(ones))
                        return dict(status='PASS', blank_steps=tick, start=95, dispatcher=96,
                                    head=head, marker=head-1, header=header,
                                    header_distance=header-head, pc='',
                                    physical_registers=values[:9], logical_registers=logical,
                                    spare_values=values[9:], one_count=len(ones),
                                    all_one_positions=sorted(ones), all_other_cells_zero=True,
                                    sparse_dense_exact_agreement=True,
                                    dirty_root_condition='T=W=H=0; the six other logical registers are arbitrary naturals',
                                    used_rows=[[s,b,n] for (s,b),n in sorted(used.items())])
        if tick == limit:
            break
        if (q, int(head in ones)) not in table:
            return dict(status='HALTED_BEFORE_FRAME', blank_steps=tick, state=q, head=head)
        key = q, int(head in ones)
        used[key] += 1
        write, direction, q = table[key]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
    return dict(status='NO_FRAME_WITHIN_BOUND', bound=limit, state=q, head=head,
                one_count=len(ones), minimum_gap=minimum_gap)


def check_bisimulation(old, new, entries):
    first_incs, first_old = rmpath.seg(old, [])
    second_incs, first_new = rmpath.seg(new, [])
    assert rmpath.counts(first_incs) == rmpath.counts(second_incs)
    assert entries and entries[0][:2] == [first_old, first_new]
    edge_count, halt_pairs = 0, 0
    for i, (pa, pb, nz, z) in enumerate(entries):
        ea, qa = rmpath.site(old, pa)
        eb, qb = rmpath.site(new, pb)
        assert ea == eb, (i, ea, eb)
        if ea == ('halt',):
            assert nz is z is None
            halt_pairs += 1
            continue
        assert ea[0] == 'dec'
        for target, xa, xb in ((nz, rmpath.inc_path(qa), rmpath.inc_path(qb)),
                              (z, rmpath.brk(1, qa), rmpath.brk(1, qb))):
            assert type(target) is int and 0 <= target < len(entries)
            ia, sa = rmpath.seg(old, xa)
            ib, sb = rmpath.seg(new, xb)
            assert rmpath.counts(ia) == rmpath.counts(ib)
            assert entries[target][:2] == [sa, sb]
            edge_count += 1
    return dict(status='PASS', pairs=len(entries), edges=edge_count, halt_pairs=halt_pairs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--boot-limit', type=int, default=2000000)
    parser.add_argument('--padding', type=int, default=None,
                        help='Uniform initial header distance; default max(40, maximum path depth + 8).')
    parser.add_argument('--short-scan',action='store_true')
    parser.add_argument('--allow-scanner-risk',action='store_true')
    args = parser.parse_args()
    began = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=True)
    local = audit(args.candidate.resolve(), short_scan=args.short_scan,allow_scanner_risk=args.allow_scanner_risk)
    write_json(args.output / 'local-routing-audit.json', local)
    source = json.loads((INPUTS / 'closed-sequence-grammar-next22.json').read_text())
    gram = json.loads(args.candidate.read_text())
    _, terminals, words, _, _ = make_vocabulary(gram.get('source_override'))
    rules = {w: (a,b) for w,a,b in gram['rules']}
    sequences = set(source['sequence_states'])
    short_scan = bool(args.short_scan or gram.get('short_scan', False))
    erased = ({177} if gram.get('erase177', False) else set()) | ({74} if short_scan else set())
    routes = {(r['source'],r['read']): r['word'] for r in gram.get('routes', [])}
    alloc = {words[q]:q for q in sequences if words[q] in rules}
    available = sorted((sequences | erased) - set(alloc.values()))
    # Labels are immaterial to state count.  Fresh labels also permit larger
    # positive controls; final canonicalization is always dense.
    fresh = 256
    while len(available) < len(rules) - len(alloc):
        if fresh not in available and fresh not in alloc.values():
            available.append(fresh)
        fresh += 1
    for word in sorted(set(rules) - set(alloc)):
        alloc[word] = available.pop(0)
    assert alloc[words[96]] == 96

    def destination(word):
        return source['atoms'][terminals[word]]['state'] if word in terminals else alloc[word]

    original_table, start = rebuild.read_table(TABLE)
    assert start == 95
    table = {key: row for key,row in original_table.items() if key[0] not in sequences | erased}
    for key,(w,d,t) in list(table.items()):
        if short_scan and key == (58,0):
            table[key] = (0,'L',84)
        elif key in routes:
            table[key] = (w,d,alloc[routes[key]])
        elif t in sequences:
            table[key] = (w,d,alloc[words[t]])
        else:
            assert t not in erased
    for word,(left,right) in rules.items():
        table[alloc[word],0] = (0,'R',destination(left))
        table[alloc[word],1] = (1,'R',destination(right))
    states = {q for q,b in table}
    assert len(states) == local['working_states'] and len(table) == 2*len(states)
    assert {t for w,d,t in table.values()} - states == {254}
    tm = args.output / 'machine_old.tm'
    tm.write_text(rebuild.encode(table, 95))
    order = [95] + sorted(states - {95})
    mapping = {q:i for i,q in enumerate(order)} | {254:len(states)}
    canonical = {(mapping[q],b):(w,d,mapping[t]) for(q,b),(w,d,t) in table.items()}
    (args.output / 'machine.tm').write_text(rebuild.encode(canonical, 0))
    write_json(args.output / 'allocation.json', alloc)
    write_json(args.output / 'renumbering.json', dict(old_to_canonical=mapping, canonical_to_old=order))
    by_ast = {int(i):words[int(q)] for q,i in source['sequence_ast_roots'].items()}

    @lru_cache(None)
    def original(i):
        row=source['ast_dag'][i]
        return ('L',tuple(row[1])) if row[0]=='L' else ('N',original(row[1]),original(row[2]))

    @lru_cache(None)
    def changed(i):
        if i in by_ast and by_ast[i] in rules:
            return expand(by_ast[i])
        row=source['ast_dag'][i]
        return ('L',tuple(row[1])) if row[0]=='L' else ('N',changed(row[1]),changed(row[2]))

    @lru_cache(None)
    def expand(word):
        if word in terminals:
            return changed(source['atoms'][terminals[word]]['ast'])
        left,right=rules[word]
        return ('N',expand(left),expand(right))

    pinned_before = original(source['original_ast'])
    override = gram.get('source_override')
    if override is None:
        before = pinned_before
    else:
        # A separate explicitly specified reference program. This is not an
        # assertion that the changed program has the original register effect.
        _, _, immutable_words, _, _ = make_vocabulary()
        assert override['state'] == 76
        assert override['original_word'] == immutable_words[76]
        ast = source['ast_dag']
        @lru_cache(None)
        def bounds(i):
            row = ast[i]
            if row[0] == 'L':
                op, *a = row[1]
                return (1,0) if op=='dec' else (a[0],0) if op=='brk' else (0,a[0]) if op=='cont' else (0,0)
            a,b=bounds(row[1]),bounds(row[2])
            return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
        @lru_cache(None)
        def finest(i):
            row=ast[i]
            return finest(row[1])+finest(row[2]) if row[0]=='N' and bounds(row[1])==bounds(row[2])==(0,0) else (i,)
        fine_ids=sorted(set(t for name in terminals.values() for t in finest(source['atoms'][name]['ast'])))
        char_to_ast=dict(zip('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789',fine_ids))
        atoms=[original(char_to_ast[c]) for c in override['new_word']]
        assert all(bounds(char_to_ast[c])==(0,0) for c in override['new_word'])
        def balanced(xs):
            if len(xs)==1:return xs[0]
            k=len(xs)//2
            return ('N',balanced(xs[:k]),balanced(xs[k:]))
        replacement=balanced(atoms)
        @lru_cache(None)
        def modified(i):
            if i==source['sequence_ast_roots']['76']:return replacement
            row=ast[i]
            return ('L',tuple(row[1])) if row[0]=='L' else ('N',modified(row[1]),modified(row[2]))
        before=modified(source['original_ast'])
        write_json(args.output/'modified_source.json',dict(source_override=override,
            construction='Replace exactly the original AX AST root by a balanced sequence of the listed original closed AST atoms',
            AX_ast=source['sequence_ast_roots']['76'],fine_char_to_ast=char_to_ast,
            logical_sites=[[p,e[0],e[1] if len(e)>1 else None] for p,e in paths(before)]))
    after = changed(source['original_ast'])
    assert [e for p,e in paths(before)] == [e for p,e in paths(after)], 'Compiled source leaf order differs from explicit reference'

    codes = dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')

    def sites(tree, physical):
        result=[]
        for p,edge in paths(tree):
            op=codes[edge[0]]
            arg=edge[1] if len(edge)>1 else None
            if physical and op in ('CI','CD'):
                arg=rebuild.PHYSICAL[arg]
            result.append([p,op,arg])
        return result

    _, pinned_sites = review.parse_source(REFERENCE / 'sources/Prog254.v')
    assert sites(pinned_before, True) == pinned_sites, 'The grammar AST differs from the pinned source.'
    logical_sites, physical_sites = sites(after, False), sites(after, True)
    assert len(logical_sites) == len(physical_sites) == len(paths(before))
    write_json(args.output / 'sites_logical.json', logical_sites)
    write_json(args.output / 'sites_physical.json', physical_sites)
    result = dict(status='PENDING', working_states=len(states), table_sha256=digest(tm),
                  canonical_sha256=digest(args.output / 'machine.tm'),
                  candidate_sha256=digest(args.candidate), source_leaves=len(logical_sites),
                  maximum_depth=max(len(p) for p,op,r in logical_sites),
                  maximum_zero_run=max(max(map(len,p.split('1'))) for p,op,r in logical_sites),
                  local_routing_audit='PASS',root_word_override_checks=local['root_word_override_checks'],
                  short_scanner=short_scan, source_override=override)
    result['expected_guarded_cases'] = sum(2 if op=='CD' else 1 for p,op,r in logical_sites)
    result['source_calibration_scope'] = 'Separate AX logical-transfer proof required' if override else 'Original source'
    padding = args.padding if args.padding is not None else max(40, result['maximum_depth'] + 8)
    print('BUILT',len(states),'states; verifying explicit reference program and',result['expected_guarded_cases'],'affine cases.',flush=True)
    try:
        entries = rmpath.certificate(before, after)
        result['register_program_bisimulation'] = check_bisimulation(before,after,entries)
        bits = lambda xs: ''.join('1' if b else '0' for b in xs)
        write_json(args.output / 'register_bisimulation.json', dict(start_pair=0, entries=[[bits(a),bits(b),nz,z] for a,b,nz,z in entries]))
    except Exception as exc:
        result['register_program_bisimulation'] = dict(status='FAIL',error=repr(exc))
    if result['register_program_bisimulation']['status']=='PASS':
        affine = parametric_prefix_affine
        padding = args.padding if args.padding is not None else max(40, result['maximum_depth'] + 8)
        assert padding >= result['maximum_depth']
        affine.PADDING = padding
        native_run=affine.run
        current={}
        def counted(*run_args,**run_kwargs):
            current.update(pc=run_args[1],branch=run_args[2])
            return native_run(*run_args,**run_kwargs)
        affine.run=counted
        try:
            result['affine_all_cases'] = dict(status='PASS',**check_parametric_sites(affine,{(str(q),b):(w,d,str(t)) for(q,b),(w,d,t) in table.items()},physical_sites,padding))
        except Exception as exc:
            result['affine_all_cases'] = dict(status='FAIL',padding=padding,first_bad_case=current,error=repr(exc))
        result['affine_all_cases']['parametric_rules_sha256']=digest(Path(parametric_prefix_affine.__file__))
    print('AFFINE',result.get('affine_all_cases',{}).get('status','NOT_RUN'),'; checking blank start.',flush=True)
    result['blank_boot'] = sparse_boot(table, args.boot_limit, minimum_gap=padding)
    if result['blank_boot']['status']=='PASS':
        write_json(args.output / 'blank_boot.json',result['blank_boot'])
        result['blank_boot'] = {k:v for k,v in result['blank_boot'].items() if k not in ('all_one_positions','spare_values','used_rows')}
    if result.get('affine_all_cases',{}).get('status')=='PASS':
        result['status'] = 'PASS_AFFINE_AND_BOOT' if result['blank_boot']['status']=='PASS' else 'RUNTIME_PASS_BOOT_UNRESOLVED'
    else:
        result['status'] = 'FAIL'
    result['seconds']=time.monotonic()-began
    result['scope']='Finite register bisimulation, inherited affine symbolic rules with their stated macro contracts, and exact blank boot; no new kernel-checked endpoint.'
    write_json(args.output / 'machine-audit.json',result)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
