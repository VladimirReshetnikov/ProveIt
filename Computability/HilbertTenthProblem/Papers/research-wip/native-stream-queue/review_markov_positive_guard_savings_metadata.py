#!/usr/bin/env python3
"""Fresh structural metadata only: no imported/evaluated author or old arrays."""
import argparse
import hashlib
import json
from pathlib import Path

def require(p, message):
    if not p:
        raise ValueError(message)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def record(path, spans):
    data = path.read_bytes()
    lines = data.splitlines(keepends=True)
    return {'path': str(path), 'bytes': len(data), 'sha256': digest(data),
            'read_spans': [{'first': a, 'last': b,
                            'sha256': digest(b''.join(lines[a-1:b]))}
                           for a, b in spans]}

def recipe(kind, T, q):
    """Independent literal schedule transcription, never an array interpreter."""
    rows, residuals = [], []
    history = kind.endswith('history')
    raw = kind.startswith('raw')
    linked = kind == 'raw_local_linked'
    if history:
        if raw:
            witnesses = ['H0'] + [s+str(j) for j in range(1, T+1)
                                     for s in ('X', 'H')] + ['B'+str(j) for j in range(T)]
            rows.append(['u0', '*', 'H0', 'x'])
        else:
            witnesses = ['C'+str(j) for j in range(1, T+1)] + ['B'+str(j) for j in range(T)]
        external = ['x']
    elif raw:
        external = ['C', 'Cp'] if linked else ['X', 'H', 'Xp', 'Hp']
        witnesses = ['B', 'X', 'H', 'Xp', 'Hp'] if linked else ['B']
        rows.append(['u0', '-', 'X', 'H'])
    else:
        external, witnesses = ['C', 'Cp'], ['B']
        rows.append(['u0', '-', 'C', 1])
    for j in range(T if history else 1):
        suffix = str(j)
        u = 'x' if history and not raw and j == 0 else 'u'+suffix
        if history and j:
            rows.append([u, '-', ('X' if raw else 'C')+suffix,
                         'H'+suffix if raw else 1])
        B = 'B'+suffix if history else 'B'
        t = 't'+suffix
        rows += [[t, '-', B, 2], ['rz'+suffix, '*', t, u]]
        residuals.append('rz'+suffix)
        if raw:
            H = 'H'+suffix if history else 'H'
            Xp = 'X'+str(j+1) if history else 'Xp'
            Hp = 'H'+str(j+1) if history else 'Hp'
            rows += [['tH'+suffix, '*', t, H], ['qX'+suffix, '*', q, Xp],
                     ['transition_partial'+suffix, '-', 'qX'+suffix, u],
                     ['rx'+suffix, '+', 'transition_partial'+suffix, 'tH'+suffix],
                     ['qH'+suffix, '*', q, Hp], ['rh'+suffix, '-', 'qH'+suffix, H]]
            residuals += ['rx'+suffix, 'rh'+suffix]
        else:
            Cp = 'C'+str(j+1) if history else 'Cp'
            rows += [['transition_partial'+suffix, '-', Cp, u],
                     ['rt'+suffix, '+', 'transition_partial'+suffix, t]]
            residuals.append('rt'+suffix)
    if linked:
        rows += [['linked_product', '*', 'H', 'C'], ['link', '-', 'X', 'linked_product'],
                 ['linked_product_next', '*', 'Hp', 'Cp'], ['link_next', '-', 'Xp', 'linked_product_next']]
        residuals += ['link', 'link_next']
    if history:
        rows.append(['endpoint', '-', ('X' if raw else 'C')+str(T), 'H'+str(T) if raw else 1])
        residuals.append('endpoint')
    rows += [['square_'+str(j), '*', r, r] for j, r in enumerate(residuals)]
    tail = 'square_0'
    for j in range(1, len(residuals)):
        nxt = 'join_'+str(j)
        rows.append([nxt, '+', tail, 'square_'+str(j)])
        tail = nxt
    return rows, residuals, tail, external, witnesses

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--author-stem', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    stem = args.author_stem
    author = {ext: record(stem.with_suffix('.'+ext), []) for ext in ('md', 'py', 'json')}
    for ext in ('md', 'py'):
        author[ext] = record(stem.with_suffix('.'+ext), [(1, len(stem.with_suffix('.'+ext).read_bytes().splitlines()))])
    receipt = json.loads(stem.with_suffix('.json').read_bytes())
    require(receipt['helper_sha256'] == author['py']['sha256'], 'author helper binding')
    dependencies = {}
    spans = {'markov_projective_counter_step.md': [(1,134)],
             'review_markov_projective_counter_step.md': [(1,95)],
             'markov_sine_lift.md': [(1,192)],
             'residue_affine_factored_counter_step.md': [(1,66)],
             'markov_projective_counter_step_checks.json': [(697,787),(1755,1945)]}
    for name, metadata in receipt['dependencies'].items():
        r = record(args.root/name, spans[name])
        require(r['sha256'] == metadata['sha256'] and r['bytes'] == metadata['bytes'], 'dependency '+name)
        dependencies[name] = r
    old = json.loads((args.root/'markov_projective_counter_step_checks.json').read_bytes())['packets']
    checked = {}
    for name, p in receipt['packets'].items():
        rows, residuals, output, external, witnesses = recipe(p['kind'], p['T'], p['q'])
        require(rows == p['source'], 'full literal rows '+name)
        require(residuals == p['residuals'] and output == p['output'], 'finalizer '+name)
        require(external == p['external_positive_integer_ports'] and witnesses == p['positive_witnesses'], 'interface '+name)
        require(set(p['ports']) == set(external+witnesses) and len(p['ports']) == len(external+witnesses), 'ports '+name)
        known, ancestors = set(p['ports']), {}
        for dest, op, x, y in rows:
            require(dest not in known and op in ('+', '-', '*'), 'destination '+name)
            require(all(type(v) is int or v in known for v in (x,y)), 'topology '+name)
            known.add(dest)
            ancestors[dest] = [v for v in (x,y) if type(v) is str]
        live, pending = set(), [output]
        while pending:
            v = pending.pop()
            if v not in live:
                live.add(v)
                pending.extend(ancestors.get(v, []))
        require(live == known, 'liveness '+name)
        M = sum(row[1] == '*' for row in rows)
        A = len(rows)-M
        require((M,A,len(rows)) == (p['M'],p['A'],p['total']), 'ledger '+name)
        if p['kind'] == 'direct_history':
            T=p['T']; predicted=(3*T+1,6*T,2*T,4); predecessor=old['direct_'+str(T)]
        elif p['kind'] == 'raw_history':
            T=p['T']; predicted=(7*T+2,8*T,3*T+1,6); predecessor=old['raw_'+str(T)]
        else:
            predicted={'direct_local': (3,5,1,4), 'raw_local_unlinked':(7,7,1,4), 'raw_local_linked':(11,11,5,4)}[p['kind']]
            predecessor=old['direct_local'] if p['kind']=='direct_local' else old['raw_local'] if p['kind']=='raw_local_linked' else None
        require((M,A,len(witnesses),p['exact_degree']) == predicted, 'independent formulas '+name)
        comparison = None
        if predecessor is not None:
            require(set(predecessor['ports']) == set(p['ports']), 'own-parent interface '+name)
            old_M=sum(row[1] == '*' for row in predecessor['source'])
            old_A=len(predecessor['source'])-old_M
            if p['kind']=='direct_history': old_expected=(5*T+1,8*T+2)
            elif p['kind']=='raw_history': old_expected=(9*T+2,10*T+2)
            elif p['kind']=='direct_local': old_expected=(5,7)
            else: old_expected=(13,13)
            require((old_M,old_A)==old_expected, 'old metadata ledger '+name)
            comparison={'old_M':old_M,'old_A':old_A,'saved_M':old_M-M,'saved_A':old_A-A}
        checked[name]={'rows':len(rows),'M':M,'A':A,'positive_witnesses':len(witnesses),
                       'residuals':len(residuals),'degree_mathematical_not_array_evaluation':p['exact_degree'],
                       'all_literal_rows_reconstructed':True,'all_ports_rows_live':True,'comparison':comparison}
    require(len(checked)==14 and sum(p['rows'] for p in checked.values())==368, 'complete census')
    result={'schema':'independent-markov-positive-guard-structural-review-v1',
            'metadata_helper_sha256':digest(Path(__file__).read_bytes()),'author':author,'dependencies':dependencies,
            'packets':checked,'totals':{'arrays':14,'rows':368},
            'scope':{'author_or_predecessor_execution_import':False,'array_evaluation':False,
                     'metadata_code_new_before_freeze':True,'saved_coefficient_tables_recomputed':False,
                     'finite_numerical_tests_replayed':False,'proof_review':'companion Markdown'},'status':'PASS'}
    with args.output.open('x', encoding='utf-8') as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({'status':'PASS','arrays':14,'rows':368}))

if __name__ == '__main__':
    main()
