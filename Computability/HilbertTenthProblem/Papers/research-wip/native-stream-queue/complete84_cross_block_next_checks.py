#!/usr/bin/env python3
"""Fresh data-only check of a tied outer rewrite and a monomial boundary.

No predecessor program is imported or executed. This is not a circuit search.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PIN = '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def sparse_add(a, b, sign=1):
    r = dict(a)
    for e, c in b.items():
        r[e] = r.get(e, 0) + sign*c
    return {e: c for e, c in r.items() if c}

def sparse_mul(a, b):
    r = {}
    for e, c in a.items():
        for f, d in b.items():
            g = tuple(x+y for x, y in zip(e, f))
            r[g] = r.get(g, 0) + c*d
    return {e: c for e, c in r.items() if c}

def check_graph(source, free):
    available = set(free)
    names = set()
    byname = {}
    for row in source:
        name, op, a, b = row
        need(name not in available and op in ('+', '-', '*'), 'bad row')
        need(all(isinstance(x, int) or x in available for x in (a, b)), 'unpaid operand')
        available.add(name)
        names.add(name)
        byname[name] = row
    live = set()
    pending = ['polynomial']
    while pending:
        name = pending.pop()
        if name in live:
            continue
        live.add(name)
        if name in byname:
            pending.extend(x for x in byname[name][2:] if isinstance(x, str))
    need(names <= live and set(free) <= live, 'dead row or input')
    counts = Counter(row[1] for row in source)
    return {'rows': len(source), 'M': counts['*'], 'A': counts['+']+counts['-'], 'live_rows': len(names), 'live_free': len(free)}

def token_evaluation(source, free, cut):
    values = {name: ('input', name) for name in free}
    for name, op, a, b in source:
        va = ('constant', a) if isinstance(a, int) else values[a]
        vb = ('constant', b) if isinstance(b, int) else values[b]
        values[name] = ('proven_local_cut', name) if name == cut else (op, va, vb)
    return values

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output')
    parser.add_argument('--expect')
    args = parser.parse_args()
    raw = (ROOT/'complete84_scaled_strong_output.json').read_bytes()
    need(sha(raw) == PIN, 'parent pin')
    packet = json.loads(raw)['packet']
    source = packet['source']
    expected_old = [
        ['Lm1', '-', 'Lbig', 1],
        ['rproduct', '*', 'gap', 'Lm1'],
        ['qMF', '*', 'q', 'MF'],
        ['mask_factor', '+', 'MC', 'qMF'],
        ['mask', '*', 'mask_factor', 'Jrep'],
        ['r_lhs', '+', 'rproduct', 'mask'],
    ]
    need(source[53:59] == expected_old, 'literal old outer cut')
    need(source[1:4] == [['repunit', '*', 'Bm1', 'Jrep'], ['q', '+', 'repunit', 1], ['Lbig', '*', 'q', 'q']], 'actual q binding')
    replacement = [
        ['cross_mask_t', '*', 'Bm1', 'gap'],
        ['cross_mask_u', '+', 'cross_mask_t', 'MF'],
        ['cross_mask_v', '*', 'q', 'cross_mask_u'],
        ['cross_mask_w', '+', 'cross_mask_t', 'MC'],
        ['cross_mask_sum', '+', 'cross_mask_v', 'cross_mask_w'],
        ['r_lhs', '*', 'Jrep', 'cross_mask_sum'],
    ]
    child = source[:53] + replacement + source[59:]
    parent_ledger = check_graph(source, packet['free'])
    child_ledger = check_graph(child, packet['free'])
    need(parent_ledger == child_ledger == {'rows':84, 'M':47, 'A':37, 'live_rows':84, 'live_free':25}, 'full ledger')
    # Exact local expansion in Z[m,J,g,MC,MF]; g is the actual paid gap.
    zero = (0,)*5
    one = {zero:1}
    variables = [{tuple(int(j == k) for j in range(5)):1} for k in range(5)]
    m, J, g, mc, mf = variables
    q = sparse_add(sparse_mul(m, J), one)
    old = sparse_add(sparse_mul(g, sparse_add(sparse_mul(q,q),one,-1)), sparse_mul(J,sparse_add(mc,sparse_mul(q,mf))))
    t = sparse_mul(m,g)
    new = sparse_mul(J, sparse_add(sparse_mul(q,sparse_add(t,mf)),sparse_add(t,mc)))
    need(old == new, 'exact outer polynomial identity')
    # The cut is justified above on the actual q definition, not an unbound digest.
    pv = token_evaluation(source, packet['free'], 'r_lhs')
    cv = token_evaluation(child, packet['free'], 'r_lhs')
    common = sorted(set(pv) & set(cv))
    need(all(pv[x] == cv[x] for x in common), 'full unchanged-source induction')
    # Independent monomial exponent expansion at paid q,k,w,s,h.
    monomials = {name:tuple(int(j == k) for j in range(5)) for k,name in enumerate(['q','R10b','w','s','h'])}
    row_ids = [4,5,6,7,8,10,11,50]
    selected = [source[j-1] for j in row_ids]
    for name, op, a, b in selected:
        need(op == '*' and a in monomials and b in monomials, 'monomial cut binding')
        monomials[name] = tuple(x+y for x,y in zip(monomials[a],monomials[b]))
    target_names = ['Lbig','wn2','sn2','UM','ksn2','first_root_base','hpm1']
    exponents = [monomials[x] for x in target_names]
    need(len(set(exponents)) == 7, 'distinct targets')
    target_y = monomials['sn2']
    possible = [zero] + [monomials[x] for x in ['q','R10b','w','s','h']] + [monomials[x] for x in target_names if x != 'sn2']
    pairs = [(a,b) for a in possible for b in possible if tuple(x+y for x,y in zip(a,b)) == target_y]
    need(not pairs, 'target Y has no pair of paid leaves/other targets')
    receipt = {
        'scope': 'Data-only source reconstruction and exact local algebra; no original compiler or helper execution; monomial lower bound requires the separate proof.',
        'helper_sha256': sha(Path(__file__).read_bytes()),
        'parent_json_sha256': PIN,
        'parent_ledger': parent_ledger,
        'child_ledger': child_ledger,
        'witnesses': packet['witnesses'],
        'free': packet['free'],
        'full_tied_source': child,
        'local_identity_expansion': [[list(e),c] for e,c in sorted(old.items())],
        'common_values_equal_by_local_identity_and_row_induction':len(common),
        'monomial_paid_order':['q','R10b','w','s','h'],
        'monomial_source_row_numbers':row_ids,
        'monomial_targets':dict(zip(target_names,exponents)),
        'Y_factor_pairs_from_leaves_and_other_targets':pairs,
        'lower_bound_scope':'Multiplication-only with these five paid monomial cuts and scalar constants, all seven target values retained; no outside donors, addition, subtraction or division.'
    }
    encoded = json.dumps(receipt, indent=2, sort_keys=True)+'\n'
    if args.output:
        with open(args.output, 'x') as stream:
            stream.write(encoded)
    if args.expect:
        need(Path(args.expect).read_text() == encoded, 'receipt mismatch')
    print('PASS: exact 84-row tie, all 84 rows/25 ports live, 104 common values, seven-target factor obstruction')

if __name__ == '__main__':
    main()
