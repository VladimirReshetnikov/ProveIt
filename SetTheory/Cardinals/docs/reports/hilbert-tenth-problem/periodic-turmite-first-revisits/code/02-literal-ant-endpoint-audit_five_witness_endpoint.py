#!/usr/bin/env python3
"""Construct new five-witness alternatives; never overwrite prior artifacts."""
from pathlib import Path
import hashlib
import json
import audit_endpoint as original

ROOT = Path(__file__).resolve().parent
PRESERVE = [
    'ENDPOINT_AUDIT.md', 'FOLDED_ENDPOINT_ADDENDUM.md', 'audit_endpoint.py',
    'audit_folded_endpoint.py', 'endpoint_audit_receipt.json',
    'endpoint_fixed_numerals_source.json', 'endpoint_paid_numerals_source.json',
    'endpoint_folded_fixed_numerals_source.json',
    'endpoint_folded_paid_numerals_source.json', 'folded_endpoint_audit_receipt.json',
]


def source(paid):
    gates = []
    if paid:
        K, C, PU = original.constant_chain(gates)
        D = original.add_gate(gates, 'DBuild', 'sub', C, '1')
        fixed = {}
    else:
        K, C, D, PU = 'K', 'C', 'D', None
        fixed = {
            'K': {'base': 3, 'exponent': original.X_RESIDUE},
            'C': {'base': 3, 'exponent': original.U_PERIOD, 'subtract': 1},
            'D': {'base': 3, 'exponent': original.U_PERIOD, 'subtract': 2},
        }
    const_end = len(gates)
    T, A = original.variable_chain(gates)
    power_end = len(gates)
    g = lambda out, op, left, right: original.add_gate(gates, out, op, left, right)
    hleft = g('HorizontalLeft', 'add', 'U', D)
    hright = g('HorizontalRight', 'mul', C, 'Uq')
    aminus = g('AMinusOne', 'sub', A, '1')
    vminus = g('VMinusOne', 'sub', 'V', '1')
    vleft = g('VerticalLeft', 'add', vminus, aminus)
    vright = g('VerticalRight', 'mul', aminus, 'Vq')
    acol = g('Acol', 'mul', K, 'U')
    col = g('ColumnBound', 'add', acol, 'BoundCol')
    at = g('AT', 'mul', acol, T)
    head = g('EndpointHead', 'mul', at, 'V')
    return {
        'model': 'five_positive_witnesses_' + ('paid_constant_construction' if paid else 'free_fixed_numeral_ports'),
        'literal_ports': ['1', '3'] if paid else ['1'],
        'fixed_numeral_recipes': fixed,
        'existing_relation_ports': ['W', 'FinalHead', 'FinalSignPlus'],
        'new_positive_witnesses': ['U', 'V', 'Uq', 'Vq', 'BoundCol'],
        'gates': gates,
        'equalities': [[hleft, hright], [vleft, vright], [col, 'W'], [head, 'FinalHead'], ['FinalSignPlus', '1']],
        'section_ends': [const_end, power_end, len(gates)],
        'power_targets': {'K': K, 'ThreeToU': PU, 'T': T, 'WToV': A},
        'source_semantics': 'Gate outputs are arithmetic expressions, not quantified witnesses. Equalities are free in this component operation ledger.',
    }


# Exact sparse formal polynomials in actual variables W,U,V,Uq,Vq,
# BoundCol,FinalHead,FinalSignPlus followed by two coefficient symbols K,C.
# D is replaced by C-1; the last two symbols are excluded from variable degree.
VARS = ['W','U','V','Uq','Vq','BoundCol','FinalHead','FinalSignPlus','K','C']
N = len(VARS)
Z = (0,)*N


def integer(n):
    return {Z:n} if n else {}


def variable(i):
    e = [0]*N
    e[i] = 1
    return {tuple(e):1}


def add(p,q,sign=1):
    out = dict(p)
    for mon, coef in q.items():
        out[mon] = out.get(mon,0)+sign*coef
        if out[mon] == 0:
            del out[mon]
    return out


def mul(p,q):
    out = {}
    for m,c in p.items():
        for n,d in q.items():
            mon = tuple(x+y for x,y in zip(m,n))
            out[mon] = out.get(mon,0)+c*d
    return {m:c for m,c in out.items() if c}


def Wpower(e):
    mon = [0]*N
    mon[0] = e
    return {tuple(mon):1}


def check_formal_polynomials(src):
    v = {name:variable(i) for i,name in enumerate(VARS)}
    v['1'] = integer(1)
    v['D'] = add(v['C'],v['1'],-1)
    a, _, _ = src['section_ends']
    if a:
        # The independent exponent pass checks the fixed power construction.
        v[src['power_targets']['K']] = v['K']
        v['CBuild'] = v['C']
        v['DBuild'] = v['D']
        assert src['gates'][a-1] == {'out':'DBuild','op':'sub','args':['CBuild','1']}
    for gate in src['gates'][a:]:
        left,right = [v[n] for n in gate['args']]
        if gate['op']=='mul':
            result = mul(left,right)
        else:
            result = add(left,right,1 if gate['op']=='add' else -1)
        v[gate['out']] = result
    residuals = [add(v[l],v[r],-1) for l,r in src['equalities']]
    # Independently specified five polynomials, using V+A-2 as the vertical
    # left side rather than the source's (V-1)+(A-1) evaluation order.
    expected = [
        add(add(v['U'],v['D']),mul(v['C'],v['Uq']),-1),
        add(add(add(v['V'],Wpower(original.V_PERIOD)),integer(2),-1),
            mul(add(Wpower(original.V_PERIOD),integer(1),-1),v['Vq']),-1),
        add(add(mul(v['K'],v['U']),v['BoundCol']),v['W'],-1),
        add(mul(mul(mul(v['K'],v['U']),Wpower(original.Y_RESIDUE)),v['V']),v['FinalHead'],-1),
        add(v['FinalSignPlus'],integer(1),-1),
    ]
    assert residuals == expected
    degrees = [max(sum(mon[:8]) for mon in p) for p in residuals]
    assert degrees == [1,576001,1,29950,1]
    return {
        'formal_residuals_match_independent_five_equations':True,
        'expanded_equation_degrees_excluding_fixed_numerals':degrees,
        'maximum_expanded_equation_degree':max(degrees),
        'formal_residual_term_counts':[len(p) for p in residuals],
    }


def main():
    preserved = {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in PRESERVE}
    audits = {}
    created = []
    for label, paid in [('fixed_numerals',False),('paid_numerals',True)]:
        src = source(paid)
        result = original.check_source(src)
        result.update(check_formal_polynomials(src))
        result['new_positive_witnesses'] = 5
        result['asserted_equalities'] = 5
        assert result['total'] == ({'M':94,'A':7,'total':101} if paid else {'M':37,'A':5,'total':42})
        name = f'endpoint_five_witness_{label}_source.json'
        # Reproducible reruns may verify an existing new artifact, but never
        # replace it (nor any predecessor) with different bytes.
        encoded = json.dumps(src,indent=2)+'\n'
        path = ROOT/name
        if path.exists():
            assert path.read_text() == encoded
        else:
            path.write_text(encoded)
        created.append(name)
        audits[label] = result
    checks = 0
    for u in [2,4,6]:
        C, D = 3**u-1, 3**u-2
        for w in [3,5]:
            W = 3**w
            for v in [2,4]:
                A = W**v
                for Uq in range(1,5):
                    for Vq in range(1,5):
                        U = C*(Uq-1)+1
                        V = (A-1)*(Vq-1)+1
                        assert U>0 and V>0
                        assert U+D == C*Uq
                        assert V+A-2 == (A-1)*Vq
                        assert (U==1) == (Uq==1)
                        assert (V==1) == (Vq==1)
                        checks += 1
    assert {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in PRESERVE} == preserved
    report = {
        'audits':audits,
        'witness_correspondence_regression_cases':checks,
        'predecessor_and_folded_files_unchanged':preserved,
        'scope':'Endpoint equations only. Gate outputs are expressions; equalities are free; degrees exclude fixed numeral ports.',
        'upstream_code_executed':False,
        'giant_powers_materialized':False,
        'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in created+['audit_five_witness_endpoint.py']},
    }
    name = ROOT/'five_witness_endpoint_audit_receipt.json'
    encoded = json.dumps(report,indent=2)+'\n'
    if name.exists():
        assert name.read_text() == encoded
    else:
        name.write_text(encoded)
    print(encoded)

if __name__=='__main__':
    main()
