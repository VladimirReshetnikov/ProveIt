#!/usr/bin/env python3
"""Literal fixed-marker Diophantine circuits; no predecessor code is executed.

The six compiler numerals have a separate semantic contract in the report.
This program verifies arithmetic source structure and algebraic degree evidence,
not the existence/nonexistence of halting witnesses or a ZFC proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

BASE_SHA256 = '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
COMMIT = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
CONSTANTS = ['Bm1', 'Kconstant', 'MC', 'MF', 'W0', 'W0plus2d']
DELETE = {'scaled_t', 'odd_index', 'gamma_sum', 'W', 'index_product',
          'index_rhs', 'difference_multiple', 'exponent_partial',
          'modulus_multiple', 'exponent_rhs', 'mu2', 'kappa2',
          'scaled_kappa2', 'norm_input', 'norm_triple'}
FACTORS = ['norm_first', 'norm_main', 'norm_aux', 'norm_index',
           'norm_transport', 'norm_strong']


def require(p, message):
    if not p:
        raise ValueError(message)


def ledger(rows):
    c = Counter(row[1] for row in rows)
    return {'operations': len(rows), 'multiplications': c['*'],
            'additions_subtractions': c['+'] + c['-']}


def closure(rows, targets):
    definitions = {row[0]: row for row in rows}
    live = set()
    def visit(n):
        if isinstance(n, str) and n in definitions and n not in live:
            live.add(n)
            visit(definitions[n][2]); visit(definitions[n][3])
    for n in targets:
        visit(n)
    return [row for row in rows if row[0] in live]


def check_graph(rows, free, targets):
    known = set(free)
    require(len(known) == len(free), 'duplicate free port')
    for n, op, a, b in rows:
        require(n not in known and op in ('+', '-', '*'), 'SSA or operation')
        require(all(type(v) is int or v in known for v in (a, b)), 'unbound operand')
        known.add(n)
    require(closure(rows, targets) == rows, 'dead instruction')
    used = {v for row in rows for v in row[2:] if isinstance(v, str)}
    used.update(v for v in targets if isinstance(v, str))
    require(set(free) <= used, 'dead supplied port')


def evaluate(rows, assignment):
    env = dict(assignment)
    def get(v):
        return v if type(v) is int else env[v]
    for n, op, a, b in rows:
        a, b = get(a), get(b)
        env[n] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def bound_rows():
    return [['bound_difference', '-', 'C_after_alpha', 'Z'],
            ['bound_error', '-', 'bound_difference', 'W0plus2d'],
            ['bound_error_square', '*', 'bound_error', 'bound_error'],
            ['bound_unit', '+', 'bound_error_square', 1]]


def fixed_base(parent):
    rows = []
    for name, op, a, b in parent['source']:
        if name in DELETE:
            continue
        if name == 'marked_rhs':
            op, a, b = '+', 'Z', 'W0'
        elif name == 'gam':
            a = 'gamma'
        elif name == 'norm_four':
            a = 'norm_pair'
        rows.append([name, op, a, b])
    require(len(rows) == 69, 'fixed base length')
    witnesses = [w for w in parent['witnesses'] if w not in ('delta', 'rho', 'sigma')]
    witnesses.append('gamma')
    require(len(witnesses) == 16, 'fixed witness count')
    return rows, witnesses


def change_auxiliary(rows, unscaled=False):
    out = []
    for name, op, a, b in rows:
        if unscaled and name == 'aux_coefficient_root':
            b = 'c2'  # now i*c^2, rather than Delta*i*c^2
        elif unscaled and name == 'scaled_f_square':
            b = 'R16'  # now Delta*(i*c^2)^2
        elif unscaled and name == 'norm_strong':
            a, b = 'L16', 'scaled_f_square'
        if name == 'L17':
            if unscaled:
                out.append(['auxiliary_Delta_f2', '*', 'A', 'L16'])
                out.append(['auxiliary_reduced_coefficient', '-', 'auxiliary_Delta_f2', 'A'])
            else:
                out.append(['auxiliary_reduced_coefficient', '-', 'scaled_f_square', 'A'])
            a = 'auxiliary_reduced_coefficient'
        if unscaled and name == 'polynomial':
            b = 1
        out.append([name, op, a, b])
    return out


def product_with_bound(rows, unscaled=False):
    require(rows[-1][0] == 'polynomial', 'finalizer')
    return rows[:-1] + bound_rows() + [
        ['bounded_product', '*', 'seven_units', 'bound_unit'],
        ['fixed_polynomial', '-', 'bounded_product', 1 if unscaled else 'A']]


def as_system(rows, witnesses, unscaled=False):
    equations = [[n, 1 if n != 'norm_strong' or unscaled else 'A'] for n in FACTORS]
    equations.append(['C_after_alpha', 'bound_rhs'])
    source = closure(rows, FACTORS + ['C_after_alpha'])
    source.append(['bound_rhs', '+', 'Z', 'W0plus2d'])
    return source, equations


NORM_TAIL = [
    ['ng_ic2','*','i','c2'], ['ng_Dminus1','*','ng_ic2','aux_coefficient_root'],
    ['ng_D','+','ng_Dminus1',1], ['ng_RD','*','r_lhs','ng_D'],
    ['ng_b','+','R10a','ng_RD'], ['ng_u','*','R10a','auxiliary_quotient'],
    ['ng_u2','*','ng_u','ng_u'], ['ng_p','*','ng_D','ng_u2'],
    ['ng_b2','*','ng_b','ng_b'], ['ng_P4a','*','norm_pair','norm_index'],
    ['ng_P4','*','ng_P4a','norm_transport'], ['ng_sum','+','ng_p','ng_b2'],
    ['ng_gap','-','ng_sum','aux_y2'], ['ng_Qgap','*','R16','ng_gap'],
    ['ng_Aplus1','+','ng_Qgap','aux_y2'], ['ng_A','-','ng_Aplus1',1],
    ['ng_Qp','*','R16','ng_p'], ['ng_Qb2','*','R16','ng_b2'],
    ['ng_cross','*','ng_Qp','ng_Qb2'], ['ng_four','*',4,'ng_cross'],
    ['ng_A2','*','ng_A','ng_A'], ['ng_K','-','ng_A2','ng_four'],
    ['ng_unit','+','ng_K',1], ['ng_product','*','ng_P4','ng_unit']]

OUTER_TAIL = [
    ['er_ic2','*','i','c2'], ['er_kS','*','er_ic2','aux_coefficient_root'],
    ['er_D','+','er_kS',1], ['er_RD','*','r_lhs','er_D'],
    ['er_b','+','R10a','er_RD'], ['er_u','*','R10a','auxiliary_quotient'],
    ['er_u2','*','er_u','er_u'], ['er_p','*','er_D','er_u2'],
    ['er_b2','*','er_b','er_b'], ['er_P4a','*','norm_pair','norm_index'],
    ['er_P4','*','er_P4a','norm_transport'],
    ['er_P','*','er_P4','bound_unit'],
    ['er_C','*','er_P','R16'], ['er_L','*','er_C','er_p'],
    ['er_M','*','er_C','er_b2'], ['er_Pc','-','er_P','er_C'],
    ['er_Z','*','er_Pc','aux_y2'], ['er_LM','+','er_L','er_M'],
    ['er_LMZ','+','er_LM','er_Z'], ['er_alpha','-','er_LMZ',1],
    ['er_alpha2','*','er_alpha','er_alpha'], ['er_prod','*','er_L','er_M'],
    ['er_four','*',4,'er_prod'], ['fixed_polynomial','-','er_alpha2','er_four']]


def root_deleted(rows):
    dependent = {'f'}
    out = []
    for row in rows:
        if any(v in dependent for v in row[2:] if isinstance(v, str)):
            dependent.add(row[0])
        else:
            out.append(row)
    # Bound-comparison producers were formerly used only by the input bridge.
    return out


def degree_upper(rows, witnesses):
    """A proved main-norm cancellation is the sole nontrivial rewrite."""
    d = {w: 1 for w in witnesses} | {c: 0 for c in CONSTANTS}
    definitions = {r[0]: r for r in rows}
    require(definitions['norm_main'] == ['norm_main','-','L15','Ac2'], 'main norm binding')
    for name, op, a, b in rows:
        da = 0 if type(a) is int else d[a]
        db = 0 if type(b) is int else d[b]
        d[name] = da+db if op == '*' else max(da, db)
        if name == 'norm_main':
            # (X+a*c+g)^2-(a^2+H)c^2
            # = X^2+2Xg+g^2+2acX+2acg-Hc^2.
            d[name] = max(2*d['wn2'], d['wn2']+d['gam'], 2*d['gam'],
                          d['R12']+d['R10a']+d['wn2'],
                          d['R12']+d['R10a']+d['gam'], d['a4m5']+2*d['R10a'])
    return d


def line_degree(rows, witnesses, targets, modulus=1000000007):
    """Full univariate source evaluation, as supplementary algebra evidence."""
    constants = dict(Bm1=15, Kconstant=37, MC=11, MF=23, W0=256, W0plus2d=264)
    env = {w: [i+1, 2*i+3] for i, w in enumerate(witnesses)}
    env.update({c: [v] for c, v in constants.items()})
    def get(a):
        return [a % modulus] if type(a) is int else env[a]
    for name, op, a, b in rows:
        a, b = get(a), get(b)
        if op == '*':
            result = [0]*(len(a)+len(b)-1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    result[i+j] = (result[i+j]+x*y) % modulus
        else:
            result = [0]*max(len(a),len(b))
            for i,x in enumerate(a): result[i] = x
            sign = 1 if op == '+' else -1
            for i,y in enumerate(b): result[i] = (result[i]+sign*y) % modulus
        while len(result)>1 and result[-1] == 0: result.pop()
        env[name] = result
    return {n: {'degree': len(env[n])-1, 'leading_coefficient': env[n][-1]} for n in targets}


def make_packet(name, source, witnesses, output=None, equations=None, degree=None):
    targets = [output] if output else [v for eq in equations for v in eq if isinstance(v,str)]
    check_graph(source, witnesses+CONSTANTS, targets)
    ds = degree_upper(source, witnesses)
    diagnostics = line_degree(source, witnesses, [output] if output else FACTORS)
    if output:
        require(ds[output] == degree, name + ' symbolic degree bound')
        require(diagnostics[output]['degree'] == degree, name + ' full source diagnostic degree')
    return {'name': name, 'source_commit': COMMIT,
            'witnesses': witnesses, 'witness_domain': 'strictly positive integers',
            'fixed_numerals': CONSTANTS, 'source': source, 'output': output,
            'equations': equations, 'ledger': ledger(source),
            'exact_degree': degree, 'degree_upper_by_register': ds,
            'supplementary_full_source_degree_diagnostic': diagnostics,
            'diagnostic_scope': 'Arbitrary small numeral slice: an algebra check, not a valid compiler instance or a halting witness.',
            'intermediate_domain': 'Signed integer polynomial abbreviations; intermediate registers are not extra existential variables.'}


def build(parent):
    base, witnesses = fixed_base(parent)
    reduced = change_auxiliary(base)
    lowdegree = change_auxiliary(base, unscaled=True)
    packets = {}
    for name, rows, unscaled, deg in [
        ('fixed16_product74_degree157',base,False,157),
        ('fixed16_product75_degree125',reduced,False,125),
        ('fixed16_product76_degree113',lowdegree,True,113)]:
        packets[name] = make_packet(name, product_with_bound(rows,unscaled), witnesses,
                                    output='fixed_polynomial', degree=deg)
    system, eqs = as_system(lowdegree, witnesses, True)
    name = 'fixed16_system66_degree34'
    packets[name] = make_packet(name, system, witnesses, equations=eqs)
    packets[name]['maximum_equation_degree'] = max(max(
        0 if type(v) is int else packets[name]['degree_upper_by_register'][v] for v in eq) for eq in eqs)
    require(packets[name]['maximum_equation_degree'] == 34, 'system equation degree')
    sos = list(system)
    for j,(a,b) in enumerate(eqs):
        sos += [[f'residual{j}','-',a,b],[f'square{j}','*',f'residual{j}',f'residual{j}']]
    prior = 'square0'
    for j in range(1,len(eqs)):
        sos.append([f'sum{j}','+',prior,f'square{j}']); prior=f'sum{j}'
    name = 'fixed16_sos86_degree68'
    packets[name] = make_packet(name,sos,witnesses,output=prior,degree=68)
    root_free = root_deleted(base)
    witnesses15 = [w for w in witnesses if w != 'f']
    name = 'fixed15_product82_degree295'
    source = root_free + NORM_TAIL + bound_rows() + [
        ['ng_bounded_product','*','ng_product','bound_unit'],
        ['fixed_polynomial','-','ng_bounded_product',1]]
    packets[name] = make_packet(name,source,witnesses15,output='fixed_polynomial',degree=295)
    name = 'fixed15_outer80_degree346'
    source = root_free + bound_rows() + OUTER_TAIL
    packets[name] = make_packet(name,source,witnesses15,output='fixed_polynomial',degree=346)
    expected = { 'fixed16_product74_degree157':74, 'fixed16_product75_degree125':75,
                'fixed16_product76_degree113':76, 'fixed16_system66_degree34':66,
                'fixed16_sos86_degree68':86, 'fixed15_product82_degree295':82,
                'fixed15_outer80_degree346':80 }
    for name, count in expected.items():
        require(packets[name]['ledger']['operations'] == count, name+' operation count')
    return packets


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    raw=(root/'upstream_complete84.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==BASE_SHA256,'upstream source checksum')
    packets=build(json.loads(raw)['packet'])
    for name,packet in packets.items():
        target=root/(name+'.json')
        if args.write:
            target.write_text(json.dumps(packet,indent=2)+'\n')
        else:
            require(json.loads(target.read_text())==packet,'receipt mismatch: '+name)
    print(json.dumps({'status':'PASS','scope':'Literal arithmetic source, live dependencies, operation counts and degree diagnostics; semantic proof is in the report.',
                      'circuits':{n:dict(witnesses=len(p['witnesses']),**p['ledger'],degree=p['exact_degree'],equations=len(p['equations']) if p['equations'] else 1) for n,p in packets.items()}},indent=2))


if __name__=='__main__':
    main()
