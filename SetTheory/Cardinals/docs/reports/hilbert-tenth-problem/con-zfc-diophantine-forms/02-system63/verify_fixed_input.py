#!/usr/bin/env python3
"""Exact source/identity checks for the fixed-input73 construction.

This does not decide consistency, instantiate a valid compiler, or certify
the imported universal-machine theorem. It verifies the new arithmetic DAG,
the all-value bridge identity, operation counts, and exact degree witness.
"""
import collections
import hashlib
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def evaluate(source, values):
    state = dict(values)
    for out, op, left, right in source:
        a = state[left] if isinstance(left, str) else left
        b = state[right] if isinstance(right, str) else right
        require(out not in state, 'duplicate output: ' + out)
        state[out] = {'+': lambda: a+b, '-': lambda: a-b,
                      '*': lambda: a*b}[op]()
    return state

def add(a, b, sign=1):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += sign*v
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def mul(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def diagonal(source, witnesses, constants):
    state = {k:[v] for k,v in constants.items()}
    state.update({k:[0,1] for k in witnesses})
    for out, op, left, right in source:
        a = state[left] if isinstance(left,str) else [left]
        b = state[right] if isinstance(right,str) else [right]
        state[out] = mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    return state

def validate_source(packet, outputs):
    source = packet['source']
    known = set(packet['fixed_numerals'] + packet['witnesses'])
    for out, op, left, right in source:
        require(op in ['+','-','*'], 'non-polynomial operation')
        require(out not in known, 'duplicate register')
        for arg in [left,right]:
            require(type(arg) is int or (type(arg) is str and arg in known),
                    'missing producer or invalid literal')
        known.add(out)
    live = set(outputs)
    for row in reversed(source):
        if row[0] in live:
            live.update(v for v in row[2:] if isinstance(v,str))
    require(all(row[0] in live for row in source),'dead gate')
    require(all(v in live for v in packet['witnesses']),'dead witness')
    require(all(v in live for v in packet['fixed_numerals']),'dead constant')
    count = collections.Counter(row[1] for row in source)
    actual = {'multiplication':count['*'],
              'addition_subtraction':count['+']+count['-'], 'total':len(source)}
    require(actual==packet['operations'],'wrong operation count')
    return actual

def main():
    old_bytes=(HERE/'complete84_scaled_strong_output.json').read_bytes()
    old_git_blob=hashlib.sha1(b'blob '+str(len(old_bytes)).encode()+b'\0'+old_bytes).hexdigest()
    require(old_git_blob=='a8e6e50e96503e69221b8586e273208e5345eee4',
            'pinned upstream F84 source receipt changed')
    old = json.loads(old_bytes)['packet']
    new = json.loads((HERE/'fixed_input73.json').read_text())
    system = json.loads((HERE/'fixed_input63_system.json').read_text())
    deleted=set('gamma_sum scaled_t W odd_index index_product index_rhs '
        'difference_multiple exponent_partial modulus_multiple exponent_rhs '
        'mu2 kappa2 scaled_kappa2 norm_input norm_triple'.split())
    replacements={'gamma_sum':'gamma','norm_triple':'norm_pair'}
    expected_source=[]
    for row in old['source']:
        if row[0] in deleted: continue
        row=[row[0],row[1],replacements.get(row[2],row[2]),replacements.get(row[3],row[3])]
        if row[0]=='marked_rhs': row=['marked_rhs','+','Z','W0']
        if row[0]=='polynomial':
            expected_source.extend([
                ['marker_difference','-','C_after_alpha','marked_rhs'],
                ['marker_square','*','marker_difference','marker_difference'],
                ['marker_unit','+','marker_square',1],
                ['all_with_marker','*','seven_units','marker_unit']])
            row=['polynomial','-','all_with_marker','A']
        expected_source.append(row)
    require(new['source']==expected_source, 'literal parent source transformation differs')
    require(new['witnesses']==[v for v in old['witnesses']
        if v not in ['delta','rho','sigma']]+['gamma'], 'wrong witness interface')
    require(new['fixed_numerals']==['Bm1','Kconstant','MC','MF','W0'], 'wrong numeral interface')
    ledger = validate_source(new,['polynomial'])
    system_ledger = validate_source(system,
        [v for pair in system['comparisons'] for v in pair if isinstance(v,str)])
    require(len(new['witnesses'])==16, 'wrong witness count')
    rng = random.Random(20261022)
    for trial in range(64):
        v = {k:rng.randrange(-4,8) for k in old['free']}
        v['x']=1
        o=evaluate(old['source'],v)
        w={k:v[k] for k in new['fixed_numerals']+new['witnesses'] if k not in ['gamma','W0']}
        w['gamma']=v['rho']+v['sigma']
        w['alpha']=v['alpha']+v['twice_cell_bits']
        w['W0']=rng.randrange(-4,8)
        n=evaluate(new['source'],w)
        require(n['A']==o['A'],'discriminant mismatch')
        require(n['norm_transport']-o['norm_transport']
                == (v['Kconstant']+v['w'])*(n['marked_rhs']-o['marked_rhs']),
                'transport substitution identity fails')
        require(o['norm_input']*o['norm_transport']*(n['polynomial']+n['A'])
                == n['marker_unit']*n['norm_transport']*(o['polynomial']+o['A']),
                'full-source cross-product identity fails')
        s=evaluate(system['source'],w)
        require(all(s[k]==n[k] for k in s),'system source differs')
    constants={'Bm1':15,'Kconstant':11,
               'MC':2,'MF':19,'W0':8192}
    d=diagonal(new['source'],new['witnesses'],constants)
    expected=8*(2**13)*(15**91)*14*(11**2)
    require(len(d['polynomial'])-1==157,'wrong diagonal degree')
    require(d['polynomial'][-1]==expected,'wrong diagonal leader')
    require([len(d[k])-1 for k in ['norm_first','norm_main','norm_aux',
            'norm_index','norm_transport','norm_strong','marker_unit']]
            ==[22,18,60,7,2,46,2], 'wrong factor degrees')
    result={'status':'pass','polynomial_ledger':ledger,
            'upstream_f84_git_blob':old_git_blob,
            'seven_equation_ledger':system_ledger,'positive_unknowns':16,
            'signed_whole_source_identity_fixtures':64,
            'exact_diagonal_degree':157,
            'diagonal_leading_coefficient':str(expected),
            'diagnostic_constants_are_not_a_compiled_ZFC_program':True,
            'scope':'Arithmetic source checks; uniform degree proof and semantic theorem are in the note.',
            'source_sha256':hashlib.sha256((HERE/'fixed_input73.json').read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
