#!/usr/bin/env python3
"""Pinned-data independent-gamma83 source/fiber scout; no predecessor execution."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from math import gcd, lcm
from pathlib import Path

PINS = {
  "complete84_scaled_strong_output.py": "8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737",
  "complete84_scaled_strong_output.json": "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf",
  "complete84_scaled_strong_output.md": "01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade",
  "complete85_auxiliary_bezout_projection.md": "d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b",
  "review_complete85_auxiliary_bezout_math.md": "77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d",
  "review_complete85_auxiliary_bezout_source.md": "d8e8720f5287ef1069ce46f52369c532fb551d9611935065aa56210295ab2cd9",
  "review_complete74_asymmetric_scale_math.md": "a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58",
  "complete75_independent_gamma87_alias.md": "cff7a7e69fcb681e2b7368028f6e38ba975370ed5e2facafdfa8b4b179b0dbfb",
  "complete75_independent_gamma87_alias.json": "49de79c91457284c7d4cac7ec02fc839e88afcc29e082ae80c659b22236274c9",
  "complete75_independent_gamma87_period.md": "dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784",
  "complete75_independent_gamma87_period.json": "4546ed7c0d750a20a5bef73e8a9a6ec7ba1c386f4b40fed87c8ae787f9d7f054",
  "complete75_gamma87_compiler_order_filters.md": "43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3"
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def sha(data):
    return hashlib.sha256(data).hexdigest()

def value(x, env):
    return env[x] if isinstance(x, str) else x

def evaluate(rows, env):
    env = dict(env)
    for dst, op, a, b in rows:
        x, y = value(a, env), value(b, env)
        env[dst] = x*y if op == '*' else x+y if op == '+' else x-y
    return env

def layout(rows, free, output):
    seen = set(free)
    definitions = {}
    for row in rows:
        need(type(row) is list and len(row) == 4, 'row shape')
        dst, op, a, b = row
        need(dst not in seen and op in ('+', '-', '*'), 'row definition')
        for port in (a, b):
            need(type(port) is int or type(port) is str and port in seen, 'unknown port')
        seen.add(dst)
        definitions[dst] = (a, b)
    live = set()
    def visit(port):
        if not isinstance(port, str) or port in live:
            return
        live.add(port)
        for dep in definitions.get(port, ()):
            visit(dep)
    visit(output)
    need(live == seen, 'dead gate or free port')
    m = sum(row[1] == '*' for row in rows)
    return {'M': m, 'A': len(rows)-m, 'total': len(rows),
            'live_gates': len(definitions), 'live_free': len(free)}

def pnorm(p, mod):
    p = [v % mod for v in p]
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p

def pop(op, a, b, mod):
    if op != '*':
        out = [0]*max(len(a), len(b))
        for i, x in enumerate(a): out[i] += x
        for i, x in enumerate(b): out[i] += x if op == '+' else -x
    else:
        out = [0]*(len(a)+len(b)-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): out[i+j] += x*y
    return pnorm(out, mod)

def poly_eval(rows, initial, mod):
    env = dict(initial)
    for dst, op, a, b in rows:
        env[dst] = pop(op, env[a] if isinstance(a, str) else [a],
                      env[b] if isinstance(b, str) else [b], mod)
    return env

def degrees(rows, free, numerals):
    env = {n: 0 if n in numerals else 1 for n in free}
    for dst, op, a, b in rows:
        x = env[a] if isinstance(a, str) else 0
        y = env[b] if isinstance(b, str) else 0
        env[dst] = x+y if op == '*' else max(x, y)
    return env

def pell(A, n):
    chi, psi = 1, 0
    D = A*A-1
    for _ in range(n):
        chi, psi = A*chi+D*psi, chi+A*psi
    return chi, psi

def period_checks():
    records = []
    comparisons = steps = 0
    for a in (6, 12, 18, 24, 30, 42, 48, 60):
        A, D, H = a+2, (a+1)*(a+3), 4*a+3
        powers, z = [], 1
        while z not in powers:
            powers.append(z)
            z = 2*z % H
        need(z == 1, 'power cycle')
        O = len(powers)
        g, L = gcd(2*D, O), lcm(2*D, O)
        us = (1, 3, 5, 7, 9, 11)
        observed = {u:set() for u in us}
        chi, psi, mod = 1, 0, D*H
        for v in range(L):
            E = (chi-a*psi) % H
            need(E == pow(2, v, H), 'Pell power residue')
            need(psi % D == (v if v % 2 else A*v) % D, 'Pell index residue')
            for u in us:
                if psi % D == u:
                    observed[u].add(E)
            chi, psi = (A*chi+D*psi) % mod, (chi+A*psi) % mod
        for u in us:
            predicted = {W for j,W in enumerate(powers) if (j-u) % g == 0 or (j-A*u) % g == 0}
            need(observed[u] == predicted, 'complete two-branch period test')
            for W in range(H):
                need((W in observed[u]) == (W in predicted), 'residue membership')
                comparisons += 1
            need(all(W % 3 == 2 for j,W in enumerate(powers) if (j-u) % g == 0), 'odd branch')
            need(all(W % 3 == 1 for j,W in enumerate(powers) if (j-A*u) % g == 0), 'even branch')
        steps += L
        records.append({'a':a, 'Delta':D, 'H':H, 'order':O, 'g':g, 'joint_period':L})
    fixtures = []
    for a in (6, 12):
        A, D, H = a+2, (a+1)*(a+3), 4*a+3
        for v in (5, 8, 11, 20):
            chi, psi = pell(A, v)
            u = psi % D
            if u % 2 == 0: u += D
            for signed in (False, True):
                W = pow(2,v,H) - (H if signed else 0)
                delta, r0 = divmod(psi-u, D)
                rho, r1 = divmod(chi-a*psi-W, H)
                need(not r0 and not r1 and min(u,delta,rho,chi,psi)>0, 'positive input completion')
                need(chi == W+a*(u+delta*D)+rho*H and chi*chi-D*psi*psi == 1, 'input norm')
                fixtures.append({'a':a,'v':v,'u':u,'W':W,'delta':str(delta),'rho':str(rho)})
    return {'small_parameter_scope':'Input components only; not compiler tuples or full zeros.',
            'periods':records,'recurrence_steps':steps,'residue_comparisons':comparisons,
            'positive_components':fixtures}

def verify(root):
    blobs = {}
    for name, pin in PINS.items():
        data = (root/name).read_bytes()
        need(sha(data) == pin, 'pin mismatch: '+name)
        blobs[name] = data
    parent = json.loads(blobs['complete84_scaled_strong_output.json'])['packet']
    old = parent['source']
    need(old[18] == ['gamma_sum','+','rho','sigma'], 'gamma producer')
    consumers = [row for row in old if 'gamma_sum' in row[2:]]
    need(consumers == [['gam','*','gamma_sum','a4m5']], 'private gamma consumer')
    rows = []
    for row in old:
        if row[0] == 'gamma_sum': continue
        rows.append([row[0],row[1],*['sigma' if x == 'gamma_sum' else x for x in row[2:]]])
    free = parent['free']
    ledger = layout(rows, free, parent['output'])
    need(ledger['total'] == 83 and ledger['M'] == 47 and ledger['A'] == 36, 'complete ledger')
    need(len(parent['witnesses']) == 18, 'witness interface')
    need(rows[-1] == ['polynomial','-','seven_units','A'], 'paid finalizer')
    finalizer_names = {'norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'}
    finalizer_rows = [r for r in rows if r[0] in finalizer_names]
    need(len(finalizer_rows) == 7 and sum(r[1] == '*' for r in finalizer_rows) == 6, 'all paid finalizer gates')
    ledger.update(core_M=41,core_A=35,core_total=76,finalizer_M=6,finalizer_A=1,finalizer_total=7)
    dependencies = {n:{n} for n in free}
    for dst,op,a,b in rows:
        dependencies[dst] = (dependencies[a] if isinstance(a,str) else set()) | (dependencies[b] if isinstance(b,str) else set())
    noninput_factors = [f for f in parent['factors'] if f != 'norm_input']
    need(all(not ({'rho','delta'} & dependencies[f]) for f in noninput_factors), 'private input coordinates')
    rho_consumers = [r for r in rows if 'rho' in r[2:]]
    delta_consumers = [r for r in rows if 'delta' in r[2:]]
    need(rho_consumers == [['modulus_multiple','*','rho','a4m5']], 'rho consumers')
    need(delta_consumers == [['index_product','*','delta','A']], 'delta consumers')
    retained = {r[0]:r for r in old if r[0] != 'gamma_sum'}
    for row in rows:
        expected = list(retained[row[0]])
        expected[2:] = ['sigma' if x == 'gamma_sum' else x for x in expected[2:]]
        need(row == expected, 'inductive whole-DAG equality')
    # The only exceptional induction premise is rho + (sigma-rho) = sigma.
    gamma_cut = {}
    for term in ({'rho':1}, {'sigma':1,'rho':-1}):
        for var, coefficient in term.items():
            gamma_cut[var] = gamma_cut.get(var,0)+coefficient
    gamma_cut = {var:c for var,c in gamma_cut.items() if c}
    need(gamma_cut == {'sigma':1}, 'linear cut')
    rational_cases = signed_cases = retained_values = 0
    numerals = parent['fixed_numerals']
    for case in range(48):
        env = {name: ((case+3)*(j+5) % 19)-9 for j,name in enumerate(free)}
        if case >= 24:
            env = {name:Fraction(v, (j%4)+1) for j,(name,v) in enumerate(env.items())}
            rational_cases += 1
        else: signed_cases += 1
        old_env = dict(env)
        old_env['sigma'] = env['sigma']-env['rho']
        child_values, parent_values = evaluate(rows,env), evaluate(old,old_env)
        for dst,op,a,b in rows:
            need(child_values[dst] == parent_values[dst], 'signed full pullback')
            retained_values += 1
    alias_values = 0
    for case in range(24):
        env = {name:((case+7)*(j+3) % 23)-11 for j,name in enumerate(free)}
        moved = dict(env)
        shift = case-13
        moved['x'] += shift
        moved['alpha'] -= env['twice_cell_bits']*shift
        moved['delta'] += case+2
        moved['rho'] -= case+3
        before, after = evaluate(rows,env), evaluate(rows,moved)
        for port in noninput_factors+['marked_rhs','W','r_lhs']:
            need(before[port] == after[port], 'exact alias cone preservation')
            alias_values += 1
    diagnostics = []
    for mod, constants in ((1000003,(3,5,6,3,2,7)),(1000033,(7,11,10,5,6,13))):
        initial = {n:[0,1] for n in free}
        for n,c in zip(numerals, constants): initial[n] = [c]
        child_poly = poly_eval(rows,initial,mod)
        initial_old = dict(initial)
        initial_old['sigma'] = pop('-', initial['sigma'],initial['rho'],mod)
        parent_poly = poly_eval(old,initial_old,mod)
        need(child_poly['polynomial'] == parent_poly['polynomial'], 'dense full pullback')
        factor_degrees = [len(child_poly[f])-1 for f in parent['factors']]
        need(factor_degrees == [22,18,32,60,7,2,46], 'exact factor diagnostics')
        need(len(child_poly['polynomial'])-1 == 187, 'degree attainment')
        diagnostics.append({'modulus':mod,'numerals':dict(zip(numerals,constants)),
                            'degree':187,'factor_degrees':factor_degrees,
                            'coefficients_sha256':sha(json.dumps(child_poly['polynomial']).encode())})
    upper = degrees(rows,free,numerals)['polynomial']
    need(upper == 197, 'naive degree bound')
    # A separate, simple formal leader calculation: the old leader is linear in rho+sigma.
    # The affine pullback replaces that sum by sigma. The transport term contributes
    # -transport_quotient*(B-1)*J, leaving an isolated nonzero monomial.
    packet = {'source':rows,'free':copy.deepcopy(free),'witnesses':copy.deepcopy(parent['witnesses']),
              'fixed_numerals':copy.deepcopy(numerals),'ordinary_input':parent['ordinary_input'],
              'output':parent['output'],'factors':copy.deepcopy(parent['factors']),
              'witness_domain':'strictly positive integers; sigma now means independent gamma',
              'ledger':ledger,'exact_degree':187,'naive_degree_upper':upper,
              'factor_exact_degrees':[22,18,32,60,7,2,46],
              'all_ring_pullback':'P83_gamma(sigma)=P84(sigma_old=sigma-rho)',
              'positive_forward_map':'sigma_new=rho+sigma_old; all other coordinates fixed',
              'positive_inverse':'Not valid on all positive zeros; sigma_old=sigma_new-rho can be negative.',
              'language_status':'UNRESOLVED; not a universal bound or a valid-compiler false-input construction.'}
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':dict(PINS),
            'scope':'One complete independent-gamma83 source and exact input-fiber theorem; ordinary-input language unresolved.',
            'packet':packet,'structural':{'removed_row':old[18],'only_consumer':consumers,
                    'inductive_retained_rows':len(rows),'all_free_and_gates_live':True,
                    'rho_consumers':rho_consumers,'delta_consumers':delta_consumers,
                    'six_noninput_factors_exclude_rho_delta':True,'paid_finalizer_rows':finalizer_rows},
            'algebra_checks':{'signed_cases':signed_cases,'rational_cases':rational_cases,
                             'retained_value_equalities':retained_values,'alias_cone_cases':24,'alias_cone_equalities':alias_values},
            'degree':{'uniform_leader':'32 Q^111 h sigma delta^2 i^4 (eta+zeta)^13 w^18 s^31 Nt_top T^2 f^2',
                      'witness_coefficient':'-32*(B-1)^112','exact':187,'naive_upper':upper,
                      'diagnostics':diagnostics},'input_period_checks':period_checks(),
            'full_compiler_zeros_materialized':0}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    args = parser.parse_args()
    need(args.output is not None or args.expect is not None, 'supply --output or --expect')
    receipt = verify(args.root)
    if args.expect is not None:
        need(exact(receipt,json.loads(args.expect.read_text())), 'receipt mismatch')
    if args.output is not None:
        args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print('PASS: complete independent-gamma83 source; input-language status UNRESOLVED')

if __name__ == '__main__':
    main()
