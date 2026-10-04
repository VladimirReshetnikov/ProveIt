#!/usr/bin/env python3
"""Fresh bounded actual-modulus source scout; predecessors are inert data only."""
import argparse
import json
import hashlib
import random
from pathlib import Path
from fractions import Fraction as Q
PINS = {'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade', 'complete84_joint_root_cut.md': '79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c', 'complete87_joint_norm_scout.md': '681a06e6f280b9b17a723ab9046012f66ffcdeb963930e33d745b47ff044d1bf', 'complete87_discriminant_shear_scout.md': '9ef454b65cf75ace91c232d1b0ac643b8c0a00f39c43e16f0ead0666ba414765', 'complete86_affine_port_scout.md': '295dc976c0cffb71fe17be53c6bd541431fc7bb4d43a2f81e9f61c426b3cc558'}
def need(ok, message):
 if not ok:raise ValueError(message)
def audit(W):
 for n,h in PINS.items():need(hashlib.sha256((W/n).read_bytes()).hexdigest()==h, 'pin '+n)
 b=(W/'complete84_scaled_strong_output.json').read_bytes()
 p = json.loads(b)['packet']
 need({r[0]: r for r in p['source']}['a4'] == ['a4', '*', 4, 'R12'], 'pinned source, identity, or boundary check')
 need({r[0]: r for r in p['source']}['a4m5'] == ['a4m5', '+', 'a4', 3], 'pinned source, identity, or boundary check')
 remove = {'cam2', 'D1', 'gamma_sum', 'gam', 'R14', 'difference_multiple', 'exponent_partial', 'modulus_multiple', 'exponent_rhs'}
 new = [['modulus_multiple', '*', 'rho', 'a4m5'], ['sigma_four', '*', 4, 'sigma'], ['shifted_main_center', '+', 'R10a', 'sigma_four'], ['main_center_product', '*', 'R12', 'shifted_main_center'], ['sigma_three', '*', 3, 'sigma'], ['main_offset', '+', 'wn2', 'sigma_three'], ['main_partial', '+', 'main_center_product', 'main_offset'], ['R14', '+', 'main_partial', 'modulus_multiple'], ['difference_multiple', '*', 'index_rhs', 'R12'], ['exponent_partial', '+', 'W', 'difference_multiple'], ['exponent_rhs', '+', 'exponent_partial', 'modulus_multiple']]
 rows = [r for r in p['source'] if r[0] not in remove] + new
 known = set(p['free'])
 out = []
 while rows:
     row = next((r for r in rows if all((type(a) is int or a in known for a in r[2:]))))
     rows.remove(row)
     out.append(row)
     known.add(row[0])
 need(len(out) == 86 and sum((r[1] == '*' for r in out)) == 48, 'pinned source, identity, or boundary check')
 prods = {r[0]: r[2:] for r in out}
 todo = [p['output']]
 used = set()
 while todo:
     a = todo.pop()
     if type(a) is int or a in used:
         continue
     used.add(a)
     todo.extend(prods.get(a, []))
 need(used == set(p['free']) | set(prods), 'pinned source, identity, or boundary check')
 
 def run(src, values):
     e = dict(values)
     for n, o, a, b in src:
         a = a if type(a) is int else e[a]
         b = b if type(b) is int else e[b]
         e[n] = a * b if o == '*' else a + b if o == '+' else a - b
     return e
 vars = ['a', 'c', 'kappa', 'rho', 'sigma', 'X', 'W']
 z = (0,) * 7
 
 def atom(x):
     if type(x) is int:
         return {z: x} if x else {}
     e = list(z)
     e[vars.index(x)] = 1
     return {tuple(e): 1}
 
 def plus(a, b, s=1):
     c = dict(a)
     for t, x in b.items():
         c[t] = c.get(t, 0) + s * x
         if not c[t]:
             del c[t]
     return c
 
 def mul(a, b):
     c = {}
     for s, v in a.items():
         for t, w in b.items():
             e = tuple((x + y for x, y in zip(s, t)))
             c[e] = c.get(e, 0) + v * w
     return c
 A, C, K, R, S, X, Y = map(atom, vars)
 H = plus(mul(atom(4), A), atom(3))
 D = plus(plus(mul(A, C), X), mul(plus(R, S), H))
 Dnew = plus(plus(mul(A, plus(C, mul(atom(4), S))), plus(X, mul(atom(3), S))), mul(R, H))
 need(D == Dnew, 'pinned source, identity, or boundary check')
 rng = random.Random(20261003)
 for j in range(32):
     vals = {v: Q(rng.randrange(-4, 5), rng.randrange(1, 5)) for v in p['free']}
     a = run(p['source'], vals)
     bb = run(out, vals)
     need(all((a[n] == bb[n] for n in ['norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index', 'norm_transport', 'norm_strong', 'polynomial'])), 'pinned source, identity, or boundary check')
 fixtures = []
 for a in [Q(-3, 4), Q(-1)]:
     v = {n: Q(1) for n in p['free']}
     v.update(dict(zip(p['fixed_numerals'], [31, 7, 10, 5, 2, 19])))
     v.update({'Jrep': 1 / Q(v['Bm1']), 'w': Q(1, 2), 's': a / 16, 'x': -Q(v['inner_bits'], v['twice_cell_bits']), 'delta': 0, 'F': 0, 'Z': 0, 'alpha': v['inner_bits'] + 1, 'rho': 0, 'sigma': 0, 'eta': 0, 'zeta': 0})
     e = run(p['source'], v)
     need(e['R12'] == a and e['R10a'] == e['index_rhs'] == 0 and (e['W'] == 1), 'pinned source, identity, or boundary check')
     need(e['norm_main'] == e['norm_input'] == 1, 'pinned source, identity, or boundary check')
     need(e['a4m5' if a == Q(-3, 4) else 'A'] == 0, 'pinned source, identity, or boundary check')
     fixtures.append({'a': str(a), 'supplied': {n: str(x) for n, x in v.items()}, 'H': str(e['a4m5']), 'Delta': str(e['A']), 'main': str(e['norm_main']), 'input': str(e['norm_input']), 'scope': 'signed rational all-value nondivisibility diagnostic for Nm*Ni only, not a compiler zero'})
 memo = {}
 
 def node(key):
     if key not in memo:
         memo[key] = len(memo)
     return memo[key]
 
 def abstract(rows):
     ev = {n: node(('free', n)) for n in p['free']}
     for n, o, a, b in rows:
         if n == 'R14':
             ev[n] = node(('proved_main_root',))
             continue
         a = node(('integer', a)) if type(a) is int else ev[a]
         b = node(('integer', b)) if type(b) is int else ev[b]
         if o in ['+', '*'] and a > b:
             a, b = (b, a)
         ev[n] = node((o, a, b))
     return ev
 oldenv = abstract(p['source'])
 newenv = abstract(out)
 factors = ['norm_first', 'norm_main', 'norm_input', 'norm_aux', 'norm_index', 'norm_transport', 'norm_strong']
 need(all((oldenv[n] == newenv[n] for n in factors + ['polynomial'])), 'pinned source, identity, or boundary check')
 r = {'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'dependency_pins': PINS, 'parent_json_sha256': hashlib.sha256(b).hexdigest(), 'status': 'NO_SAVING_IN_DISPLAYED_H_SPECIFIC_SCHEDULE', 'packet': {'source': out, 'free': p['free'], 'witnesses': p['witnesses'], 'fixed_numerals': p['fixed_numerals'], 'ordinary_input': 'x', 'output': p['output'], 'ledger': {'M': 48, 'A': 38, 'total': 86}, 'exact_degree': 187}, 'root_identity_coefficients': len(D), 'full_cut_identities': 8, 'whole_signed_rational_checks': 32, 'nondivisibility_diagnostics': fixtures, 'scope': 'One all-value 86-row alternative, and nondivisibility of Nm*Ni by H or Delta; not a global lower bound.'}
 return r

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path)
 mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--output',type=Path);mode.add_argument('--expect',type=Path)
 a=ap.parse_args();r=audit(a.root.resolve());text=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.expect:need(a.expect.read_bytes()==text.encode(), 'exact receipt replay')
 else:
  with a.output.open('x') as f:f.write(text)
 print(json.dumps({'status':r['status'],'ledger':r['packet']['ledger'],'exact_degree':r['packet']['exact_degree'],'full_cut_identities':r['full_cut_identities']}))
if __name__=='__main__':main()
