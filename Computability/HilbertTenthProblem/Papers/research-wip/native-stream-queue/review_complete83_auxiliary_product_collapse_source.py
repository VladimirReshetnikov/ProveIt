#!/usr/bin/env python3
"""Independent full factor/source audit. Frozen predecessors are inert data only."""
import argparse
import hashlib
import json
from pathlib import Path
from collections import Counter

AUTHOR_PINS = {
 'complete83_auxiliary_product_collapse.py':'48cfce3e30fe2d1118a17b328962d987595dd604e37411c299ce8f7382b88a6c',
 'complete83_auxiliary_product_collapse.json':'0045c588a9053903c6e99a8362efa2ccef320bc5b057f2beda6419d0fc593af0',
 'complete83_auxiliary_product_collapse.md':'a224d930f94a3888b4208147dc54d90127999342313120a5239e40408e948d50',
}
def need(ok, message):
 if not ok: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def audit(ROOT, author):
 for n,h in AUTHOR_PINS.items(): need(sha((author/n).read_bytes())==h, 'author pin '+n)
 BASE=author/'complete83_auxiliary_product_collapse'
 parent = json.loads((ROOT / 'complete84_scaled_strong_output.json').read_text())['packet']
 old = json.loads((ROOT / 'complete82_auxiliary_square_product_chart.json').read_text())['packet']
 r = json.loads(BASE.with_suffix('.json').read_text())
 p = r['packet']
 need(len(p['free'])==25 and len(p['witnesses'])==18, 'supplied interface')
 need(p['factors']==['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong'], 'full factor order')
 need(r['source_sha256'] == AUTHOR_PINS['complete83_auxiliary_product_collapse.py'], 'independent source or coefficient check')
 for n, h in r['dependency_pins'].items():
     need(hashlib.sha256((ROOT / n).read_bytes()).hexdigest() == h, n)
 expected = []
 for row in parent['source']:
     if row[0] == 'auxiliary_Tf':
         need(row == ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f'], 'independent source or coefficient check')
         continue
     expected.append(['auxiliary_product' if v == 'auxiliary_Tf' else v for v in row])
 need(expected == p['source'], 'independent source or coefficient check')
 for key in ['free', 'witnesses']:
     need(['auxiliary_product' if x == 'auxiliary_quotient' else x for x in parent[key]] == p[key], 'independent source or coefficient check')
 need(p['fixed_numerals'] == parent['fixed_numerals'], 'independent source or coefficient check')
 need(set(old['free']) - {'L16', 'auxiliary_Tf'} | {'f', 'auxiliary_product'} == set(p['free']), 'independent source or coefficient check')
 known = set(p['free'])
 producers = {}
 for n, o, a, b in p['source']:
     need(n not in known and o in ['+', '-', '*'], 'independent source or coefficient check')
     need(all((type(v) is int or v in known for v in [a, b])), 'independent source or coefficient check')
     known.add(n)
     producers[n] = [a, b]
 stack = [p['output']]
 live = set()
 while stack:
     v = stack.pop()
     if type(v) is int or v in live:
         continue
     live.add(v)
     stack.extend(producers.get(v, []))
 need(live == set(p['free']) | set(producers), 'independent source or coefficient check')
 need([r for r in p['source'] if r[0] == 'L16'] == [['L16', '*', 'f', 'f']], 'independent source or coefficient check')
 need([['auxiliary_Tf' if x == 'auxiliary_product' else x for x in row] for row in p['source'] if row[0] != 'L16'] == old['source'], 'independent source or coefficient check')
 counts = Counter((row[1] for row in p['source']))
 need(counts == {'*': 46, '+': 20, '-': 17}, counts)
 need(p['ledger']=={'M':46,'A':37,'total':83,'core_M':40,'core_A':36,'core_total':76,'finalizer_M':6,'finalizer_A':1,'finalizer_total':7}, 'paid ledger')
 names = p['free']
 N = len(names)
 zero = (0,) * N
 weights = [0 if n in p['fixed_numerals'] else 1 for n in names]
 
 def const(x):
     return {} if x == 0 else {zero: x}
 
 def var(n):
     e = list(zero)
     e[names.index(n)] = 1
     return {tuple(e): 1}
 
 def add(a, b, s=1):
     c = dict(a)
     for e, v in b.items():
         c[e] = c.get(e, 0) + s * v
         if not c[e]:
             del c[e]
     return c
 
 def mul(a, b):
     c = {}
     for e, v in a.items():
         for f, w in b.items():
             g = tuple((x + y for x, y in zip(e, f)))
             c[g] = c.get(g, 0) + v * w
     return {e: v for e, v in c.items() if v}
 
 def power(a, n):
     z = const(1)
     for _ in range(n):
         z = mul(z, a)
     return z
 
 def op(s, a, b):
     return mul(a, b) if s == '*' else add(a, b, -1 if s == '-' else 1)
 
 def leader(a):
     d = max((sum((x * w for x, w in zip(e, weights))) for e in a))
     return (d, {e: v for e, v in a.items() if sum((x * w for x, w in zip(e, weights))) == d})
 e = {n: var(n) for n in names}
 final = {'norm_pair', 'norm_triple', 'norm_four', 'norm_product', 'all_units', 'seven_units', 'polynomial'}
 for n, s, a, b in p['source']:
     if n in final:
         continue
     e[n] = op(s, const(a) if type(a) is int else e[a], const(b) if type(b) is int else e[b])
 need(leader(e['A'])[0]==12, 'subtracted Delta degree')
 Q = mul(e['Bm1'], e['Jrep'])
 k = add(e['eta'], e['zeta'])
 gamma = add(e['rho'], e['sigma'])
 x0 = mul(e['w'], Q)
 y0 = mul(e['s'], power(Q, 3))
 a0 = mul(x0, y0)
 c0 = mul(k, y0)
 D0 = power(a0, 2)
 V0 = mul(power(Q, 3), add(mul(mul(k, e['s']), e['auxiliary_product']), mul(add(Q, e['F'], -1), power(e['f'], 2)), -1))
 S20 = mul(power(e['i'], 2), mul(power(D0, 2), power(c0, 4)))
 C1 = add(add(add(add(Q, e['F'], -1), e['Z'], -1), e['alpha'], -1), mul(e['twice_cell_bits'], e['x']), -1)
 Nt = add(mul(e['w'], C1), mul(e['transport_quotient'], Q), -1)
 expected_leaders = {'norm_first': mul(const(-1), mul(power(a0, 2), power(c0, 2))), 'norm_main': mul(const(8), mul(gamma, mul(power(a0, 2), c0))), 'norm_input': mul(const(-4), mul(power(e['delta'], 2), power(a0, 5))), 'norm_aux': mul(S20, power(V0, 2)), 'norm_index': mul(const(-1), mul(e['h'], a0)), 'norm_transport': Nt, 'norm_strong': mul(const(-1), S20)}
 actual = {}
 for f in p['factors']:
     d, L = leader(e[f])
     need(L == expected_leaders[f], f)
     actual[f] = {'degree': d, 'full_factor_monomials': len(e[f]), 'leader_monomials': len(L), 'full_factor_coefficient_sha256': sha(json.dumps(sorted(e[f].items()), separators=(',', ':')).encode())}
 need([actual[f]['degree'] for f in p['factors']] == [22, 18, 32, 58, 7, 2, 46], 'independent source or coefficient check')
 lead = const(1)
 for f in p['factors']:
     lead = mul(lead, expected_leaders[f])
 claimed = const(32)
 for n, t in [(Q, 111), (e['h'], 1), (gamma, 1), (e['delta'], 2), (e['i'], 4), (k, 11), (e['w'], 18), (e['s'], 29), (Nt, 1), (add(mul(mul(k, e['s']), e['auxiliary_product']), mul(add(Q, e['F'], -1), power(e['f'], 2)), -1), 2)]:
     claimed = mul(claimed, power(n, t))
 need(lead == claimed, 'independent source or coefficient check')
 exps = {'Jrep': 112, 'Bm1': 112, 'h': 1, 'rho': 1, 'delta': 2, 'i': 4, 'eta': 13, 'w': 18, 's': 31, 'transport_quotient': 1, 'auxiliary_product': 2}
 target = tuple((exps.get(n, 0) for n in names))
 need(lead[target] == -32, 'independent source or coefficient check')
 need(leader(lead)[0] == 185, 'independent source or coefficient check')
 expected_final = [['norm_pair', '*', 'norm_first', 'norm_main'], ['norm_triple', '*', 'norm_pair', 'norm_input'], ['norm_four', '*', 'norm_triple', 'norm_aux'], ['norm_product', '*', 'norm_four', 'norm_index'], ['all_units', '*', 'norm_product', 'norm_transport'], ['seven_units', '*', 'all_units', 'norm_strong'], ['polynomial', '-', 'seven_units', 'A']]
 need([r for r in p['source'] if r[0] in final] == expected_final, 'independent source or coefficient check')
 out = {'status': 'PASS', 'pins_verified': len(r['dependency_pins']), 'source_count': len(p['source']), 'operations': dict(counts), 'factors': actual, 'whole_leader_monomials': len(lead), 'exact_degree': 185, 'uniform_f_free_coefficient': '-32*Bm1^112', 'scope': 'Fresh full factor coefficient expansions and exact inherited-row comparison; no predecessor execution.'}
 out.update({'review_source_sha256': sha(Path(__file__).read_bytes()), 'author_pins': AUTHOR_PINS, 'dependency_pins': r['dependency_pins'], 'whole_leader_sha256': sha(json.dumps(sorted(lead.items()), separators=(',', ':')).encode())})
 return out


def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--root',type=Path,required=True)
 ap.add_argument('--author-dir',type=Path)
 mode=ap.add_mutually_exclusive_group(required=True)
 mode.add_argument('--output',type=Path)
 mode.add_argument('--expect',type=Path)
 a=ap.parse_args()
 r=audit(a.root.resolve(),(a.author_dir or a.root).resolve())
 text=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.expect: need(a.expect.read_bytes()==text.encode(), 'exact independent receipt')
 else:
  with a.output.open('x') as out: out.write(text)
 print(json.dumps({'status':r['status'],'source_count':r['source_count'],'exact_degree':r['exact_degree'],'factor_monomials':sum(z['full_factor_monomials'] for z in r['factors'].values())}))
if __name__=='__main__': main()
