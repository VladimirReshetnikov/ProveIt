#!/usr/bin/env python3
"""Evaluate a deterministic s=0 obstruction at toy and authenticated ports."""
from pathlib import Path
import gzip, hashlib, json
P = Path(__file__).resolve().parent
D = P.parents[1]
def digest(x): return hashlib.sha256(x).hexdigest()
def load(path, sha):
    b = path.read_bytes(); assert digest(b) == sha, str(path); return json.loads(b)
a = load(D/'research/ordinary14-natural-forcedj81/candidate.json', '24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999')
b = load(P/'candidate.json', 'bbdd14c8bb424a65803d3624d404ba17cdad1cb053cc38401218c22be2780559')
assert ['s', '+', 'n_s', 1] in a['source']
expected = [[n,op,'n_s' if x=='s' else x,'n_s' if y=='s' else y]
            for n,op,x,y in a['source'] if n!='s']
assert b['source'] == expected and len(expected) == b['operations'] == 80
assert b['parent_sha256'] == digest((D/'research/ordinary14-natural-forcedj81/candidate.json').read_bytes())
def calc(g, values):
    e = values.copy()
    for n, op, x, y in g['source']:
        x = x if type(x) is int else e[x]
        y = y if type(y) is int else e[y]
        e[n] = x+y if op=='+' else x-y if op=='-' else x*y
    return e
def witness(beta, K0, MC, MF):
    assert beta >= 2 and K0 >= 0 and MC > 0 and MF > 0
    q=beta+1; w=(1-K0)%beta or beta
    R=(beta-1+beta*beta)*(q*q-1)+MC+MF*q
    assert R > 0 and (q*w+K0-1)%beta == 0
    v={'n_J':1, 'n_F':0, 'n_alpha':beta-2, 'n_f':2, 'n_i':2,
       'n_T':R-1, 'n_w':w-1, 'n_s':0, 'n_r':1, 'n_eta':0,
       'n_zeta':R-1, 'n_y':1, 'n_gamma':0,
       'n_h':(q*w+K0-1)//beta, 'beta':beta, 'K0':K0, 'MC':MC, 'MF':MF}
    assert all(v[n] >= 0 for n in b['witnesses'])
    e=calc(b,v)
    for n,x in {'qm':beta, 'q':q, 'X':q*w, 'Y':0, 'U':0, 'ell':0, 'c':1,
                'k':R+1, 'R':R, 'Dstar':0, 'Q':9, 'V':-1,
                'F0':1, 'F1':1, 'Fa':1, 'Fs':1, 'guard':1, 'out':0}.items():
        assert e[n] == x, n
    return v
toy=witness(2,1,1,1)
assert toy == {'n_J':1,'n_F':0,'n_alpha':0,'n_f':2,'n_i':2,'n_T':43,
               'n_w':1,'n_s':0,'n_r':1,'n_eta':0,'n_zeta':43,'n_y':1,
               'n_gamma':0,'n_h':3,'beta':2,'K0':1,'MC':1,'MF':1}
assert calc(a,toy)['out'] != 0
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(p72/'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,m in bind['ports'].items():
    assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
    z=(p72/m['path']).read_bytes();assert digest(z)==m['sha256_gzip']
    raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and digest(raw)==m['sha256_raw']
    ports[n]=int.from_bytes(raw,'little')
assert set(ports)=={'beta','K0','MC','MF'}
witness(**ports)
print(json.dumps({'scope':'counterexample to forced s positivity and unchanged-coordinate transfer only',
                  'toy_ports':{'beta':2,'K0':1,'MC':1,'MF':1},
                  'toy_zero':True,'same_toy_coordinates_parent_nonzero':True,
                  'authenticated_ports_zero':True,'unshifted_gates':80,
                  'no_global_existence_or_lean_claim':True}, sort_keys=True, indent=2))
