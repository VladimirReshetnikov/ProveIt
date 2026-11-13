#!/usr/bin/env python3
"""Read-only compact arithmetic and literal graph checks; no giant witness expansion."""
import gzip
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PINS = {
    'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json': 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
    'research/current14-carrier64-current-full-zero/README.md': '81a50389d94021a08dd878fa6d8e006a57297afe12a53cdcc69b62b4d397b5c0',
    'research/current14-carrier64-pell-floor/README.md': '8d3b46e7949b7db849a12ef1b6c3586cac661d3158e0347c402581c3b1d08db8',
    'research/current14-carrier64-toy-full-zero/README.md': '9749b225400ca60926a6ce150f7ba056ec6bb95cd5eb5fb9a466d6675c856b9f',
    'reviews/current14-carrier64-toy-full-zero-independent/README.md': '3c9b0901cb7ff7e3b331ea3c44986fa4c6192a1bd815473abae8887ccadff5bd',
}
for path, expected in PINS.items():
    if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
        raise RuntimeError('source pin changed: '+path)
source_path = ROOT / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
old = json.loads(source_path.read_bytes())
new = json.loads((Path(__file__).parent / 'graph.json').read_bytes())
deleted = {'ac','main_base','gammaH','main_root'}
expected = []
for row in old['source']:
    if row[0] not in deleted:
        expected.append([('root' if item == 'main_root' else item) for item in row])
if new['source'] != expected or len(expected) != 61:
    raise RuntimeError('graph transformation mismatch')
if new['witnesses'] != old['witnesses'][:-1]+['root']:
    raise RuntimeError('witness transformation mismatch')
rows = {r[0]:r for r in expected}
needed = {new['output']}
for row in reversed(expected):
    if row[0] in needed:
        needed.update(x for x in row[2:] if isinstance(x,str))
if len(needed & set(rows)) != 61 or not set(new['witnesses']) <= needed:
    raise RuntimeError('nonlive gate or witness')
ports={}
for name, meta in old['coefficient_binding']['ports'].items():
    packed=(source_path.parent/'coefficients'/meta['file']).read_bytes()
    raw=gzip.decompress(packed)
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:
        raise RuntimeError('port bytes mismatch')
    ports[name]=int.from_bytes(raw,'big')
beta,K,lo,mf=[ports[x] for x in ('beta','K0','MC','MF')]
B=beta.bit_length(); q=beta+1; hi=mf-beta
G=q*(hi-1)+lo+1; R=(G+1)*q*q-1; N=(R-1)//2
F=q-hi; alpha=lo+hi-beta; C=beta-lo
if not (B==94517 and q==1<<B and 0<lo<beta<mf<2*beta and F>0 and alpha>0 and C>0 and q-F-alpha==C):
    raise RuntimeError('scalar/port assumptions')
if not (R==G*(q*q-1)+lo+q*mf and G==beta*(q-F)+alpha and R%4==3 and R.bit_count()==3*B+2 and N.bit_count()==3*B+1 and R>3*B+2):
    raise RuntimeError('rank/population assumptions')
if math.gcd(C,beta)!=1:
    raise RuntimeError('transport coefficient is not invertible')
target=((F-K*C)*pow(C,-1,beta))%beta
exponent=R%B
t=(target*pow(pow(2,exponent,beta),-1,beta))%beta
if not (0<t<beta and ((K+pow(2,exponent,beta)*t)*C-F)%beta==0):
    raise RuntimeError('transport residue')
digest=hashlib.sha256(t.to_bytes((t.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'scope':'finite checks and literal graph only; symbolic full-zero argument is in README',
                  'graph_sha256':hashlib.sha256((Path(__file__).parent/'graph.json').read_bytes()).hexdigest(),
                  'old_gates':65,'new_gates':61,'R_bits':R.bit_length(),'R_mod_4':R%4,
                  'R_mod_B':exponent,'N_population':N.bit_count(),'t_bits':t.bit_length(),
                  't_sha256':digest,'C_coprime_beta':True,'transport_mod_beta':0},indent=2,sort_keys=True))
