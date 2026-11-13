#!/usr/bin/env python3
"""Bounded source, DAG and residue controls; no Lean proof."""
import hashlib,json,random
from pathlib import Path
P=Path(__file__).resolve().parent; D=P.parents[1]
files={
 'draft':(P/'Natural79ZeroWUnits.lean','2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c'),
 'graph':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'candidate':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
 'residues':(D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60'),
 'units':(D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean','ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d')}
s={}
for name,(path,digest) in files.items():
 data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==digest,name;s[name]=data.decode()
a=json.loads(s['candidate']);g={n:[op,x,y] for n,op,x,y in a['source']}
shapes={'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'E':['*','X','Y'],
        'kY':['*','Y','k'],'ell':['*','E','kY'],'g30':['+','ell','k'],
        'g38':['*','n_r','n_r'],'g40':['*','ell','g30'],'F0':['-','g38','g40'],
        'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
        'P01234':['*','P0123','guard'],'out':['-','P01234',1]}
for n,row in shapes.items(): assert g[n]==row,n
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in s['graph']
for name in ('main_ne','aux_ne','strong_ne'): assert 'theorem '+name in s['residues']
assert 'theorem product5_positive' in s['units']
for tok in ('theorem product_of_zero','theorem first_eval_at_w_zero','(hw : v 6=0)',
            'theorem nonnegative_not_negative_unit','theorem units_of_zero_w_zero',
            'theorem restricted_residues_of_shapes','(hmain : pairResidue',
            '(haux : pairResidue','(hstrong : pairResidue'):
 assert tok in s['draft'],tok
assert 'sorry' not in s['draft'] and 'admit' not in s['draft']
# Exhaust the elementary factor residue patterns, independently of Lean.
for aa in range(4):
 delta=(aa*aa+4*aa+3)%4
 for f in range(4):
  Q=(delta*(f*f-1))%4
  for c in range(4):
   for U in range(4):
    for d in range(4): assert (1+d*d-U*U*(1+delta*c*c))%4!=3
  for y in range(4):
   for z in range(4): assert (y*y-Q*(y*y-z*z))%4!=3
  for i in range(4): assert (1+i*i-Q)%4!=3
# Finite arbitrary-port graph controls at w=0 supplement the structural first cut.
rng=random.Random(79001); prime=1000003
for _ in range(300):
 e={n:rng.randrange(-10,11)%prime for n in a['witnesses']+a['fixed_numerals']};e['n_w']=0
 val=lambda x:x%prime if type(x) is int else e[x]
 for n,op,x,y in a['source']:
  x,y=val(x),val(y); e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 assert e['F0']==e['n_r']**2%prime
 assert e['out']==(e['F0']*e['F1']*e['Fa']*e['Fs']*e['guard']-1)%prime
print(json.dumps({'scope':'source signatures, exact selected DAG rows, residue and finite controls; no Lean/model/iPRA proof','pinned_files':len(files),'selected_DAG_rows':len(shapes),'arbitrary_port_w_zero_controls':300,'residue_modulus':4,'residue_graph_bindings_assumed':True},sort_keys=True,indent=2))
