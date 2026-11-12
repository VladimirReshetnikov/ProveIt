#!/usr/bin/env python3
"""Pinned composition interface and bounded eta-zero graph controls; no Lean."""
from pathlib import Path
import hashlib,json,random
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
g=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
rows={r[0]:r[1:] for r in g['source']}
for n,r in {'c':['+','n_eta','kY'],'i':['+','n_i',1],'T':['+','n_T',1],
 'I':['*','c2','i'],'V':['-','g76','c'],'g72':['-','g71','Q'],
 'Fa':['-','y2','g82'],'R':['+','g47','g50']}.items():assert rows[n]==r
src=(HERE/'EtaNaturalGraphParity.lean.src').read_text()
for x in ['theorem eta_zero_impossible','(heta : v 9=0)',
          'EtaNaturalUnitBridgeDraft.signed_norms',
          'EtaNaturalGraphStrongAuxDraft.field_I',
          'EtaNaturalGraphStrongAuxDraft.direct_auxiliary p v hz hFq',
          'EtaNaturalCompactParityDraft.eta_zero_of_represented_factors K v hz heta hstrong haux',
          'theorem eta_positive']:
 assert x in src,x
head=src.split('theorem eta_zero_impossible',1)[1].split(':= by',1)[0]
assert '(hstrong :' not in head and '(haux :' not in head
rng=random.Random(130092); count=0
for _ in range(192):
 e={n:rng.randrange(0,4) for n in g['witnesses']+g['fixed_numerals']}
 e['n_eta']=0;e['n_J']=rng.randrange(1,4);e['beta']=rng.randrange(1,4)
 q=1+e['n_J']*e['beta'];e['n_F']=rng.randrange(q)
 for name,op,a,b in g['source']:
  x=a if isinstance(a,int) else e[a];y=b if isinstance(b,int) else e[b]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 assert e['q']==q and e['F']<=q
 naturalR=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['n_J']
 assert e['R']==naturalR
 X=e['X'];Y=e['Y'];k=e['k'];a=X*Y+Y;c=Y*k;D=3+4*a+a*a
 f=e['n_f'];i=e['n_i']+1;T=e['n_T']+1;y=e['n_y'];z=f*f*(T*c)-(f*f*naturalR+c)
 assert e['c']==c and e['Delta']==D and e['I']==c*c*i and e['V']==z
 assert e['g72']==(c*c*i)**2-D*(f*f-1)
 assert e['Fa']==y*y-D*(f*f-1)*(y*y-z*z)
 count+=1
print(json.dumps({'source_pins':pins,'eta_zero_literal_controls':count,
 'lean_executed':False,'scope':'source interface and bounded graph checks only; no model proof or endpoint'},sort_keys=True,indent=2))
