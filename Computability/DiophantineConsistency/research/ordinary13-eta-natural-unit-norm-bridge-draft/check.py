#!/usr/bin/env python3
"""Pinned source interfaces and exact finite residue/graph controls; no Lean."""
from pathlib import Path
import hashlib,itertools,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/Compact44/FreeJ13.lean':'cf8beb3993b1cd716266d7adf06ab9ee4eda5d5a7e4b921072eecc5b31389d01',
'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',
'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean':'9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
source=s['Lean/DiophantineConsistency/Compact44/FreeJ13.lean']
for term in ('theorem main_ne','theorem aux_ne','theorem strong_ne','theorem unit_iff_one'):assert term in source
assert 'theorem product5_magnitudes' in s['Lean/DiophantineConsistency/ArithmeticSignedPairs.lean']
assert 'theorem negative_residue' in s['Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'])
rng=random.Random(130085);n=0
for _ in range(200):
 e={x:rng.randrange(-6,7) for x in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:
  x=a if isinstance(a,int) else e[a];y=b if isinstance(b,int) else e[b]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 b=e['qm'];z=e['Z'];x=e['X'];ss=e['s'];k=e['k'];q=1+b;Y=q**3*ss;ell=x*Y*Y*k
 assert e['ell']==ell
 assert e['A0']==z*z-b*b*(1+ell*(ell+k))
 assert e['A1']==e['Dstar']**2-e['U']**2*(1+e['Delta']*e['c']**2)
 assert e['g72']==e['I']**2-e['Delta']*(e['n_f']**2-1)
 assert e['Fa']==e['n_y']**2-e['Delta']*(e['n_f']**2-1)*(e['n_y']**2-e['V']**2)
 assert e['out']==(1+e['A0'])*(1+e['A1'])*e['Fa']*(1+e['g72'])-1
 assert all(t%4!=3 for t in (1+e['A0'],1+e['A1'],e['Fa'],1+e['g72']))
 n+=1
cases=0
for b,z,x,ss,k in itertools.product(range(4),repeat=5):
 q=1+b;Y=q**3*ss;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
 cases+=1
outs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (here/'EtaNaturalUnitGraph.lean.src',here/'EtaNaturalUnitBridge.lean.src')}
text=(here/'EtaNaturalUnitBridge.lean.src').read_text()
for t in ('theorem first_ne','theorem factor_units','theorem residuals_zero','theorem signed_norms','FreeJ13.main_ne','FreeJ13.aux_ne','FreeJ13.strong_ne','product5_magnitudes'):assert t in text
assert 'sorry' not in text and '\naxiom ' not in text
print(json.dumps({'source_sha256':pins,'draft_sha256':outs,'first_factor_mod4_cases':cases,'signed_graph_controls':n,'scope':'pinned source and finite controls only; no Lean elaboration, zero maps, endpoint or provider build','lean_executed':False},sort_keys=True,indent=2))
