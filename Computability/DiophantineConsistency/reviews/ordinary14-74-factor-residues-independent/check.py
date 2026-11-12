#!/usr/bin/env python3
"""Independent pattern-DAG and complete mod-four controls, no Lean."""
from pathlib import Path
from itertools import product
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-factor-residues-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'1931e6625ec0174ee582e80c3819ba85fda0f03a38e920d257f646159108726e','FactorResidues74.lean':'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60','check_source.py':'328d45060a239dbc614140cdc3e8e91dd5e0a2ffec592d25f6362e3ea3ea49d3','observation.json':'a396dfc8420ed12f2294323697c4df984c60fc91b3903f4012abc786e7228425'}
tail=b"\nIndependent source review: [74 factor residues](../../reviews/ordinary14-74-factor-residues-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='3bfa652fc13a59ee5bca9426ae5e88ae95073c3958746524a6a7bd459e6529ff'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'FactorResidues74.lean').read_text();g=D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean';provider=D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean';gtext=g.read_text();prov=provider.read_text()
assert sha(g)=='5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b'
assert sha(provider)=='9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4'
for t in ['rw [pairEval_residue]','main_bad uv av cv dv','aux_bad av fv zv yv','strong_bad av fv iv','mainPattern (P74PositiveGuard.graph p).U','auxPattern (.var 11)','strongPattern (P74PositiveGuard.graph p).I','(P74PositiveGuard.graph p).a (.var 3) := by rfl']:
 assert t in s,t
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
for signature in ['theorem pairEval_residue {σ : Type*} (e : Expr σ) (v : σ → V)','theorem main_bad : ∀ u a c d : ZMod 4','theorem aux_bad : ∀ a f v y : ZMod 4','theorem strong_bad : ∀ a f i : ZMod 4']:
 assert signature in prov,signature
# Independently construct full binary syntax DAG from the actual literal source rows.
body=gtext.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH\n',1)[0]
nodes={name:('leaf',name) for name in ['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma','h','beta','K0','MC','MF']}
def op(o,a,b):return (o,a,b)
for line in body.splitlines():
 m=re.fullmatch(r'  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)',line);assert m,line
 n,a,o,b=m.groups(); nodes[n]=op(o,int(a) if a.isdigit() else nodes[a],int(b) if b.isdigit() else nodes[b])
a,u,c,d,y,z,f,i=[nodes[x] for x in ['a','U','c','Dstar','y','V','f','I']]
add=lambda x,y:op('+',x,y);sub=lambda x,y:op('-',x,y);mul=lambda x,y:op('*',x,y)
delta=add(add(3,mul(4,a)),mul(a,a)); Q=mul(delta,sub(mul(f,f),1))
main=add(1,sub(mul(d,d),mul(mul(u,u),add(1,mul(delta,mul(c,c))))))
aux=sub(mul(y,y),mul(Q,sub(mul(y,y),mul(z,z))))
strong=add(1,sub(mul(i,i),Q))
assert nodes['F1']==main and nodes['Fa']==aux and nodes['Fs']==strong
mainn=auxn=strongn=0
for U,A0,C,D0 in product(range(4),repeat=4):
 delta=(A0*A0+4*A0+3)%4
 assert (1+D0*D0-U*U*(1+delta*C*C))%4 !=3
 mainn+=1
for A0,F,V,Y in product(range(4),repeat=4):
 Q=(A0*A0+4*A0+3)*(F*F-1)
 assert (Y*Y-Q*(Y*Y-V*V))%4 == (Q*V*V+(1-Q)*Y*Y)%4 != 3
 auxn+=1
for A0,F,I in product(range(4),repeat=3):
 assert (1+I*I-(A0*A0+4*A0+3)*(F*F-1))%4 != 3
 strongn+=1
receipt=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout
assert receipt==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'independent source DAG and finite residue controls; no Lean, provider or model endpoint','author_pins':pins,'graph_sha256':sha(g),'mod4_provider_sha256':sha(provider),'main_cases':mainn,'aux_cases':auxn,'strong_cases':strongn,'author_receipt_reproduced':True},sort_keys=True,indent=2))
