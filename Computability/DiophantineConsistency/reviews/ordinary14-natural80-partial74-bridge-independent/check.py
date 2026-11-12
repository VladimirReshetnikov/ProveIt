#!/usr/bin/env python3
"""Independent exact graph/coordinate source review; does not invoke Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def data(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
P='research/ordinary14-natural80-partial74-bridge-draft/'
s=data(P+'Natural80Partial74.lean','942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16').decode()
assert hashlib.sha256(data(P+'check_source.py','9b008baac81e066ac55f7c740615511a827a64a0afcf1b1d7ac2ecd2278cd03e')).hexdigest()=='9b008baac81e066ac55f7c740615511a827a64a0afcf1b1d7ac2ecd2278cd03e'
data(P+'result.json','62a08ab5dadfc4e82ee73f8cb0debe083ad004863ef9ffa2cc86fcb5769e8d90')
specs=[
 ('80','research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5','research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean','015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9'),
 ('82','research/ordinary14-root74-natural-forced82/candidate.json','1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a','research/ordinary14-natural-forced82-lean-draft/P82NaturalForced.lean','4fd5635afea3327181cdce6d176103195a9d2698f40ab8c40e2ea5c9a9b1fb84'),
 ('86','research/ordinary14-root74-natural-cancel86/candidate.json','0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170','research/ordinary14-natural-cancel86-lean-draft/P86NaturalCancel.lean','57015ecd6c66b06867dc05fe392cf02db4a125e646faf9ca16830cb3c0b0b2ef'),
 ('74','research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093','research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean','5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b')]
G={};graphtexts={}
for label,jpath,jhash,lpath,lhash in specs:
 g=json.loads(data(jpath,jhash));t=data(lpath,lhash).decode();G[label]=g;graphtexts[label]=t
 assert len(g['witnesses'])==14 and len(g['fixed_numerals'])==4 and len(g['source'])==int(label)
 # Check aliases, full literal rows and the selected output/factor tuple independently.
 vs=re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var (\d+)',t)
 ps=re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.constant \(p (\d+)\)',t)
 assert vs==[(v,str(i)) for i,v in enumerate(g['witnesses'])]
 assert ps==[(v,str(i)) for i,v in enumerate(g['fixed_numerals'])]
 block=t.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
 rows=[]
 for line in block.splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'\s*let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)\s*',line);assert m,line
  name,x,op,y=m.groups();parse=lambda z:int(z) if z.isdecimal() else z
  rows.append([name,op,parse(x),parse(y)])
 assert rows==g['source']
 tuplebody=re.search(r'-- END LITERAL GRAPH\s*⟨([^⟩]+)⟩',t).group(1)
 assert [x.strip() for x in tuplebody.split(',')][:6]==['F0','F1','Fa','Fs','guard','out']
 assert all(token in t for token in ('theorem output_shape','(graph p).first * (graph p).main * (graph p).aux','(graph p).strong * (graph p).guardFactor - 1'))
 known=set(g['witnesses']+g['fixed_numerals'])
 for n,op,x,y in rows:
  assert n not in known and all(type(v)==int or v in known for v in (x,y));known.add(n)
 assert g['output']=='out'

# 80 vs 82: delete only J/gamma successors and redirect consumers.
a,b=G['80'],G['82'];assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
replacement={'J':'n_J','gamma':'n_gamma'}
assert all([n,'+',w,1] in b['source'] for n,w in replacement.items())
assert a['source']==[[n,op,replacement.get(x,x),replacement.get(y,y)] for n,op,x,y in b['source'] if n not in replacement]
# 82 vs 86: remove f/r/y successors, replace zeta/k/r0 nodes by the exact cut.
old={n:(op,x,y) for n,op,x,y in G['86']['source']};new={n:(op,x,y) for n,op,x,y in G['82']['source']}
assert set(new)-set(old)=={'kbase'} and set(old)-set(new)=={'f','r','y','zeta','g52'}
for name in ('f','r','y','zeta'):assert old[name]==('+','n_'+name,1)
assert old['k']==('+','eta','zeta') and old['g52']==('-','k','R') and old['r0']==('-','g52',1)
assert new['kbase']==('+','eta','n_zeta') and new['k']==('+','kbase',1) and new['r0']==('-','kbase','R')
for n in (set(old)&set(new))-{'k','r0'}:
 op,x,y=old[n];r={'f':'n_f','r':'n_r','y':'n_y'}
 assert new[n]==(op,r.get(x,x),r.get(y,y)),n
# 86 vs 74: all common rows agree apart from qF and the combined guard cut.
u={n:(op,x,y) for n,op,x,y in G['74']['source']};v={n:(op,x,y) for n,op,x,y in G['86']['source']}
assert set(u)<=set(v)
for n in set(u)-{'qF','guard_base','bt_quotient'}:assert u[n]==v[n],n
assert u['q']==('+',1,'qm') and u['qF']==('-','q','F') and v['qF']==('-','qm','n_F')
assert u['guard_base']==('+','g27','qF') and v['guard_base']==('-','g27','n_F')
assert u['bt_quotient']==('*','qm','h') and v['bt_quotient']==('*','qm','n_h')
# Sparse integer polynomials prove the qF, k/r0 and guard cancellations exactly.
def var(x):return {(x,):1}
def con(n):return {():n} if n else {}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def sub(a,b):return add(a,{m:-c for m,c in b.items()})
def mul(a,b):
 z={}
 for x,c in a.items():
  for y,d in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+c*d
 return {m:c for m,c in z.items() if c}
one=con(1);qm,f,eta,z,R,guard,h=map(var,('qm','f','eta','z','R','guard','h'))
qf=sub(add(one,qm),add(f,one));assert qf==sub(qm,f)
assert sub(sub(add(eta,add(z,one)),R),one)==sub(add(eta,z),R)
assert sub(add(guard,qf),mul(qm,add(h,one)))==sub(sub(guard,f),mul(qm,h))
# The three translations compose coefficientwise to the advertised five unchanged slots.
fixed={0,3,8,11,12}
for j in range(14):
 offset=-(j in {0,12})-(j in {3,8,11})+1
 assert offset==(0 if j in fixed else 1)
# Inspect the quoted interfaces and model embedding/zero directions at source level.
s82=data('research/ordinary14-natural-forced82-ring-bridge-draft/RingNatural82To86.lean','08e86ba4044b84a32ad7c2e496c61b454fcd4a5ee963b345d8fe75dc420c120e').decode()
s86=data('research/ordinary14-natural-cancel86-ring-bridge-draft/RingNatural86To74.lean','f7418af67e32119d47179e8bb92bfade6e24f305800f7abeb0d8f900bcfe47d4').decode()
model=data('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
for x in ('j = 3 ∨ j = 8 ∨ j = 11','(P82NaturalForced.graph p).output.evalRing v =','(P86NaturalCancel.graph p).output.evalRing (down v)'):assert x in s82
for x in ('fun j => v j+1','(P86NaturalCancel.graph p).output.evalRing v=(P74PositiveGuard.graph p).output.evalRing (shift v)'):assert x in s86
for x in ('j = 0 ∨ j = 12','j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12',
 'RingNatural86To74Draft.shift (RingNatural82To86Draft.down (down82 v)) = partial74 v',
 'partial74 (fun j => ι (v j)) = (fun j => ι (partial74 v j))',
 'InternalZero (P80NaturalForcedGamma.graph p).output v ↔',
 'InternalZero (P74PositiveGuard.graph p).output (partial74 v)',
 'rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,',
 '#print axioms DiophantineConsistency.Natural80Partial74Draft.output_eval74',
 '#print axioms DiophantineConsistency.Natural80Partial74Draft.internalZero_iff_partial'):assert x in s,x
assert 'AdaptiveEquationSyntax2011.InternalZero e v ↔ e.evalRing (fun i => ι (v i)) = 0' in model
print(json.dumps({'scope':'independent source signatures, literal graph rows and exact external algebraic cuts; no Lean or model theorem', 'graphs_and_full_row_counts':{k:len(G[k]['source']) for k in ('80','82','86','74')}, 'unshifted_slots':sorted(fixed),'exact_algebraic_cuts':3,'evaluated_or_elaborated_in_lean':False},sort_keys=True,indent=2))
