#!/usr/bin/env python3
"""Independent bounded source review; archived and author code never execute."""
import argparse
import io
import zipfile
import json,hashlib
from collections import Counter
from pathlib import Path

def req(x,s):
 if not x:raise ValueError(s)
def C(c):return {():c} if c else {}
def V(x):return {(x,):1}
def A(a,b):
 o=dict(a)
 for x,c in b.items():o[x]=o.get(x,0)+c
 return {x:c for x,c in o.items() if c}
def scale(a,c):return {x:v*c for x,v in a.items() if v*c}
def neg(a):return scale(a,-1)
def S(*xs):
 o={}
 for x in xs:o=A(o,x)
 return o
def M(a,b):
 o={}
 for x,c in a.items():
  for y,d in b.items():z=tuple(sorted(x+y));o[z]=o.get(z,0)+c*d
 return {x:c for x,c in o.items() if c}
def sq(a):return M(a,a)
def ref(lengths,eta,real,positive):
 pts=list(__import__('itertools').product(*(range(n) for n in lengths)));ids={p:i for i,p in enumerate(pts)}
 E=[];halo=[]
 for axis in range(3):
  for p in pts:
   q=tuple(p[j]+int(j==axis) for j in range(3))
   if q in ids:E.append((ids[p],ids[q]))
  other=[x for x in range(3) if x!=axis]
  for direction in (-1,1):
   for a in range(lengths[other[0]]):
    for b in range(lengths[other[1]]):
     q=[0,0,0];q[axis]=0 if direction==-1 else lengths[axis]-1;q[other[0]]=a;q[other[1]]=b
     halo.append(ids[tuple(q)])
 def p(n):return S(V('p_'+n),C(-1)) if positive else V(n)
 verts=[{f:p(f'v{i}_{f}') for f in ('z','ell','f','k','c','beta','g','h')} for i in range(len(pts))]
 us=[S(v['k'],v['c']) for v in verts]
 rs=[S(v['k'],scale(v['c'],2),v['beta']) for v in verts]
 av=[C(0) for v in verts];bv=[C(0) for v in verts];neigh=[[] for v in verts];terms=[]
 for i,(v,w) in enumerate(E):
  neigh[v].append(w);neigh[w].append(v)
  lo,mi,eq,pl,hi,sigma=[p(f'e{i}_{name}') for name in ('lo','neg','eq','pos','hi','sigma')]
  terms.append(sq(S(lo,mi,eq,pl,hi,C(-1))))
  d=S(rs[w],neg(rs[v]))
  for weight,res in [(lo,S(d,C(2),sigma)),(mi,S(d,C(1))),(eq,d),(pl,S(d,C(-1))),(hi,S(d,C(-2),neg(sigma)))]:terms.append(M(weight,sq(res)))
  terms.append(M(S(mi,eq,pl),sigma))
  av[v]=S(av[v],eq,pl,hi);bv[v]=S(bv[v],mi,eq,pl,hi)
  av[w]=S(av[w],lo,mi,eq);bv[w]=S(bv[w],lo,mi,eq,pl)
 for i,v in enumerate(verts):
  terms += [sq(S(v['z'],scale(us[i],6),neg(S(*(us[j] for j in neigh[i]))),C(-eta[i]))),sq(S(v['z'],v['ell'],C(-5))),sq(S(v['f'],v['k'],v['c'],C(-1))),M(S(v['f'],v['k']),v['beta']),M(us[i],sq(S(v['z'],neg(av[i]),neg(v['g'])))),M(v['f'],S(v['g'],us[i]) if real else v['g']),M(v['c'],sq(S(bv[i],neg(v['z']),C(-1),neg(v['h'])))),M(S(v['f'],v['k']),v['h'])]
 for i,v in enumerate(halo):terms.append(sq(S(us[v],p(f'halo{i}'),C(-5))))
 return S(*terms),E,halo,neigh

def check(path):
 receipt=json.loads(Path(path).read_text());total=0;mon=0;zeros=0;seen=set();certificates=[];own_bills={};paid_shifts=0
 for form in receipt['forms']:
  p=form['packet'];geo=p['geometry'];lengths=geo['lengths'];n=geo['V'];e=geo['E'];h=geo['H'];real=p['variant']=='real';pos=p['positive_coordinates'];moment=p['mode']=='moment_merged'
  key=(tuple(lengths),real,pos,moment);req(key not in seen,'duplicate form');seen.add(key)
  expected,edges,halo,nei=ref(lengths,p['eta'],real,pos)
  req(len(edges)==e and len(halo)==h,'geometry')
  env={x:V(x) for x in p['ports']};defs={};ops=Counter()
  for name,op,a,b in p['source']:
   req(name not in env,'distinct name');req(type(a) is int or a in env,'a defined');req(type(b) is int or b in env,'b defined')
   x=C(a) if type(a) is int else env[a];y=C(b) if type(b) is int else env[b]
   env[name]=M(x,y) if op=='*' else S(x,y if op=='+' else neg(y));defs[name]=(a,b);ops[op]+=1
  req(env[p['output']]==expected,'full polynomial')
  todo=[p['output']];live=set()
  while todo:
   x=todo.pop()
   if type(x) is int or x in live:continue
   live.add(x);todo.extend(defs.get(x,()))
  req(live==set(env),'all live')
  m=(10 if moment else 11)*n+(8 if moment else 12)*e+h
  a=21*n+(27 if moment else 28)*e+3*h-1-int(n==1)+int(real)*n+int(pos)*(8*n+6*e+h)
  req(ops['*']==m and ops['+']+ops['-']==a,'ledger')
  req(p['ledger']['operations']==m+a and p['ledger']['witnesses']==len(p['ports']),'saved metadata')
  req(max(map(len,expected))==3,'exact degree')
  rows=[[list(m),c] for m,c in sorted(expected.items())]
  ch=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  req(ch==p['coefficient_sha256'] and len(expected)==p['collected_monomials'] and max(map(abs,expected.values()))==p['coefficient_height'],'coefficient metadata')
  if pos:
   req(all(row[1:]==['-',port,1] for row,port in zip(p['source'][:len(p['ports'])],p['ports'])),'one paid shift per port')
   paid_shifts+=len(p['ports'])
  own_bills[key]={'M':m,'A':a,'total':m+a,'witnesses':len(p['ports']),'V':n,'E':e}
  certificates.append({'lengths':lengths,'real':real,'positive':pos,'moment':moment,'M':m,'A':a,'gates':m+a,'coefficient_count':len(expected),'coefficient_sha256':ch,'exact_degree':3})
  vals=form['zero_witness'];restored={x[2:] if pos else x:v-1 if pos else v for x,v in vals.items()};req(all(type(x) is int and x>=0 for x in restored.values()),'natural zero')
  def val(name):return restored[name]
  z=p['eta'].copy();u=[0]*n
  for v in form['legal_and_burning_trace']['legal_firing_order']:
   req(z[v]>=6,'legal toppling');z[v]-=6;u[v]+=1
   for w in nei[v]:z[w]+=1
  req(all(0<=x<=5 for x in z),'stable interior');req(all(u[v]<=5 for v in halo),'stable exterior');req(all(x in (0,1) for x in u),'binary odometer')
  req(z==[val(f'v{i}_z') for i in range(n)] and u==[val(f'v{i}_k')+val(f'v{i}_c') for i in range(n)],'witness endpoint')
  active={i for i,x in enumerate(u) if x};ranks=[0]*n;roundno=0
  while active:
   layer={i for i in active if z[i]>=sum(j in active for j in nei[i])};req(layer,'burnability');roundno+=1
   for i in layer:ranks[i]=roundno
   active-=layer
  req(ranks==[val(f'v{i}_k')+2*val(f'v{i}_c')+val(f'v{i}_beta') for i in range(n)],'canonical ranks')
  req(sum(c*__import__('math').prod(vals[x] for x in term) for term,c in expected.items())==0,'actual full zero')
  for i in range(n):
   req(val(f'v{i}_f')==int(ranks[i]==0) and val(f'v{i}_k')==int(ranks[i]==1) and val(f'v{i}_c')==int(ranks[i]>=2),'categories')
  total+=m+a;mon+=len(expected);zeros+=1
 req(len(seen)==24 and total==8788,'coverage')
 comparisons=[]
 for lengths in ((1,1,1),(2,1,1),(2,2,2)):
  for real in (False,True):
   for pos in (False,True):
    direct=own_bills[(lengths,real,pos,False)];moment=own_bills[(lengths,real,pos,True)];n,e=direct['V'],direct['E']
    req(direct['M']-moment['M']==n+4*e and direct['A']-moment['A']==e,'moment saving')
    comparisons.append({'lengths':list(lengths),'real':real,'positive':pos,'saved_M':n+4*e,'saved_A':e,'saved_total':n+5*e})
   for mode in (False,True):
    nat=own_bills[(lengths,real,False,mode)];pos=own_bills[(lengths,real,True,mode)]
    req(pos['M']==nat['M'] and pos['A']-nat['A']==nat['witnesses'],'paid shift delta')
  for pos in (False,True):
   for mode in (False,True):
    base=own_bills[(lengths,False,pos,mode)];real=own_bills[(lengths,True,pos,mode)]
    req(real['M']==base['M'] and real['A']-base['A']==base['V'],'real variant delta')
 return {'complete_sources':len(seen),'paid_gates':total,'coefficient_entries_compared':mon,'genuine_legal_zero_checks':zeros,'distinct_underlying_stabilizations':3,'paid_positive_subtractions':paid_shifts,'source_certificates':certificates,'cost_comparisons':comparisons,'scope':'Independent data-only complete polynomial, ledger, liveness and legal/burning fixture check; no author or archive code imported.'}

AUTHOR_PINS = {
 'sandpile_shared_arithmetic35_36.py':'cdf417e7504fe6fb14d9d85f1dfc91ba99d06ad51386b19923fed27816efcebc',
 'sandpile_shared_arithmetic35_36.json':'6d50b5044003e1f51265d48c72fd5c734e52d727518c33c3abd984bb49c8f55a',
 'sandpile_shared_arithmetic35_36.md':'259a66caba0d776c97de7e76d13739aab1a91c2e0685d5a318950e73b59985a7'}
ARCHIVE_PINS = {
 'Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip': '3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d',
 'Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip': '72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac'}
MEMBER_PINS = {
 'Research_Report35/evidence/composition/PROOF.md': '6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e',
 'Research_Report35/evidence/composition/prism_certificate.py': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2',
 'Research_Report36/evidence/real/PROOF.md': '9bc26062cc0e68fc8fee18290c347b309e2f711d208644ec541b29a5492071ae',
 'Research_Report36/evidence/real/approved_base/prism_certificate.py': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2'}
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def authenticate(root,incoming):
 req(len(AUTHOR_PINS)==3,'author freeze required')
 for name,pin in AUTHOR_PINS.items():req(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'author pin '+name)
 found=set()
 for name,pin in ARCHIVE_PINS.items():
  raw=(incoming/name).read_bytes();req(hashlib.sha256(raw).hexdigest()==pin,'archive pin '+name)
  with zipfile.ZipFile(io.BytesIO(raw)) as z:
   for member,mh in MEMBER_PINS.items():
    if member in z.namelist():req(hashlib.sha256(z.read(member)).hexdigest()==mh,'member pin '+member);found.add(member)
 req(found==set(MEMBER_PINS),'member inventory')

def local_identities():
 d,g,lo,mi,eq,pl,hi=[V(n) for n in ('d','g','lo','neg','eq','pos','hi')]
 direct=S(*(M(w,sq(r)) for w,r in [(lo,S(d,g)),(mi,S(d,C(1))),(eq,d),(pl,S(d,C(-1))),(hi,S(d,neg(g)))]))
 total=S(lo,mi,eq,pl,hi);ext=S(lo,hi);inner=S(mi,pl)
 moment=S(M(total,sq(d)),scale(M(d,S(M(g,S(hi,neg(lo))),pl,neg(mi))),-2),M(sq(g),ext),inner)
 req(direct==moment,'general moment identity')
 f,k,b,h=[V(n) for n in ('f','k','beta','h')]
 req(S(M(S(f,k),b),M(S(f,k),h))==M(S(f,k),S(b,h)),'general vertex identity')
 req(S(total,neg(lo),neg(mi))==S(eq,pl,hi),'lower A')
 req(S(total,neg(lo))==S(mi,eq,pl,hi),'lower B')
 req(S(total,neg(hi),neg(pl))==S(lo,mi,eq),'upper A')
 req(S(total,neg(hi))==S(lo,mi,eq,pl),'upper B')
 return {'general_edge_moment_identity':True,'edge_moment_monomials':len(direct),'general_vertex_fold_identity':True,'shared_endpoint_indicator_identities':4}

def verify(root,incoming):
 authenticate(root,incoming)
 result=check(root/'sandpile_shared_arithmetic35_36.json')
 return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'author_pins':AUTHOR_PINS.copy(),'archive_pins':ARCHIVE_PINS.copy(),'member_pins':MEMBER_PINS.copy(),'local':local_identities(),'full_sources':result,'domain_scope':'Base: natural zeros. Real variant: nonnegative real zeros. Paid positive shift: positive integer coordinates; real theorem only on shifted coordinates at least1. External finite-prism family, no fixed-arity or universal84 operation consequence.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--incoming',type=Path,required=True);mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--output',type=Path);mode.add_argument('--expect',type=Path);a=ap.parse_args()
 result=verify(a.root,a.incoming)
 if a.expect:req(exact(result,json.loads(a.expect.read_text())),'exact receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({k:result['full_sources'][k] for k in ('complete_sources','paid_gates','coefficient_entries_compared','genuine_legal_zero_checks')},sort_keys=True))
if __name__=='__main__':main()
