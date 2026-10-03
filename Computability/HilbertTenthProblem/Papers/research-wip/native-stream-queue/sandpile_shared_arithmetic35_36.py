#!/usr/bin/env python3
"""Bounded full-source shared arithmetic for Reports35/36; data-only dependencies."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import zipfile

ARCHIVES = {
 'Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip': '3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d',
 'Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip': '72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac'}
PINS = {
 'Research_Report35/evidence/composition/PROOF.md': '6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e',
 'Research_Report35/evidence/composition/prism_certificate.py': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2',
 'Research_Report36/evidence/real/PROOF.md': '9bc26062cc0e68fc8fee18290c347b309e2f711d208644ec541b29a5492071ae',
 'Research_Report36/evidence/real/approved_base/prism_certificate.py': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2'}
VF = ('z','ell','f','k','c','beta','g','h')
EF = ('lo','neg','eq','pos','hi','sigma')
STEPS = ((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))
FIXTURES = (('singleton6',(1,1,1)),('pair65',(2,1,1)),('cube65555555',(2,2,2)))
def need(ok,message):
 if not ok: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def stable(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def typed_equal(a,b):
 if type(a) is not type(b): return False
 if type(a) is dict: return a.keys()==b.keys() and all(typed_equal(a[k],b[k]) for k in a)
 if type(a) is list: return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
 return a==b

def authenticate(incoming):
 blobs={}
 for name,pin in ARCHIVES.items():
  raw=(incoming/name).read_bytes();need(sha(raw)==pin,'archive pin '+name)
  with zipfile.ZipFile(io.BytesIO(raw)) as z:
   for member,want in PINS.items():
    if member in z.namelist():
     data=z.read(member);need(sha(data)==want,'member pin '+member);blobs[member]=data
 need(set(blobs)==set(PINS),'complete member inventory')
 need(blobs['Research_Report35/evidence/composition/prism_certificate.py']==blobs['Research_Report36/evidence/real/approved_base/prism_certificate.py'],'unchanged approved base')


def geometry(lengths):
 points=[(x,y,z) for x in range(lengths[0]) for y in range(lengths[1]) for z in range(lengths[2])]
 index={p:i for i,p in enumerate(points)}
 edges=[];halo=[]
 for axis in range(3):
  for p in points:
   q=list(p);q[axis]+=1;q=tuple(q)
   if q in index:edges.append((index[p],index[q]))
  rest=[j for j in range(3) if j!=axis]
  for sign in (-1,1):
   for a in range(lengths[rest[0]]):
    for b in range(lengths[rest[1]]):
     p=[0,0,0];p[axis]=-1 if sign==-1 else lengths[axis];p[rest[0]]=a;p[rest[1]]=b
     q=p.copy();q[axis]-=sign;halo.append((tuple(p),index[tuple(q)]))
 neighbors=[[] for _ in points]
 for v,w in edges:neighbors[v].append(w);neighbors[w].append(v)
 V=len(points);E=len(edges);H=len(halo);S=sum(lengths[i]*lengths[j] for i,j in ((0,1),(0,2),(1,2)))
 need(E==3*V-S and H==2*S,'prism geometry')
 need(len({p for p,v in halo})==H,'distinct halo sites')
 for p,v in halo:
  adj=[index[q] for s in STEPS if (q:=tuple(p[j]+s[j] for j in range(3))) in index]
  need(adj==[v],'each halo has one inward neighbor')
 return dict(lengths=list(lengths),points=points,edges=edges,halo=halo,neighbors=neighbors,V=V,E=E,H=H)

def variables(g):
 return [f'v{i}_{f}' for i in range(g['V']) for f in VF]+[f'e{i}_{f}' for i in range(g['E']) for f in EF]+[f'halo{i}' for i in range(g['H'])]

class Circuit:
 def __init__(self,ports):self.rows=[];self.ports=ports
 def op(self,op,a,b):
  # Only exact constant and zero/unit folds; no automatic CSE or reassociation.
  if type(a) is int and type(b) is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+' and a==0:return b
  if op in ('+','-') and b==0:return a
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  n='g'+str(len(self.rows));self.rows.append([n,op,a,b]);return n
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def square(self,a):return self.mul(a,a)
 def sum(self,xs):
  out=0
  for x in xs:out=self.add(out,x)
  return out

def build(g,eta,real,moment,positive):
 original=variables(g);ports=['p_'+n for n in original] if positive else original.copy()
 c=Circuit(ports);leaf={n:c.sub(p,1) if positive else p for n,p in zip(original,ports)}
 v=[{f:leaf[f'v{i}_{f}'] for f in VF} for i in range(g['V'])]
 e=[{f:leaf[f'e{i}_{f}'] for f in EF} for i in range(g['E'])]
 u=[c.add(x['k'],x['c']) for x in v]
 ranks=[c.add(c.add(u[i],x['c']),x['beta']) if g['neighbors'][i] else None for i,x in enumerate(v)]
 As=[[] for _ in v];Bs=[[] for _ in v];edge_terms=[];edge_cuts=[]
 for i,(a,b) in enumerate(g['edges']):
  x=e[i];lo,neg,eq,pos,hi,sigma=(x[f] for f in EF)
  d=c.sub(ranks[b],ranks[a]);gap=c.add(sigma,2)
  ext=c.add(lo,hi);inner=c.add(neg,pos);middle=c.add(inner,eq);S=c.add(ext,middle)
  lowerB=c.sub(S,lo);lowerA=c.sub(lowerB,neg);upperB=c.sub(S,hi);upperA=c.sub(upperB,pos)
  As[a].append(lowerA);Bs[a].append(lowerB);As[b].append(upperA);Bs[b].append(upperB)
  simplex=c.square(c.sub(S,1));inactive=c.mul(middle,sigma)
  if moment:
   d2=c.square(d);g2=c.square(gap)
   linear=c.add(c.mul(gap,c.sub(hi,lo)),c.sub(pos,neg))
   cross=c.mul(d,linear)
   weighted=c.add(c.add(c.sub(c.mul(S,d2),c.add(cross,cross)),c.mul(g2,ext)),inner)
   terms=[simplex,weighted,inactive]
  else:
   args=((lo,c.add(d,gap)),(neg,c.add(d,1)),(eq,d),(pos,c.sub(d,1)),(hi,c.sub(d,gap)))
   weighted=[c.mul(w,c.square(r)) for w,r in args]
   terms=[simplex,*weighted,inactive]
  edge_terms.extend(terms)
  edge_cuts.append(dict(delta=d,gap_plus_two=gap,ext=ext,inner=inner,middle=middle,S=S,A_lower=lowerA,B_lower=lowerB,A_upper=upperA,B_upper=upperB))
 vertex_terms=[]
 for i,x in enumerate(v):
  z,ell,f,k,cc,beta,gg,h=(x[f] for f in VF)
  A=c.sum(As[i]);B=c.sum(Bs[i]);neighbors=c.sum(u[j] for j in g['neighbors'][i])
  balance=c.sub(c.sub(c.add(z,c.mul(6,u[i])),neighbors),eta[i])
  vertex_terms.extend([c.square(balance),c.square(c.sub(c.add(z,ell),5)),c.square(c.sub(c.add(f,u[i]),1))])
  fk=c.add(f,k)
  if moment:vertex_terms.append(c.mul(fk,c.add(beta,h)))
  else:vertex_terms.extend([c.mul(fk,beta),c.mul(fk,h)])
  vertex_terms.append(c.mul(u[i],c.square(c.sub(c.sub(z,A),gg))))
  vertex_terms.append(c.mul(f,c.add(gg,u[i]) if real else gg))
  vertex_terms.append(c.mul(cc,c.square(c.sub(c.sub(c.sub(B,z),1),h))))
 halo_terms=[c.square(c.sub(c.add(u[v],leaf[f'halo{i}']),5)) for i,(_,v) in enumerate(g['halo'])]
 terms=vertex_terms+edge_terms+halo_terms
 final_start=len(c.rows);out=c.sum(terms)
 packet=dict(ports=ports,source=c.rows,output=out,mode='moment_merged' if moment else 'direct_unmerged',variant='real' if real else 'base',positive_coordinates=positive,eta=eta.copy(),geometry={k:g[k] for k in ('lengths','V','E','H')},term_outputs=terms,final_sum_start=final_start,edge_cuts=edge_cuts)
 return packet

# Independent coefficient reference: direct report affine forms/summands, never
# the circuit's moment identity or shared comparison formulas.
def constant(n):return {():n} if n else {}
def variable(n):return {(n,):1}
def plus(a,b,sgn=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+sgn*c
 return {m:c for m,c in out.items() if c}
def times(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
 return {m:c for m,c in out.items() if c}
def summation(xs):
 out={}
 for x in xs:out=plus(out,x)
 return out
def lin(*terms):
 return summation(times(constant(c),constant(1) if n is None else variable(n)) for n,c in terms)
def ref_expand(g,eta,real):
 v=[{f:f'v{i}_{f}' for f in VF} for i in range(g['V'])]
 u=[lin((x['k'],1),(x['c'],1)) for x in v]
 rank=[lin((x['k'],1),(x['c'],2),(x['beta'],1)) for x in v]
 Ap=[[] for _ in v];Bp=[[] for _ in v];terms=[]
 for i,(a,b) in enumerate(g['edges']):
  x={f:variable(f'e{i}_{f}') for f in EF};d=plus(rank[b],rank[a],-1)
  terms.append(times(plus(summation(x[f] for f in EF[:-1]),constant(1),-1),plus(summation(x[f] for f in EF[:-1]),constant(1),-1)))
  for label,sgn,n in (('lo',1,2),('neg',0,1),('eq',0,0),('pos',0,-1),('hi',-1,-2)):
   r=plus(plus(d,constant(n)),times(constant(sgn),x['sigma']))
   terms.append(times(x[label],times(r,r)))
  terms.append(times(summation(x[f] for f in ('neg','eq','pos')),x['sigma']))
  Ap[a].append(summation(x[f] for f in ('eq','pos','hi')));Bp[a].append(summation(x[f] for f in ('neg','eq','pos','hi')))
  Ap[b].append(summation(x[f] for f in ('lo','neg','eq')));Bp[b].append(summation(x[f] for f in ('lo','neg','eq','pos')))
 for i,x in enumerate(v):
  z,ell,f,k,cc,beta,gg,h=(variable(x[f]) for f in VF)
  A=summation(Ap[i]);B=summation(Bp[i])
  residuals=[plus(plus(plus(z,times(constant(6),u[i])),summation(u[j] for j in g['neighbors'][i]),-1),constant(eta[i]),-1),plus(plus(z,ell),constant(5),-1),plus(summation((f,k,cc)),constant(1),-1)]
  terms.extend(times(r,r) for r in residuals)
  terms.append(times(plus(f,k),beta));terms.append(times(plus(f,k),h))
  r=plus(plus(z,A,-1),gg,-1);terms.append(times(u[i],times(r,r)))
  terms.append(times(f,summation((gg,k,cc)) if real else gg))
  r=plus(plus(plus(B,z,-1),constant(1),-1),h,-1);terms.append(times(cc,times(r,r)))
 for i,(_,vtx) in enumerate(g['halo']):
  r=plus(plus(u[vtx],variable(f'halo{i}')),constant(5),-1);terms.append(times(r,r))
 return summation(terms)

def shifted_poly(p):
 out={}
 for m,coef in p.items():
  term=constant(coef)
  for n in m:term=times(term,lin(('p_'+n,1),(None,-1)))
  out=plus(out,term)
 return out

def execute(packet,values):
 env=dict(values)
 for n,op,a,b in packet['source']:
  a=a if type(a) is int else env[a];b=b if type(b) is int else env[b]
  env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env

def expand_source(packet):
 env={n:variable(n) for n in packet['ports']}
 for n,op,a,b in packet['source']:
  a=constant(a) if type(a) is int else env[a];b=constant(b) if type(b) is int else env[b]
  env[n]=times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
 return env[packet['output']]

def ledger(packet):
 known=set(packet['ports']);need(len(known)==len(packet['ports']),'distinct ports');defs={};counts=Counter()
 for n,op,a,b in packet['source']:
  need(n not in known and op in ('+','-','*'),'fresh opcode')
  need(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'closed operands')
  defs[n]=(op,a,b);known.add(n);counts['M' if op=='*' else 'A']+=1
 live=set();todo=[packet['output']]
 while todo:
  n=todo.pop()
  if type(n) is int or n in live:continue
  live.add(n)
  if n in defs:todo.extend(defs[n][1:])
 need(live==known,'all supplied coordinates and gates live')
 need(len(packet['source'])-packet['final_sum_start']==len(packet['term_outputs'])-1,'complete sum charge')
 need(len(packet['ports'])==8*packet['geometry']['V']+6*packet['geometry']['E']+packet['geometry']['H'],'all witnesses counted')
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],witnesses=len(packet['ports']),terms=len(packet['term_outputs']),final_additions=len(packet['term_outputs'])-1,positive_adapter_additions=len(packet['ports']) if packet['positive_coordinates'] else 0)

def coeff_data(p):return [[list(m),c] for m,c in sorted(p.items())]
def own_witness(g,eta):
 # Literal legal stabilization on the tiny fixture, followed by parallel burn.
 z=eta.copy();u=[0]*g['V'];trace=[]
 while any(x>=6 for x in z):
  i=next(j for j,x in enumerate(z) if x>=6);z[i]-=6;u[i]+=1;trace.append(i)
  need(u[i]<=1,'fixture has binary odometer')
  for j in g['neighbors'][i]:z[j]+=1
 rank=[0]*g['V'];remaining={i for i,x in enumerate(u) if x};layers=[]
 while remaining:
  layer=sorted(i for i in remaining if z[i]>=sum(j in remaining for j in g['neighbors'][i]))
  need(layer,'burning fixture');layers.append(layer)
  for i in layer:rank[i]=len(layers)
  remaining.difference_update(layer)
 w={}
 for i in range(g['V']):
  A=sum(rank[j]>=rank[i] for j in g['neighbors'][i]);B=sum(rank[j]+1>=rank[i] for j in g['neighbors'][i])
  vals=(z[i],5-z[i],int(rank[i]==0),int(rank[i]==1),int(rank[i]>=2),max(0,rank[i]-2),z[i]-A if u[i] else 0,B-z[i]-1 if rank[i]>=2 else 0)
  w.update({f'v{i}_{f}':value for f,value in zip(VF,vals)})
 for i,(v,x) in enumerate(g['edges']):
  d=rank[x]-rank[v];case=0 if d<=-2 else 1 if d==-1 else 2 if d==0 else 3 if d==1 else 4
  w.update({f'e{i}_{f}':int(j==case) for j,f in enumerate(EF[:-1])});w[f'e{i}_sigma']=max(0,abs(d)-2)
 for i,(_,v) in enumerate(g['halo']):w[f'halo{i}']=5-u[v]
 need(set(w)==set(variables(g)) and all(type(v) is int and v>=0 for v in w.values()),'complete natural fixture')
 return w,dict(legal_firing_order=trace,odometer=u,stable_interior=z,burning_layers=layers,ranks=rank,halo_final=[u[v] for _,v in g['halo']])

def verify(incoming):
 authenticate(incoming);forms=[];totals=Counter();bills=[]
 for name,lengths in FIXTURES:
  g=geometry(lengths);eta=[6]+[5]*(g['V']-1);w,trace=own_witness(g,eta)
  references={real:ref_expand(g,eta,real) for real in (False,True)}
  difference=plus(references[True],references[False],-1)
  expected=summation(times(variable(f'v{i}_f'),lin((f'v{i}_k',1),(f'v{i}_c',1))) for i in range(g['V']))
  need(difference==expected,'exact real-upgrade coefficient delta')
  need(set(references[False])==set(references[True]) and max(map(abs,references[False].values()))==max(map(abs,references[True].values())),'support and height unchanged by real upgrade')
  for real in (False,True):
   reference=references[real]
   need(max(map(len,reference))==3 and reference[tuple(sorted(('v0_k','v0_z','v0_z')))]==1,'exact cubic coefficient')
   for positive in (False,True):
    ref=shifted_poly(reference) if positive else reference
    need(max(map(len,ref))==3,'shift preserves exact degree')
    pair=[]
    for moment in (False,True):
     p=build(g,eta,real,moment,positive);bill=ledger(p);actual=expand_source(p);need(actual==ref,'entire coefficient identity')
     V,E,H=(g[n] for n in ('V','E','H'));isolated=int(V==1)
     expected_M=(10*V+8*E+H) if moment else (11*V+12*E+H)
     expected_A=21*V+(27 if moment else 28)*E+3*H-1-isolated+int(real)*V+int(positive)*len(w)
     need(bill['M']==expected_M and bill['A']==expected_A,'closed formulas for declared positive-interior zero-exterior fixtures')
     vals={'p_'+n:v+1 for n,v in w.items()} if positive else w.copy()
     need(execute(p,vals)[p['output']]==0,'genuine complete zero')
     for case in range(8):
      vv={n:Fraction((i+3*case)%13-6,3) if case>=5 else (i+3*case)%13-6 for i,n in enumerate(p['ports'])}
      e=execute(p,vv);want=sum(c*product(vv[n] for n in m) for m,c in ref.items());need(e[p['output']]==want,'signed/rational coefficient evaluation')
     p['ledger']=bill;p['exact_degree']=3;p['coefficient_sha256']=sha(stable(coeff_data(ref)));p['collected_monomials']=len(ref);p['coefficient_height']=max(map(abs,ref.values()))
     pair.append(p);forms.append(dict(fixture=name,packet=p,zero_witness=vals,legal_and_burning_trace=trace))
     totals.update(complete_sources=1,live_gates=bill['operations'],full_coefficient_identities=1,genuine_zeros=1,offzero_evaluations=8,rational_evaluations=3)
    before,after=(p['ledger'] for p in pair)
    need(before['M']-after['M']==g['V']+4*g['E'] and before['A']-after['A']==g['E'],'precisely paid saving')
    need(before['terms']-after['terms']==g['V']+4*g['E'],'complete changed final sum')
    bills.append(dict(fixture=name,real=real,positive=positive,direct=before,moment=after,saved_operations=g['V']+5*g['E']))
  # Every positive adaptation charges one actual subtraction per old coordinate.
  subset=forms[-8:]
  for real in (False,True):
   for mode in ('direct_unmerged','moment_merged'):
    packets=[f['packet'] for f in subset if f['packet']['variant']==('real' if real else 'base') and f['packet']['mode']==mode]
    natural,positive=sorted(packets,key=lambda p:p['positive_coordinates'])
    need(positive['ledger']['M']==natural['ledger']['M'] and positive['ledger']['A']==natural['ledger']['A']+len(w),'all positive shifts paid')
  for positive in (False,True):
   for mode in ('direct_unmerged','moment_merged'):
    packets=[f['packet'] for f in subset if f['packet']['positive_coordinates']==positive and f['packet']['mode']==mode]
    base,real=sorted(packets,key=lambda p:p['variant']=='real')
    need(real['ledger']['M']==base['ledger']['M'] and real['ledger']['A']==base['ledger']['A']+g['V'],'shared real-upgrade costs')
 # Exact original nonnegative-real false zero; not a natural witness.
 g=geometry((1,1,1));bad={n:Fraction(0) for n in variables(g)}
 bad.update(v0_ell=Fraction(5),v0_f=Fraction(5,6),v0_k=Fraction(1,6))
 for i in range(6):bad[f'halo{i}']=Fraction(29,6)
 for moment in (False,True):
  p=build(g,[1],False,moment,False);need(execute(p,bad)[p['output']]==0,'old real false zero')
  p=build(g,[1],True,moment,False);need(execute(p,bad)[p['output']]==Fraction(5,36),'real upgrade rejects fractional tuple')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),archive_pins=ARCHIVES,member_pins=PINS,counts=dict(totals),comparisons=bills,forms=forms,rational_regression=dict(base_value='0',real_value='5/36',eta=1),scope='24 complete finite-prism sources: three fixtures, two polynomial variants, two shared arithmetic schedules, and natural/paid-positive coordinates. Full all-value identities; no universal operation bound, archived execution, or loader audit.')

def product(xs):
 p=1
 for x in xs:p*=x
 return p

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--incoming',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 result=json.loads(json.dumps(verify(a.incoming or a.repo/'docs/incoming')))
 if a.expect:need(typed_equal(result,json.loads(a.expect.read_text())),'saved exact typed receipt')
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',**result['counts']),sort_keys=True))
if __name__=='__main__':main()
