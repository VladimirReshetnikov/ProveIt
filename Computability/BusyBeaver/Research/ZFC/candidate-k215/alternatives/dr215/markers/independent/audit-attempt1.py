#!/usr/bin/env python3
"""Independent finite audit of marker simulation; no builder imports.
The unbounded induction is in review.md. Python standard library only.
"""
from pathlib import Path
import argparse,json,hashlib,itertools

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 start=None;tab={}
 for line in Path(p).read_text().splitlines():
  if line.startswith('#! start '):
   assert start is None;start=int(line.split()[-1])
  elif line and not line.startswith('#'):
   q,a,b,d,z=line.split();q,a,b,z=map(int,(q,a,b,z));assert d in('L','R') and a in(0,1) and b in(0,1) and(q,a)not in tab
   tab[q,a]=(b,1 if d=='R'else -1,z)
 Q={q for q,a in tab};assert start in Q and set(tab)==set(itertools.product(Q,(0,1)))
 halt={z for b,d,z in tab.values()}-Q;assert len(halt)==1
 return start,tab,halt.pop()
def canon(st,tab,halt,mirror=False):
 order=[st];rename={st:0}
 for q in order:
  for bit in(0,1):
   z=tab[q,bit][2]
   if z!=halt and z not in rename:rename[z]=len(rename);order.append(z)
 assert len(rename)*2==len(tab)
 rename[halt]=len(rename)
 return tuple((bit,b,(-d if mirror else d),rename[z])for q in order for bit in(0,1)for b,d,z in[tab[q,bit]])
def advance(tab,q,h,t):
 assert h in t,'undeclared read in finite local block'
 b,d,z=tab[q,t[h]];t[h]=b;return z,h+d

# (old states; exceptional bit; predecessor marker at first/second old state)
SPECS={'m124':((124,127),0,(1,0)),'m160':((160,190),1,(0,1)),'m052':((52,176),0,(1,0))}
def main():
 p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,required=True);p.add_argument('--family',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--corpus',type=Path);a=p.parse_args()
 st,O,halt=read(a.baseline);assert st==0 and halt==254 and len(O)==430
 assert digest(a.baseline)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 corpus={};files=0;skipped=0
 if a.corpus:
  for f in a.corpus.rglob('*.tm'):
   try:
    cs,ct,ch=read(f)
    if len(ct)!=430:continue
    ck=canon(cs,ct,ch);corpus.setdefault(ck,[]).append(str(f.relative_to(a.corpus)));files+=1
   except(ValueError,AssertionError,UnicodeDecodeError,KeyError,TypeError):skipped+=1
 result=[]
 for folder in sorted(a.family.iterdir()):
  if not folder.is_dir():continue
  names=folder.name.split('-');assert all(n in SPECS for n in names)
  sn,N,hn=read(folder/'machine.native.tm');assert(sn,hn,len(N),set(N))==(st,halt,430,set(O))
  phi={q:q for q,_ in O};phi[halt]=halt;special={};constraints=[]
  for name in names:
   (q,r),bit,(x,y)=SPECS[name];phi[r]=q;special[q,bit]=x;special[r,bit]=y
   assert q!=st and r!=st
   for state,marker in((q,x),(r,y)):
    incoming={key:row for key,row in O.items()if row[2]==state};assert incoming
    if state!=176:
     assert all(w==marker and d==1 for w,d,z in incoming.values())
     reason='Every old incoming transition writes the marker and moves right.'
    else:
     assert incoming=={(156,1):(1,1,176),(165,0):(0,1,176),(193,0):(0,1,176)}
     assert {key:row for key,row in O.items()if row[2]==156}=={(189,1):(1,-1,156)}
     assert 156!=st
     reason='Other entrances write0; the only two-step route189/1,156/1 leaves current1, hence excludes exceptional read0.'
    constraints.append({'state':state,'exceptional_read':bit,'left_marker':marker,'incoming':[[*key,*v]for key,v in sorted(incoming.items())],'reason':reason})
  # Every one of the430 old rows is discharged, including common branches
  # of folded roles and targets redirected by the combined simulation map.
  cases=0;exceptional=0
  for (q,bit),oldrow in sorted(O.items()):
   markers=[special[q,bit]] if(q,bit)in special else[0,1]
   for left in markers:
    oldt={-1:left,0:bit};newt=dict(oldt)
    oq,oh=advance(O,q,0,oldt);nq,nh=phi[q],0
    ticks=3 if(q,bit)in special else1
    for tick in range(ticks):
     assert nq!=halt
     nq,nh=advance(N,nq,nh,newt)
    assert(nq,nh,newt)==(phi[oq],oh,oldt),(folder.name,q,bit,left)
    cases+=1;exceptional+=int(ticks==3)
  ds,D,dh=read(folder/'machine.tm');assert ds==0 and dh==215 and {q for q,_ in D}==set(range(215))
  assert canon(sn,N,hn)==canon(ds,D,dh),'dense table graph differs'
  key=canon(sn,N,hn);mirror=canon(sn,N,hn,True)
  same=corpus.get(key,[]);reflected=corpus.get(mirror,[])
  if a.corpus:assert not same and not reflected
  result.append({'variant':folder.name,'native_sha256':digest(folder/'machine.native.tm'),'dense_sha256':digest(folder/'machine.tm'),'old_rows_covered':430,'two_cell_cases':cases,'exceptional_cases':exceptional,'finite_proof_hypotheses':'PASS','incoming_invariants':constraints,'dense_equivalence':'PASS','corpus_matches':same,'reflected_corpus_matches':reflected})
 payload={'status':'INDEPENDENT_FINITE_MARKER_AUDIT_PASS','baseline_sha256':digest(a.baseline),'builder_imported':False,'scope':'Literal tables, complete incoming invariants, every old row under appropriate two-cell premise, common branches, arbitrary exterior untouched, dense graph identity and optional pinned-corpus nonisomorphism. Ordinary unbounded induction is separate; no new proof-assistant endpoint.','corpus_occurrences':files,'corpus_unique_graphs':len(corpus),'results':result}
 a.output.write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps({k:v for k,v in payload.items()if k!='results'},indent=2))
if __name__=='__main__':main()
