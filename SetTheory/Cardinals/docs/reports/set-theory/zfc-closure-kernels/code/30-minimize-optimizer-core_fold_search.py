#!/usr/bin/env python3
"""Experimental core-state fold search with relabelled box interfaces.
The symbolic oracles are hypotheses, not automatically proof-valid. Every
survivor additionally must pass separate box checks before semantic claims.
"""
from pathlib import Path
import json,time
from context_search import cases, program_sites, check
from analyze_table import parse_table
ROOT=Path(__file__).parent
base,*_=parse_table(ROOT/'sources/zfc_254.tm')
base.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
base={k:v for k,v in base.items() if k[0]!=8}
T={(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in base.items()}
source=(ROOT/'sources/symexec.py').read_text().split('paths = json.load',1)[0]
source='SKIP ='+source.split('SKIP =',1)[1]
source=source.replace("    while fuel > 0:\n", "    while fuel > 0:\n        q = MAP.get(q,q)\n")
source=source.replace("if q == '73' and st[0] == 'mark':", "if q == MAP.get('73','73') and st[0] == 'mark':")
source=source.replace("if q == '43' and st[0] == 'mark':", "if q == MAP.get('43','43') and st[0] == 'mark':")
ns={'MAP':{},'T':T,'D0':40}
exec(compile(source,'adapted-symexec','exec'),ns)
SKIP=ns['SKIP'].copy()
allcases=cases(ns,program_sites(ROOT/'sources/Prog254.v'))
# Probe cases sorted by path length to cheaply reject most candidates.
order=sorted(range(len(allcases)),key=lambda j:len(allcases[j][1]))
for c in allcases: assert check(ns,c)
print('baseline',len(allcases),'passes',flush=True)
core=[0,1,2,3,4,5,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131]
roles=set(SKIP)|{'43','73'}
states=sorted(set(q for q,b in T),key=int)

def box(vs,mark=None):
 out=set();pos=0
 for i,v in enumerate(vs):
  pos+=1
  for j in range(v+1):
   if (i,j)!=(mark,0):out.add(pos)
   pos+=1
 return out

def box_probes(table,mapping):
 for vs in ([0]*9,[1]*9,[0,3,1,2,0,1,4,0,2,7,1]):
  for r in range(9):
   for op in ['mark','inc','dec']:
    q=next(k for k,v in SKIP.items() if v+1==r) if op=='mark' else '73' if op=='inc' else '43'
    q=mapping.get(q,q)
    tape=box(vs,None if op=='mark' else r);tape.add(-1);h=0
    work=vs.copy()
    if op=='inc':work[r]+=1
    if op=='dec' and vs[r]>0:work[r]-=1;work.append(0)
    exp_tape=box(work,r if op=='mark' else None);exp_tape.add(-1)
    exp_q=('2' if r==0 else '6') if op=='mark' else '48' if op=='inc' else '3' if vs[r]==0 else '63' if r==0 else '48'
    exp_q=mapping.get(exp_q,exp_q)
    for t in range(2000):
     if h<0:break
     row=table.get((q,int(h in tape)))
     if row is None:return False
     w,d,q=row
     if w:tape.add(h)
     else:tape.discard(h)
     h+=1 if d=='R' else -1
    if (q,h,tape)!=(exp_q,-1,exp_tape):return False
 return True

results={'candidates':0,'box_probe_survivors':0,'runtime_survivors':[],'scope':'Experimental relabelled oracle interface; no correctness claims until box contracts checked'}
start=time.monotonic()
for a in core:
 q=str(a)
 for p in states:
  if p==q or p=='96':continue
  if q in roles and p in roles:continue
  ns['MAP']={q:p}
  ns['SKIP']={(p if k==q else k):v for k,v in SKIP.items()}
  ns['T']={k:(w,d,p if t==q else t) for k,(w,d,t) in T.items() if k[0]!=q}
  results['candidates']+=1
  if not box_probes(ns['T'],{q:p}):continue
  results['box_probe_survivors']+=1
  if all(check(ns,allcases[j],fuel=500) for j in order):
   results['runtime_survivors'].append([q,p]);print('SURVIVOR',q,p,flush=True)
 results['elapsed']=time.monotonic()-start
 (ROOT/'core_fold_results.json').write_text(json.dumps(results,indent=2)+'\n')
 print('finished',q,round(results['elapsed'],1),'secs',flush=True)
