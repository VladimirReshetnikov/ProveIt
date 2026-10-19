from pathlib import Path
import re,json,sys,time,hashlib,importlib.util,os
from functools import cache
from collections import Counter
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE));import rebracket_axioms as h
FROZEN=Path(os.environ.get('BB246_REFERENCE',str(HERE.parent/'reference/context246'))).resolve()
spec=importlib.util.spec_from_file_location('prefix_affine',FROZEN/'sources/prior/prefix_affine.py');strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
s=(FROZEN/'sources/Prog254.v').read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
source=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',s)
conv={'CN':'ENode','CI':'EInc','CD':'EDecnz','CB':'EBreak','CC':'EContinue','CH':'EHalt'}
nodes={n:tuple(' '.join([conv[e.split()[0]]]+e.split()[1:]) for e in es) for n,es in enumerate(source)}
T={}
for line in (FROZEN/'machine/zfc_prefix246_old.tm').read_text().splitlines():
 if not line or line[0]=='#':continue
 q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),d,int(t))
q2nodes={};todo=[(96,0)];seen=set()
while todo:
 q,n=todo.pop()
 if (q,n) in seen:continue
 seen.add((q,n));q2nodes.setdefault(q,set()).add(n)
 for b in (0,1):
  w,d,t=T[q,b];e=nodes[n][b]
  if e.startswith('ENode ') and (w,d)==(b,'R'):todo.append((t,int(e.split()[1])))

def inc(p):
 if '0' not in p:return None
 return p[:p.rindex('0')]+'1'
def strip(p,bit,k):
 while k and p:
  k-=p[-1]==bit;p=p[:-1]
 return p
PHYSICAL=(6,2,0,4,3,7,8,5,1)
def enumerate_sites(nodes):
 sites=[]
 def walk(n,p):
  for b,e in enumerate(nodes[n]):
   pp=p+str(b);kind,*rr=e.split()
   if kind=='ENode':walk(int(rr[0]),pp)
   else:sites.append((pp,kind,int(rr[0]) if rr else None))
 walk(0,'');return sites

def check(table,nn):
 table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()}
 sites=enumerate_sites(nn);counts=Counter();begin=time.monotonic()
 for index,(p,op,r) in enumerate(sites):
  for zero in ((True,False) if op=='EDecnz' else (None,)):
   physical=PHYSICAL[r] if op in ('EInc','EDecnz') else r
   branch=(physical,zero) if op=='EDecnz' else None
   if op=='EInc' or op=='EDecnz' and not zero:succ=inc(p)
   elif op=='EDecnz':succ=inc(strip(p,'0',1))
   elif op=='EBreak':succ=inc(strip(p,'0',r))
   elif op=='EContinue':succ=strip(p,'1',r)
   else:succ=''
   effect=('inc',physical) if op=='EInc' else ('dec',physical) if op=='EDecnz' and not zero else None
   gapadd=1 if op=='EDecnz' and not zero else 0
   right=([('r',0,1,41+gapadd),('b',1),('box',('plain',effect))] if succ is None else [('b',int(b)) for b in succ]+[('r',0,1,40+gapadd-len(succ)),('b',1),('box',('plain',effect))])
   try:
    rules,lit=strict.run(table,p,branch,strict.canon([('b',1)],right),halt=op=='EHalt',fuel=2000)
    assert lit>0;counts['cases']+=1;counts['rules']+=sum(rules.values())
   except (AssertionError,KeyError) as ex:
    return dict(status='FAIL',index=index,pc=p,op=op,r=r,zero=zero,error=str(ex),counts=dict(counts),seconds=time.monotonic()-begin)
 return dict(status='PASS',counts=dict(counts),seconds=time.monotonic()-begin,source_sites=len(sites))

@cache
def fingerprint(n):
 return tuple(fingerprint(int(e.split()[1])) if e.startswith('ENode ') else e for e in nodes[n])

def recipe(q,r,side,a,b,c,s):
 nn=dict(nodes);changed=[]
 signatures={fingerprint(n) for n in q2nodes[q]}
 assert len(signatures)==1, 'ambiguous semantic state: use contextual synthesis'
 signature=next(iter(signatures))
 occurrences={n for n in nodes if fingerprint(n)==signature}
 for n in sorted(occurrences):
  e0,e1=nn[n];rn=int(nn[n][side].split()[1]);er0,er1=nn[rn]
  if side==0:nn[n]=(er0,'ENode '+str(rn));nn[rn]=(er1,e1)
  else:nn[n]=('ENode '+str(rn),er1);nn[rn]=(e0,er0)
  changed.append(dict(n=n,rn=rn,before=[nodes[n],nodes[rn]],after=[nn[n],nn[rn]]))
 tt=dict(T);tt[q,0]=(0,'R',a if side==0 else s);tt[q,1]=(1,'R',s if side==0 else c)
 incoming=[(qq,bb) for (qq,bb),(w,d,t) in tt.items() if t==r and qq!=r]
 if not incoming:
  tt={k:v for k,v in tt.items() if k[0]!=r}
 states={qq for qq,bb in tt};assert all(t==254 or t in states for w,d,t in tt.values())
 evidence={'q':q,'r':r,'side':side,'A':a,'B':b,'C':c,'existing':s,'working_states':len(states),'remaining_incoming':incoming,'source_changes':changed}
 print('START',q,r,'states',len(states),flush=True)
 try:
  cert,stats=h.bisimulation(nodes,nn);evidence['rm_bisimulation']=stats
  print('RM PASS',stats,flush=True)
 except Exception as ex:evidence['rm_bisimulation']={'status':'FAIL','error':str(ex)}
 evidence['affine']=check(tt,nn);print(evidence['affine'],flush=True)
 out=HERE/'rotation_candidates';out.mkdir(exist_ok=True)
 (out/f'rotation{q}.tm').write_text('#! start 95\n'+''.join(f'{qq} {bb} {w} {d} {t}\n' for (qq,bb),(w,d,t) in sorted(tt.items())))
 (out/f'rotation{q}.json').write_text(json.dumps(evidence,indent=2)+'\n')
 (out/f'rotation{q}_source.json').write_text(json.dumps(nn)+'\n')
 if evidence.get('rm_bisimulation',{}).get('all_reachable_operation_labels_match'):
  (out/f'rotation{q}_bisimulation.json').write_text(json.dumps(cert)+'\n')
 return evidence
if __name__=='__main__':
 baseline=check(T,nodes);print('BASELINE',baseline,flush=True)
 (HERE/'rotation_candidates').mkdir(exist_ok=True)
 (HERE/'rotation_candidates/baseline_affine.json').write_text(json.dumps(baseline,indent=2)+'\n')
 for args in [(178,208,1,23,24,206,16),(190,99,1,105,105,114,179),(219,178,1,206,23,208,205),(226,193,0,190,213,231,207)]:recipe(*args)
