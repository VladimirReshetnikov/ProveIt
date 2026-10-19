"""Bounded search of one/two closed-subroutine associativity rotations.
Imported reference checkers are used only as a discovery filter.
"""
from pathlib import Path
import sys,json,time,copy
from collections import defaultdict,Counter
from functools import cache
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'decoder'))
import rotation_candidate as a
OUT=Path(__file__).resolve().parent
BEGAN=time.monotonic()

def analysis(T,nodes):
 pure={q for q,b in T if all(T[q,b][:2]==(b,'R') for b in (0,1))}
 qmap=defaultdict(set);todo=[(96,0)];seen=set()
 while todo:
  q,n=todo.pop()
  if (q,n) in seen:continue
  seen.add((q,n));qmap[q].add(n)
  for b in (0,1):
   w,d,t=T[q,b];e=nodes[n][b]
   if e.startswith('ENode ') and (w,d)==(b,'R'):todo.append((t,int(e.split()[1])))
 @cache
 def fp(n):return tuple(fp(int(e.split()[1])) if e.startswith('ENode ') else e for e in nodes[n])
 groups=defaultdict(set)
 for n in nodes:groups[fp(n)].add(n)
 bound=a.h.bounder(nodes)
 for q,ns in list(qmap.items()):
  fs={fp(n) for n in ns}
  if len(fs)==1:qmap[q]=set(groups[next(iter(fs))])
 closed={q for q,ns in qmap.items() if len({fp(n) for n in ns})==1 and all(bound('ENode '+str(n))==(0,0) for n in ns)}
 pairs=defaultdict(list)
 for q in pure:pairs[T[q,0][2],T[q,1][2]].append(q)
 incoming=Counter(t for w,d,t in T.values())
 moves=[]
 for q in sorted(pure&closed-{96}):
  for side in (0,1):
   r=T[q,side][2]
   if r not in pure&closed:continue
   A,B,C= (T[r,0][2],T[r,1][2],T[q,1][2]) if side==0 else (T[q,0][2],T[r,0][2],T[r,1][2])
   if not all(x in closed for x in (A,B,C)):continue
   targetpair=(B,C) if side==0 else (A,B)
   ss=pairs.get(targetpair,[])
   if not ss and incoming[r]==1:ss=[r]
   for s in ss:
    if q in (A,B,C,s) or r in (A,B,C):continue
    moves.append((q,r,side,A,B,C,s))
 return qmap,moves

def apply(T,nodes,qmap,m):
 q,r,side,A,B,C,s=m
 nn=dict(nodes);tt=dict(T)
 for n in sorted(qmap[q]):
  e0,e1=nodes[n];rn=int(nodes[n][side].split()[1]);er0,er1=nodes[rn]
  if side==0:nn[n]=(er0,'ENode '+str(rn));nn[rn]=(er1,e1)
  else:nn[n]=('ENode '+str(rn),er1);nn[rn]=(e0,er0)
 tt[q,0]=(0,'R',A if side==0 else s);tt[q,1]=(1,'R',s if side==0 else C)
 if s==r:
  tt[r,0]=(0,'R',B if side==0 else A);tt[r,1]=(1,'R',C if side==0 else B)
 elif not any(t==r for w,d,t in tt.values()):
  tt={k:v for k,v in tt.items() if k[0]!=r}
 # Exact same-row elimination is safe at the literal-table level.
 while True:
  states=sorted({q for q,b in tt});pairs={};merge=None
  for x in states:
   key=tt[x,0],tt[x,1]
   if key in pairs and x!=96:merge=(x,pairs[key]);break
   pairs[key]=x
  if merge is None:break
  gone,keep=merge
  tt={(x,b):(w,d,keep if t==gone else t) for (x,b),(w,d,t) in tt.items() if x!=gone}
 return tt,nn

qmap,moves=analysis(a.T,a.nodes)
print('initial moves',len(moves),flush=True)
seen=set();journal=[];winners=[];tried=0

def test(T,nn,ms):
 global tried
 key=tuple(sorted(T.items()))
 if key in seen:return
 seen.add(key)
 count=len(T)//2
 if count>=246:return
 tried+=1
 entry={'moves':ms,'states':count}
 try:
  cert,stats=a.h.bisimulation(a.nodes,nn);entry['bisimulation']=stats
  if not stats['all_reachable_operation_labels_match']:raise ValueError('RM mismatch')
  entry['affine']=a.check(T,nn)
 except Exception as ex:entry['error']=str(ex)
 journal.append(entry)
 print('TRIAL',tried,count,ms,entry.get('affine',entry.get('error')),flush=True)
 if entry.get('affine',{}).get('status')=='PASS':
  p=OUT/f'rotation_winner_{len(winners)}';p.mkdir(exist_ok=True)
  (p/'machine.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(T.items())))
  (p/'source.json').write_text(json.dumps(nn)+'\n');(p/'bisimulation.json').write_text(json.dumps(cert)+'\n')
  (p/'result.json').write_text(json.dumps(entry,indent=2)+'\n');winners.append(str(p))

for i,m in enumerate(moves):
 T1,N1=apply(a.T,a.nodes,qmap,m)
 test(T1,N1,[m])
 if time.monotonic()-BEGAN>300:break
 if len(T1)//2>246:continue
 try:map1,moves1=analysis(T1,N1)
 except Exception:continue
 for m1 in moves1:
  T2,N2=apply(T1,N1,map1,m1)
  test(T2,N2,[m,m1])
  if time.monotonic()-BEGAN>300:break
 if winners:break
print('DONE',tried,'journal',len(journal),'winners',winners,flush=True)
(OUT/'rotation_search_result.json').write_text(json.dumps({'seconds':time.monotonic()-BEGAN,'initial_moves':len(moves),'distinct_tables_screened':len(seen),'sub246_trials':tried,'winners':winners,'journal':journal},indent=2)+'\n')
