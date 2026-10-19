#!/usr/bin/env python3
"""New bounded color-transport search admitting actual unprotected state deletion.
Inputs are pinned archive2 sources; outputs require independent binary audit.
"""
from pathlib import Path
import sys,json,collections,time,random,argparse,functools
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
import os
OUT=Path(os.environ.get('ZFC_LOGIC_OUTPUT',str(ROOT/'experiments/logic/rerun'))).resolve()
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(HERE))
import rotation_search as r
import grammar_stats as gs
import compile_rotated as c
raw=(c.BASE/'sources/Prog254.v').read_bytes();base=r.load(raw)
assert c.oldroot==base and c.entries==r.entries
leaves,cases,by,first=r.a.read_program(raw)
C0={s:next(iter(c.sigq[s])) for s in c.oldsigs}
F={tuple(e['row']) for e in json.load(open(ROOT/'experiments/logic/inputs/original_terminal_dependencies.json'))['rows']}
shared={q for q,ss in c.qsig.items() if len(ss)>1}
support=set(q for q,b in c.T)-set(C0.values())
protected=shared|{q for q,b in F}|{c.T[row][2] for row in F}
protected|={v[2] for (q,b),v in c.T.items() if q in support}
oldctx={};cursor=0
DEDICATED={('CI',1):70,('CI',3):201,('CI',4):169,('CI',5):72,('CI',6):39,('CI',7):93,
           ('CD',1):49,('CD',3):21,('CD',4):173,('CD',5):53,('CD',6):25}

def oldwalk(n,p):
 global cursor
 lo=cursor
 for b,e in enumerate(c.ns[n]):
  if e[0]=='CN':oldwalk(e[1],p+str(b))
  else:cursor+=1
 if c.nq[n] in shared:oldctx[lo,cursor]=(c.nq[n],('001'+p)[-2:])
oldwalk(0,'')

def context(root,colors,suffix=4):
 cursor=0;valid=True;count=0
 def rec(n,p,parentrow=None):
  nonlocal cursor,valid,count
  e=r.entries[n]
  if e[0]!='N':
   k=max(suffix,4) if e[0] in ('CB','CC','CH') else 0 if e in DEDICATED and parentrow not in F else suffix
   if k and ('0'*k+'1'+p)[-k:]!=('0'*k+'1'+leaves[cursor][0])[-k:]:valid=False
   cursor+=1;return
  lo=cursor;rec(e[1],p+'0',(colors[n],0));rec(e[2],p+'1',(colors[n],1))
  if colors[n] in shared:
   count+=1
   if oldctx.get((lo,cursor))!=(colors[n],('001'+p)[-2:]):valid=False
 rec(root,'')
 return valid and count==len(oldctx)

def compile_graph(root,colors):
 qs=collections.defaultdict(list)
 for s,q in colors.items():qs[q].append(s)
 T={k:v for k,v in c.T.items() if k[0] in support or k[0] in qs}
 for q,ss in qs.items():
  for b in (0,1):
   wants=[]
   for s in ss:
    child=r.entries[r.entries[s][b+1]]
    if child[0]=='N':row=(b,'R',colors[r.entries[s][b+1]])
    else:
     if child in DEDICATED and (q,b) not in F:row=(b,'R',DEDICATED[child])
     else:
      opts={c.T[q,b] for sg in c.qsig.get(q,set()) if c.entries[c.entries[sg][b+1]]==tuple(child)}
      fallback=c.term[tuple(child)+(b,)].most_common(1)
      if len(opts)!=1 and not fallback:return
      row=next(iter(opts)) if len(opts)==1 else fallback[0][0]
    wants.append(row)
   if len(set(wants))==1:T[q,b]=wants[0]
   elif q not in shared:return
 if any(T.get(row)!=c.T[row] for row in F):return
 if any(s!=254 and (s,0) not in T for w,d,s in T.values()):return
 return T

def rotate(state,pivot,direction,swap):
 root,colors,T=state;p=r.entries[pivot];inner=p[2 if direction=='left' else 1]
 if r.entries[inner][0]!='N':return
 if colors[pivot] in shared or colors[inner] in shared:return
 qp,qi=colors[pivot],colors[inner]
 if qp==qi:return
 x=r.entries[inner]
 if direction=='left':ni=r.mk(('N',p[1],x[1]));replacement=r.mk(('N',ni,x[2]));desc=[p[1],x[1],x[2]]
 else:ni=r.mk(('N',x[2],p[2]));replacement=r.mk(('N',x[1],ni));desc=[x[1],x[2],p[2]]
 nc={};memo={};merge={};bad=False
 def canon(q):
  while q in merge:q=merge[q]
  return q
 def add(s,q):
  nonlocal bad
  if s in nc and canon(nc[s])!=canon(q):
   a,b=canon(q),canon(nc[s])
   if a in protected and b in protected:bad=True;return
   if a in protected:a,b=b,a
   merge[a]=b
  nc[s]=canon(q)
 def keep(s):
  e=r.entries[s]
  if e[0]=='N':add(s,colors[s]);keep(e[1]);keep(e[2])
 def rec(s):
  if s in memo:return memo[s]
  e=r.entries[s]
  if e[0]!='N':return s
  if s==pivot:
   # Descendants first give existing interned subtrees priority in a merger.
   for d in desc:keep(d)
   add(ni,qp if swap else qi);add(replacement,qi if swap else qp);ans=replacement
  else:
   ans=r.mk(('N',rec(e[1]),rec(e[2])));add(ans,colors[s])
  memo[s]=ans;return ans
 nr=rec(root)
 if bad:return
 reach=set(r.reachable(nr));nc={s:canon(q) for s,q in nc.items() if s in reach}
 if set(nc)!=reach or len(reach)>203:return
 if not set(colors.values())-set(nc.values())<=set(colors.values())-protected:return
 nt=compile_graph(nr,nc)
 if nt is None:return
 return nr,nc,nt

@functools.cache
def active_stats(i):
 e=r.entries[i]
 if e[0]!='N':return (0,2 if e[0]=='CD' else 1 if e[0]=='CI' else 0,(2 if e[0]=='CD' else 1 if e[0]=='CI' else 0,))
 ld,lw,lh=active_stats(e[1]);rd,rw,rh=active_stats(e[2]);h=[0]*max(len(lh)+bool(lw),len(rh))
 for j,v in enumerate(lh):h[j]+=v
 for j,v in enumerate(rh):h[j]+=v
 if lw:h[ld]-=lw;h[ld+1]+=lw
 while len(h)>1 and not h[-1]:h.pop()
 return ld+1,lw,tuple(h)

def score(state):
 root,cs,T=state;st=gs.stats(root);hist=st[5];active=active_stats(root)[2]
 return (len(T)//2,sum(active[7:]),len(cs))+tuple(hist[j] if j<len(hist) else 0 for j in range(6,-1,-1))+(st[3],)

def save(state,name,meta):
 root,cs,T=state
 r.dump_graph(root,OUT/(name+'.json'),dict(meta,score=score(state)))
 (OUT/(name+'_roles.json')).write_text(json.dumps({'roles':cs},separators=(',',':'))+'\n')
 c.save_table(T,OUT/(name+'.tm'))
 print('SAVED',name,score(state),flush=True)

def rebase_rotated(graphpath=None,tablepath=None):
 global base,C0,F,shared,support,protected,oldctx,leaves,cases
 A6=ROOT/'experiments/logic/inputs'
 data=json.loads((Path(graphpath) if graphpath else A6/'rebracket202_minimal.json').read_text())
 memo={}
 if 'nodes' in data:nodes={int(k):v for k,v in data['nodes'].items()}
 else:
  es=data['entries'];nodes={}
  for k,e in es.items():
   if e[0]=='N':
    ns=[]
    for child in e[1:]:
     ce=es[str(child)];ns.append(('N',child) if ce[0]=='N' else (ce[0][1:],ce[1]) if ce[0]!='CH' else ('H',))
    nodes[int(k)]=ns
 def edge(e):
  if e[0]=='N':return rec(e[1])
  return r.mk(('C'+e[0],e[1] if len(e)>1 else None))
 def rec(i):
  if i not in memo:memo[i]=r.mk(('N',edge(nodes[i][0]),edge(nodes[i][1])))
  return memo[i]
 base=rec(data['root']);c.T={}
 for line in (Path(tablepath) if tablepath else A6/'zfc_rotated246_old.tm').read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,t=line.split();c.T[int(q),int(b)]=int(w),d,int(t)
 def firstq(p):
  q=96;h=0;ones={-1}|{i for i,b in enumerate(p) if b=='1'}
  for _ in range(300):
   if h==len(p):return q
   w,d,q=c.T[q,int(h in ones)]
   (ones.add if w else ones.discard)(h);h+=1 if d=='R' else -1
  raise AssertionError(('first-state',p))
 c.qsig=collections.defaultdict(set);c.sigq=collections.defaultdict(set);c.term=collections.defaultdict(collections.Counter)
 ls=[];nodeocc=[]
 def visit(n,p,qs):
  e=r.entries[n]
  if e[0]!='N':ls.append((p,*e,qs));return
  q=firstq(p);c.qsig[q].add(n);c.sigq[n].add(q);nodeocc.append((n,p,q))
  for b,s in enumerate(e[1:]):
   child=r.entries[s]
   if child[0]!='N':c.term[child+(b,)][c.T[q,b]]+=1
   visit(s,p+str(b),qs+[q])
 visit(base,'',[])
 assert all(len(qs)==1 for qs in c.sigq.values()),[(s,qs) for s,qs in c.sigq.items() if len(qs)>1]
 C0={s:next(iter(qs)) for s,qs in c.sigq.items()};c.entries=r.entries;c.oldsigs=set(C0)
 shared={q for q,ss in c.qsig.items() if len(ss)>1};support={q for q,b in c.T}-set(C0.values())
 sys.path.insert(0,str(c.BASE/'code'))
 import check_literal_instructions as lit
 F=set();counter=0;ticks=0
 for p,op,x,qs in ls:
  for positive in ((False,True) if op=='CD' else (None,)):
   regs=[i*3%7 for i in range(9)]
   if op=='CD':regs[lit.PHYSICAL[x]]=1 if positive else 0
   target=lit.expected(p,op,x,regs,[0],0,64);ones=lit.paint(p,64,regs,[0],0);q=96;h=0
   for tick in range(2000):
    b=int(h in ones)
    if q in c.qsig and not (0<=h<len(p) and q==qs[h] and b==int(p[h])):F.add((q,b))
    w,d,q=c.T[q,b];(ones.add if w else ones.discard)(h);h+=1 if d=='R' else -1
    if q==254 or target is not None and q==96 and h==target[0] and ones==target[1]:break
   else:raise AssertionError(('newbase finite frame',counter,p))
   ticks+=tick+1;counter+=1
 assert counter==8391
 protected=shared|{q for q,b in F}|{c.T[row][2] for row in F}|{v[2] for (q,b),v in c.T.items() if q in support}
 oldctx={};cursor=0
 def contexts(n,p):
  nonlocal cursor
  e=r.entries[n]
  if e[0]!='N':cursor+=1;return
  lo=cursor;contexts(e[1],p+'0');contexts(e[2],p+'1')
  if C0[n] in shared:oldctx[lo,cursor]=(C0[n],('001'+p)[-2:])
 contexts(base,'')
 if graphpath:
  from bisect import bisect_right
  depth=max(len(p) for p,_,_,_ in ls);starts=[int(p,2)<<(depth-len(p)) for p,_,_,_ in ls]
  def decode(p):
   if p is None:return None
   i=bisect_right(starts,(int(p,2) if p else 0)<<(depth-len(p)))-1
   assert '1' not in p[len(ls[i][0]):]
   return i
  cases=[(i,pos,decode(r.successor(p,op,x,pos))) for i,(p,op,x,qs) in enumerate(ls) for pos in ((False,True) if op=='CD' else (None,))]
  assert len(cases)==8391
 else:assert [(op,x) for p,op,x,qs in ls]==[(op,x) for p,op,x,*_ in leaves]
 # The rebased source has its own complete finite control reference.
 leaves=[(p,op,x,0,0) for p,op,x,qs in ls]
 (OUT/(('commuted' if graphpath else 'rotated')+'_rebase_evidence.json')).write_text(json.dumps(dict(source_pairs=len(C0),decoder_colors=len(set(C0.values())),support_colors=len(support),shared_colors=sorted(shared),borrowed_rows=sorted(F),finite_cases=counter,literal_steps=ticks),indent=2)+'\n')
 print('REBASE',len(C0),len(set(C0.values())),len(support),'borrowed',len(F),'shared',len(shared),flush=True)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=240);ap.add_argument('--seed',type=int,default=0);ap.add_argument('--suffix',type=int,default=4);ap.add_argument('--start',default='baseline');ap.add_argument('--metric',choices=['states','tails'],default='states');ap.add_argument('--rebase-rotated',action='store_true');ap.add_argument('--rebase-graph');ap.add_argument('--rebase-table');args=ap.parse_args()
 if args.rebase_rotated or args.rebase_graph:rebase_rotated(args.rebase_graph,args.rebase_table)
 rng=random.Random(args.seed);start=time.monotonic();counts=collections.Counter();seen=set();elite=[];seq=0
 if args.start=='baseline':state=(base,C0,c.T.copy())
 else:
  data=json.loads(Path(args.start).read_text());memo={}
  def imp(i):
   if i not in memo:
    e=data['entries'][str(i)];memo[i]=r.mk(('N',imp(e[1]),imp(e[2]))) if e[0]=='N' else r.mk(tuple(e))
   return memo[i]
  root=imp(data['root']);rr=json.loads(Path(args.start.replace('.json','_roles.json')).read_text())['roles'];cs={memo[int(s)]:q for s,q in rr.items()}
  state=(root,cs,compile_graph(root,cs));assert state[2] is not None
 best=score(state);elite=[state];save(state,f's{args.seed}_initial',dict(suffix=args.suffix))
 while time.monotonic()-start<args.seconds:
  admitted=[];moves=[]
  for pivot in r.reachable(state[0]):
   for dr in ('left','right'):
    for swap in (False,True):moves.append((pivot,dr,swap))
  rng.shuffle(moves)
  for move in moves:
   counts['recipes']+=1;new=rotate(state,*move)
   if new is None:continue
   nr,nc,nt=new;key=(nr,tuple(sorted(nc.items())))
   if key in seen:continue
   seen.add(key);counts['colored_admitted']+=1;st=gs.stats(nr)
   if st[4]>7 or st[3]>64:continue
   if not context(nr,nc,args.suffix):continue
   counts['semantic_checks']+=1
   if r.check(nr,leaves,cases,set()) is None:continue
   counts['exact_source']+=1;s=score(new)
   # Full source equivalence is independent of chosen objective.
   admitted.append((s,new,move))
   if s<best:
    best=s;seq+=1;save(new,f's{args.seed}_best_{seq:03}',dict(move=move,seconds=time.monotonic()-start,counts=dict(counts),suffix=args.suffix))
    if s[0]<246:
     print('STATE_REDUCTION',flush=True)
   if time.monotonic()-start>=args.seconds:break
  if admitted:
   admitted.sort(key=lambda x:x[0] if args.metric=='states' else (x[0][1],x[0][0],*x[0][2:]))
   # Mix strict descent, equal-score plateaus, and short uphill escapes.
   good=[a for a in admitted if a[0][:3]<=score(state)[:3]]
   choice=rng.choice((good[:20] if good and rng.random()<.8 else admitted[:30]))
   state=choice[1]
   elite.extend(x[1] for x in admitted[:3]);elite.sort(key=score);elite=elite[:60]
  else:state=rng.choice(elite)
  counts['rounds']+=1
  if counts['rounds']%10==0:print('ROUND',counts['rounds'],best,dict(counts),time.monotonic()-start,flush=True)
 result=dict(best=best,counts=dict(counts),seconds=time.monotonic()-start,suffix=args.suffix,status='bounded source/color search; binary verification separate')
 (OUT/f's{args.seed}_summary.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
if __name__=='__main__':main()
