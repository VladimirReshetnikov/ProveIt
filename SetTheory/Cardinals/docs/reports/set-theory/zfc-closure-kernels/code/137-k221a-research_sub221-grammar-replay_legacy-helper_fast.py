#!/usr/bin/env python3
"""Literal-stream reassociation search, scored by physical decoder allocation.
Every accepted output still requires full independent source and runtime proofs.
"""
from pathlib import Path
import sys,json,random,math,time,argparse
sys.path.insert(0,str(Path(__file__).resolve().parent))
from state_context_parser import cc,REQUIRED,decode
from search_rotations import Trees

BASE=Path('research_sub222/delivery/K221_Construction_2026-10-20/machine/sites221.json')
class Grammar(Trees):
 def __init__(self):
  super().__init__();self.good=[];self.possible=[]
 def intern(self,n):
  if n in self.ids:return self.ids[n]
  i=super().intern(n)
  if self.leaf(i):g=15
  else:
   a,b=n;g=req.get(i,15)
   for ctx in range(4):
    if not (self.good[a]>>(2*(ctx%2))&1 and self.good[b]>>(2*(ctx%2)+1)&1):g&=~(1<<ctx)
  self.good.append(g)
  if self.leaf(i):opts=set()
  elif i in cc.NQ:opts={cc.NQ[i]}
  else:
   allowed=[]
   for b in (0,1):
    ch=n[b];ss=[('leaf',*self.nodes[ch])] if self.leaf(ch) else [('state',q)for q in self.possible[ch]]
    allowed.append(FREE[b].union(*(TEMPLATE[b].get(z,set())for z in ss)))
   opts=allowed[0]&allowed[1]
  self.possible.append(opts);return i
 def living(self,n):
  live=set();todo=[n]
  while todo:
   n=todo.pop()
   if n in live:continue
   live.add(n)
   if not self.leaf(n):todo.extend(self.nodes[n])
  return live
 def cost(self,live):
  oldqs={cc.NQ[n]for n in live if n in cc.NQ};new=[n for n in live if not self.leaf(n) and n not in cc.NQ];missing=cc.HELPQS-oldqs
  match={}
  def visit(n,seen):
   for q in self.possible[n]&missing:
    if q in seen:continue
    seen.add(q)
    if q not in match or visit(match[q],seen):match[q]=n;return True
   return False
  for n in new:visit(n,set())
  return 49+len(oldqs|cc.HELPQS)+len(new)-len(match)
# Match integer numbering by loading the identical baseline before any alternative.
req={n:REQUIRED[decode(n)]for n in cc.NQ}

FIXED={q for q,b in cc.T}-cc.SOURCEQS
TEMPLATE=[{},{}];FREE=[set(),set()]
for q in cc.HELPQS:
 for b in (0,1):
  if (q,b) not in cc.F:FREE[b].add(q);continue
  for on in cc.M[q]:
   ch=cc.tr.nodes[on][b];sig=('leaf',*cc.tr.nodes[ch]) if cc.tr.leaf(ch) else ('state',cc.NQ[ch])
   TEMPLATE[b].setdefault(sig,set()).add(q)

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',default='research_sub221/grammar/helper_fast');p.add_argument('--seed',type=int,default=22142);p.add_argument('--steps',type=int,default=5000);p.add_argument('--restarts',type=int,default=80);p.add_argument('--start');p.add_argument('--stop-file',default='research_sub221/grammar/STOP_HELPER');p.add_argument('--soft-tags',action='store_true');a=p.parse_args()
 out=Path(a.output);out.mkdir(parents=True,exist_ok=True);base=json.loads(BASE.read_text());initial=json.loads(Path(a.start).read_text())if a.start else base;rng=random.Random(a.seed);start=time.time();best=221;hits=0;validcomp=0;results=[]
 for restart in range(a.restarts):
  tr=Grammar();r0=tr.read(base);assert tr.nodes==cc.tr.nodes[:len(tr.nodes)];root=tr.read(initial);live=tr.living(root);score=tr.cost(live)+3*max(tr.zrun[root]-6,0)+5*(4-tr.good[root].bit_count());hist=[]
  # Most restarts stay close to the paid-state plateau; a few permit crossing a +1 barrier.
  temp=(.06,.12,.18,.25,.32,.4)[restart%6];localbest=score;accepted=0
  for step in range(a.steps):
   if step%100==0 and Path(a.stop_file).exists():print("STOP REQUEST",flush=True);return
   n=rng.choice(tuple(live));
   if tr.leaf(n):continue
   l,r=tr.nodes[n];d=rng.randrange(2)
   if tr.leaf(l if d==0 else r):continue
   if d==0:x,y=tr.nodes[l];z=r
   else:x=l;y,z=tr.nodes[r]
   if tr.bd[x][0] or tr.bd[z][1]:continue
   nn=tr.intern((x,tr.intern((y,z))))if d==0 else tr.intern((tr.intern((x,y)),z))
   nr=tr.substitute(root,n,nn)
   if tr.zrun[nr]>7 or (not a.soft_tags and tr.good[nr]!=15):continue
   nl=tr.living(nr);cost=tr.cost(nl);sc=cost+3*max(tr.zrun[nr]-6,0)+5*(4-tr.good[nr].bit_count())
   if sc>score and rng.random()>math.exp((score-sc)/temp):continue
   root=nr;live=nl;score=sc;accepted+=1;hist.append((n,nn,d));localbest=min(localbest,score)
   if cost<best and tr.zrun[root]<=6 and tr.good[root]==15:
    hits+=1;dout=out/f'cost{cost}_{hits:04}';dout.mkdir();(dout/'sites.json').write_text(json.dumps(tr.sites(root),separators=(',',':'))+'\n');(dout/'search.json').write_text(json.dumps(dict(cost=cost,metrics=tr.metrics(root),restart=restart,step=step,history=hist),indent=2)+'\n')
    print('COST HIT',cost,dout,round(time.time()-start,2),flush=True)
    result=cc.compile(dout/'sites.json',dout/'compiled');results.append(dict(path=str(dout),**{k:result.get(k)for k in('states','decoder_ok','error','decoder_failures')}));(out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print('COMPILED',results[-1],flush=True)
    best=cost
    if result.get('states',999)<=220 and result.get('decoder_ok'):
     print('SUCCESS NEEDS INDEPENDENT PROOFS',dout,flush=True);return
  print('RESTART',restart,'localbest',localbest,'end',score,'best',best,'accepted',accepted,'nodes',len(tr.nodes),'seconds',round(time.time()-start,2),flush=True)
 print('DONE',best,flush=True)
if __name__=='__main__':main()
