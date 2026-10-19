#!/usr/bin/env python3
"""Jointly reparse a whole router and both children, then remove dead nodes.

Candidates come from the finite current word dictionary. Each word retains
its exact primitive order; only binary associations and routing carriers move.
"""
from pathlib import Path
from functools import cache
import argparse,json,time

def solve(seed,inputs,output,max_extra=1):
 data=json.loads(seed.read_text());g0={w:(l,r) for w,l,r in data['rules']};roots=data['roots'];routes0={(r['source'],r['read']):r['word'] for r in data['routes']}
 ls=(inputs/'grammar.txt').read_text().splitlines();ng,nr,nt=map(int,ls[0].split());old={w:(w[:int(k)],w[int(k):]) for k,w,_ in map(str.split,ls[1:ng+1])};allowed={w:int(m) for w,m in map(str.split,ls[ng+nr+1:])};terms=set(allowed)
 constraints=(inputs/'constraints.txt').read_text().splitlines();i=1;groups={}
 for _ in range(int(constraints[0])):
  q,b,w,n=constraints[i].split();i+=1;cs=[]
  for _ in range(int(n)):
   prefix,target=constraints[i].split();i+=1;cs.append((prefix,target))
  groups[int(q),int(b)]=cs
 ne,original_expr,na=map(int,constraints[i].split());i+=1;exprs=[]
 for _ in range(ne):
  row=constraints[i].split();i+=1;exprs.append(row if row[0]!='N' else ['N',int(row[1]),int(row[2])])
 atoms={}
 for _ in range(na):w,e=constraints[i].split();i+=1;atoms[w]=int(e)
 locks=(inputs/'locks.txt').read_text().splitlines();locks=[tuple(r.split()) for r in locks[1:]];roots=list(dict.fromkeys(roots+[w for w,b,t in locks]));allwords=set(g0)|terms
 def permitted(l,r):return all(c not in terms or allowed[c]&(1<<side) for side,c in enumerate((l,r)))
 def project(g,w,p):
  for bit in p:
   if w not in g:return None
   w=g[w][int(bit)]
  return w
 def props(g):
  seen=set()
  def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
  @cache
  def ep(i):
   r=exprs[i];return wp(r[1]) if r[0]=='W' else (0,0,0) if r[0]=='L' else join(ep(r[1]),ep(r[2]))
  @cache
  def wp(w):
   assert w not in seen;seen.add(w)
   ans=ep(atoms[w]) if w in terms else join(*(wp(c) for c in (g[w] if w in g else old[w])))
   seen.remove(w);return ans
  return ep(original_expr)
 bestn=len(g0);best=data;trials=0;accepted=0;started=time.monotonic()
 for key,cs in groups.items():
  for w in sorted(g0,key=lambda w:(len(w),w)):
   for cut in range(1,len(w)):
    children=(w[:cut],w[cut:])
    if not permitted(*children):continue
    changes={w:children};valid=True
    for side,child in enumerate(children):
     sub=[(p[1:],t) for p,t in cs if int(p[0])==side]
     if any(not p and t!=child for p,t in sub):valid=False;break
     forced=[(p,t) for p,t in sub if p]
     if not forced:
      if child not in allwords:valid=False;break
      continue
     if child in terms:valid=False;break
     ab=None
     for p,t in forced:
      assert len(p)==1
      if p=='0' and child.startswith(t):pair=(t,child[len(t):])
      elif p=='1' and child.endswith(t):pair=(child[:-len(t)],t)
      else:valid=False;break
      if ab is not None and ab!=pair:valid=False;break
      ab=pair
     if not valid:break
     if not ab[0] or not ab[1] or not all(c in allwords for c in ab) or not permitted(*ab):valid=False;break
     if child in changes and changes[child]!=ab:valid=False;break
     changes[child]=ab
    if not valid or len(set(changes)-set(g0))>max_extra:continue
    trials+=1;g=dict(g0);g.update(changes);routes=dict(routes0);routes[key]=w
    if any(project(g,w,b)!=t for w,b,t in locks):continue
    for kk,cases in groups.items():
     if all(project(g,routes[kk],p)==t for p,t in cases):continue
     opts=[q for q in g if all(project(g,q,p)==t for p,t in cases)]
     if not opts:valid=False;break
     routes[kk]=min(opts,key=lambda w:(len(w),w))
    if not valid:continue
    live=set()
    def visit(q):
     if q in terms or q in live:return
     live.add(q)
     for child in g[q]:visit(child)
    for q in roots+list(routes.values()):visit(q)
    reduced={q:g[q] for q in live}
    if len(reduced)>=bestn:continue
    prop=props(reduced)
    if prop[1]>6 or prop[2]>64:continue
    accepted+=1;bestn=len(reduced);best=dict(data,rules_count=bestn,rules=[[q,*reduced[q]] for q in sorted(reduced)],roots=roots,routes=[dict(source=q,read=b,word=v) for(q,b),v in routes.items()],properties=list(prop),joint_router_search=dict(key=key,word=w,cut=cut,changes=changes,seed=str(seed)))
    output.write_text(json.dumps(best,indent=2)+'\n');print('BEST',bestn,key,w,flush=True)
 report=dict(status='BOUNDED_FINITE_DICTIONARY_ROUTER_SEARCH',seed_rules=len(g0),best_rules=bestn,proposal_assignments=trials,improvements=accepted,seconds=time.monotonic()-started,max_new_child_words=max_extra,scope=f'Current dictionary and up to {max_extra} introduced constrained children per selected carrier; not an unrestricted lower bound.')
 if not output.exists():output.write_text(json.dumps(best,indent=2)+'\n')
 output.with_suffix('.summary.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));return report
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seed',type=Path,required=True);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--max-extra',type=int,default=1);a=p.parse_args();solve(a.seed,a.inputs,a.output,a.max_extra)
