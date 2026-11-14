#!/usr/bin/env python3
from pathlib import Path
import sys,json,time,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();m=S.load_machine(out/'h_catalan_node170_3_133_37.tm');tree,nodes=S.source_tree();nodes['node168']=(nodes['node167'],nodes['node145']);nodes['node169']=(nodes['node36'],nodes['node168']);nodes['node170']=(nodes['node169'],nodes['node57']);nodes['node171']=(nodes['node170'],nodes['node23']);nodes['node172']=(nodes['node21'],nodes['node171']);nodes['trie']=nodes['node172'];tree=nodes['trie'];oldsites=S.flatten(tree)
mp=json.loads((out.parents[1]/'verification/node_map.json').read_text())
def cfg(sites):
 pref={}
 for i,(p,op)in enumerate(sites):
  for k in range(len(p)+1):pref.setdefault(p[:k],i)
 def loc(p):
  if p is None:return 0
  while p not in pref:
   if not p or p[-1]:raise ValueError(('missingprefix',p))
   p=p[:-1]
  return pref[p]
 result=[]
 for p,op in sites:
  tag=op[0]
  if tag=='inc':result.append(('inc',op[1],loc(S.successor(p))))
  elif tag=='dec':result.append(('dec',op[1],loc(S.successor(S.cut(p,0,1))),loc(S.successor(p))))
  elif tag=='continueTo':result.append(('jump',loc(S.cut(p,1,op[1]))))
  elif tag=='breakTo':result.append(('jump',loc(S.successor(S.cut(p,0,op[1])))))
  else:result.append(('halt',))
 return result
oldcfg=cfg(oldsites)
if oldcfg!=S.instructions(oldsites):raise RuntimeError('fastresolver differs')
S.instructions=cfg
leaf=lambda t:t[0]=='leaf'
def replace(t,a,b):
 if t==a:return b
 if leaf(t):return t
 return replace(t[0],a,b),replace(t[1],a,b)
incoming=collections.defaultdict(list)
for k,v in m.items():incoming[v[2]].append(k)
trees=collections.defaultdict(set)
for name,qs in mp.items():
 for q in qs:trees[q].add(nodes[name])
protected={q for q,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS}|{S.ROOT};states=sorted({q for q,b in m});records=[];hits=[];unique=set()
for name,qs in mp.items():
 if not name.startswith('node'):continue
 t=nodes[name]
 for q in qs:
  if trees[q]!={t}or not all(m[q,b][:2]==(b,1)for b in(0,1)):continue
  for direction in(0,1):
   if leaf(t[direction]):continue
   u=m[q,direction][2]
   if incoming[u]!=[(q,direction)]or not all(m[u,b][:2]==(b,1)for b in(0,1)):continue
   if direction==0:
    a,b=t[0];c=t[1];nt=(a,(b,c));p0=m[u,0][2];p1=m[u,1][2];p2=m[q,1][2]
    patch={(q,0):(0,1,p0),(q,1):(1,1,u),(u,0):(0,1,p1),(u,1):(1,1,p2)}
   else:
    a=t[0];b,c=t[1];nt=((a,b),c);p0=m[q,0][2];p1=m[u,0][2];p2=m[u,1][2]
    patch={(q,0):(0,1,u),(q,1):(1,1,p2),(u,0):(0,1,p0),(u,1):(1,1,p1)}
   key=tuple(sorted(patch.items()))
   if key in unique:continue
   unique.add(key);item={'name':name,'direction':direction,'q':q,'u':u};ns=S.flatten(replace(tree,t,nt))
   try:goodcfg=cfg(ns)==oldcfg
   except ValueError:goodcfg=False
   if not goodcfg:item['skip']='CFG';records.append(item);continue
   nm=m|patch;S.all_sites=lambda:ns;cs=S.contracts();first=collections.defaultdict(list);bad=None
   for i,branch,br,s,dest in cs:
    trace=[]
    if S.execute(nm,br,s,dest,record=trace)is None:bad=(i,branch);break
    seen=set()
    for tag,v,row in trace:
     q0=v[0]
     if tag=='step'and q0 not in seen:first[q0].append((br,v,dest));seen.add(q0)
   if bad is not None:item['failure']=bad;records.append(item);print('FAIL',item,flush=True);continue
   tested=0
   for drop in states:
    if drop in protected:continue
    for keep in states:
     if keep==drop or not ({drop,keep}&{q,u}):continue
     fm={k:(w,d,keep if z==drop else z)for k,(w,d,z)in nm.items()if k[0]!=drop};tested+=1
     if any(S.execute(fm,br,(keep,)+v[1:],dest)is None for br,v,dest in first[drop]):continue
     try:summary,_=S.verify(fm)
     except AssertionError:continue
     hit=item|{'drop':drop,'keep':keep,'summary':summary};hits.append(hit);stem=f'h_rotfold_{name}_{direction}_{drop}_{keep}';hit['stem']=stem
     (out/(stem+'.tm')).write_text(''.join(f'{qq} {b} {w} {"R"if d==1 else"L"} {z}\n'for(qq,b),(w,d,z)in sorted(fm.items())))
     (out/(stem+'_sites.json')).write_text(json.dumps(ns)+'\n');print('HIT',hit,flush=True)
   item['tested_folds']=tested;item['success']=True;records.append(item);print('PASS',item,'elapsed',round(time.monotonic()-start,1),flush=True)
(out/'h_neutral_rotation_results.json').write_text(json.dumps({'records':records,'hits':hits,'seconds':time.monotonic()-start},indent=2)+'\n');print('DONE',len(records),'hits',hits,flush=True)
