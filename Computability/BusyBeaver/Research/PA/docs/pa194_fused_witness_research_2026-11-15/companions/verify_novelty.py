#!/usr/bin/env python3
"""Exact whole-graph comparison under deliberately broad structural symmetries.

A graph with one source strongly connected component has spanning roots
exactly in that component. This avoids trying every control needlessly.
Read-bit labels and actions are compared exactly, except that the broad
key allows tape reflection, global bit exchange, and ignores halt-entry
write/move decorations. Bit exchange is a structural comparison only:
it is not asserted to preserve a zero-blank computation.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('invalid table')
  rows[q,b]=(w,d,n)
 states={q for q,b in rows}
 if len(rows)!=2*len(states) or any((q,b) not in rows for q in states for b in (0,1)):raise ValueError('incomplete table')
 if len({n for w,d,n in rows.values()}-states)!=1:raise ValueError('expected unique terminal control')
 return rows,states

def spanning_roots(rows,states):
 adj={q:{rows[q,b][2] for b in (0,1)}&states for q in states}
 rev={q:set()for q in states}
 for q,outs in adj.items():
  for n in outs:rev[n].add(q)
 seen=set();order=[]
 def visit(q):
  if q in seen:return
  seen.add(q)
  for n in adj[q]:visit(n)
  order.append(q)
 for q in sorted(states):visit(q)
 comps=[];component={}
 for q in reversed(order):
  if q in component:continue
  index=len(comps);stack=[q];component[q]=index;members=[]
  while stack:
   n=stack.pop();members.append(n)
   for v in rev[n]:
    if v not in component:component[v]=index;stack.append(v)
  comps.append(members)
 incoming=set()
 for q,outs in adj.items():
  for n in outs:
   if component[q]!=component[n]:incoming.add(component[n])
 sources=[i for i in range(len(comps)) if i not in incoming]
 return sorted(comps[sources[0]])if len(sources)==1 else []

def rooted(rows,states,start,mirror=False,flip=False,loose=False):
 index={start:0};order=[start];out=[]
 for q in order:
  for b in(0,1):
   w,d,n=rows[q,b^int(flip)];w^=int(flip)
   if mirror:d='L'if d=='R'else'R'
   if n in states:
    if n not in index:index[n]=len(order);order.append(n)
    out.append((w,d,index[n]))
   else:out.append((0,'R',-1)if loose else(w,d,-1))
 return tuple(out)

def least_bfs(rows,states,roots,options,loose=False):
 # Lexicographic branch pruning: after a prefix first exceeds the best
 # complete tuple, no unseen suffix can make this root a minimum.
 best=None
 for mirror,flip in options:
  for start in roots:
   index={start:0};order=[start];out=[];cmp=0;reject=False
   for q in order:
    for b in(0,1):
     w,d,n=rows[q,b^int(flip)];w^=int(flip)
     if mirror:d='L'if d=='R'else'R'
     if n in states:
      if n not in index:index[n]=len(order);order.append(n)
      triple=(w,d,index[n])
     else:triple=(0,'R',-1)if loose else(w,d,-1)
     if best is not None and cmp==0:
      prior=best[len(out)]
      if triple>prior:reject=True;break
      if triple<prior:cmp=-1
     out.append(triple)
    if reject:break
   if not reject:
    value=tuple(out)
    if best is None or value<best:best=value
 return best

def canonical(rows,states,mirror=False,flip=False,loose=False):
 return least_bfs(rows,states,spanning_roots(rows,states),[(mirror,flip)],loose)
def key(rows,states,broad=False):
 roots=spanning_roots(rows,states)
 if not roots:return None
 options=[(m,f)for m in(False,True)for f in(False,True)]if broad else[(False,False)]
 value=least_bfs(rows,states,roots,options,broad)
 return sha(json.dumps(value,separators=(',',':')).encode())

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'verification/novelty.json');a=ap.parse_args()
 manifest=json.loads((ROOT/'comparison/corpus_manifest.json').read_text())
 broad={};read=[]
 for item in manifest['tables']:
  p=ROOT/item['path'];data=p.read_bytes()
  if sha(data)!=item['sha256']:raise ValueError('corpus bytes changed: '+str(p))
  rows,states=parse(p);ex=key(rows,states);strong=key(rows,states,True)
  if ex!=item['exact_class']or strong!=item['strong_class']:raise ValueError('canonical identity changed: '+str(p))
  broad.setdefault(strong,[]).append(item['path']);read.append(ex)
 specs=json.loads((ROOT/'inputs/specifications.json').read_text())
 candidates=[dict(name=sp['parent'],path=ROOT/'inputs'/sp['parent']/'machine.tm',spec=None)for sp in specs if sp.get('parent_origin')=='new_this_work']
 candidates += [dict(name=sp['name'],path=ROOT/'machines'/sp['name']/'machine.tm',spec=sp)for sp in specs]
 results=[]
 for candidate in candidates:
  name=candidate['name'];p=candidate['path'];spec=candidate['spec'];rows,states=parse(p);ex=key(rows,states);strong=key(rows,states,True)
  if strong in broad:raise ValueError('candidate repeats corpus graph: '+name)
  # Positive control exercises arbitrary sparse labels, reflection, bit swap,
  # and arbitrary write/move decorations on terminal edges simultaneously.
  rename={q:10000+7*q for q in states};halts={n for w,d,n in rows.values()}-states
  for q in halts:rename[q]=99999
  control={(rename[q],b^1):(w^1,'L'if d=='R'else'R',rename[n])for(q,b),(w,d,n)in rows.items()}
  control={k:((1,'L',n)if n==99999 else(w,d,n))for k,(w,d,n)in control.items()}
  if key(control,{rename[q]for q in states},True)!=strong:raise ValueError('broad-symmetry positive control failed')
  pk=None;parent_present=None
  if spec is not None:
   parent=ROOT/'inputs'/spec['parent']/'machine.tm';pr,ps=parse(parent);pk=key(pr,ps)
   parent_present=pk in read
   if spec.get('parent_origin')!='new_this_work' and not parent_present:raise ValueError('known parent missing from corpus')
   if sha(parent.read_bytes())!=spec['parent_dense_sha256']:raise ValueError('parent bytes changed')
  results.append({'name':name,'dense_sha256':sha(p.read_bytes()),'working_states':len(states),'rows':len(rows),'start':0,'halt':194,'spanning_roots':spanning_roots(rows,states),'exact_class':ex,'strong_class':strong,'matches':[],'symmetry_positive_control':True,'known_parent_class':pk,'known_parent_present':parent_present,'self_loops':sum(q==n for(q,b),(w,d,n)in rows.items())})
 if len({x['strong_class']for x in results})!=len(results):raise ValueError('children structurally repeat one another')
 report={'status':'PASS','pin':manifest['pin'],'corpus_graphs':len(read),'scope':manifest['scope'],'method':'source-SCC spanning roots; exact ordered BFS tuples with lexicographic prefix pruning; four reflection/bit-exchange choices; erase halt-entry actions','results':results}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
