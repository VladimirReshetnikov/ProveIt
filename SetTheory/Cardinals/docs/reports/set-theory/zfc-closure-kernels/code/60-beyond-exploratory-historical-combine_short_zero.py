import json,sys,time
from pathlib import Path
from functools import cache
sys.path.insert(0,str(Path(__file__).parent))
import inspect_negation_regions as a
from macro_signatures import make_signature
started=time.monotonic()
qs=(162,120,117,156,216,218)
lookup={make_signature(a.d.unfold(a.native,q)):q for q in qs}
source=json.load(open('agent_runtime/short-zero-layout.json'))
results=[]
for index,layout in enumerate(source['short_zero_layouts']):
 ns={int(k):tuple(tuple(y) for y in x) for k,x in layout['nodes'].items()}
 tree=a.d.unfold(ns,layout['root']);seen=set();matches={}
 def visit(e):
  if e[0]!='N' or e in seen:return
  seen.add(e)
  if a.d.closed(e):
   q=lookup.get(make_signature(e))
   if q is not None:matches[q]=e
  visit(e[1]);visit(e[2])
 visit(tree)
 if set(matches)!=set(qs):
  results.append(dict(layout=index,matched=list(matches),status='match_missing'));continue
 variants={
  'direct_transfer':('N',matches[216],('N',('I',1),matches[120])),
  'zerohead_add8':('N',matches[120],('N',matches[156],matches[156])),
  'output_prefill2':('N',('N',('I',7),('I',7)),matches[120]),
 }
 for kind,wn in variants.items():
  @cache
  def repl(e):
   if e==matches[218]:return wn
   if e[0]=='N':return('N',repl(e[1]),repl(e[2]))
   return e
  t=repl(tree);new,r=a.d.interned(t);paths=list(a.d.leaves(t));z=max(max(map(len,''.join(map(str,p)).split('1')))for p,e in paths)
  print(index,kind,len(new),len(paths),a.d.bounds(t),z,flush=True)
  result=dict(layout=index,kind=kind,nodes=len(new),leaves=len(paths),bounds=a.d.bounds(t),maxzero=z)
  results.append(result)
  out=Path('agent_architecture')/f'combined_{index}_{kind}_dag.json'
  out.write_text(json.dumps({'nodes':new,'root':r},indent=2)+'\n');result['path']=str(out)
Path('agent_architecture/combined_results.json').write_text(json.dumps({'results':results,'elapsed':time.monotonic()-started},indent=2)+'\n')
