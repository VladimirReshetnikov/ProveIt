from pathlib import Path
exec((Path(__file__).resolve().parent / 'exhaust_context.py').read_text().split('choices={}')[0])
import importlib.util
sp=importlib.util.spec_from_file_location('audit',BASE/'code/audit_routing_grammar.py');audit=importlib.util.module_from_spec(sp);sp.loader.exec_module(audit);audit.BASE=OUT.parent
stem='zero5-feasibility-best'
gram=json.loads((OUT/(stem+'.json')).read_text());g={q:(a,b) for q,a,b in gram['rules']};routes={(r['source'],r['read']):r['word'] for r in gram['routes']};force.cache_clear()
C='VqkjGqkjGVqkjG';B='qkjG';E='VqkjG';tail=C[1:];cs=next(cs for s,b,cs in groups if(s,b)==(183,1));assert routes[183,1]==C
alts=[(q,p) for q in g if q!=C for p in force(q,tuple(cs))]
left=[q for q,(a,b) in g.items() if b==B];right=[q for q,(a,b) in g.items() if b==E]
for a,b in itertools.product(left,right):
 q=a+b
 if q!=C:alts.append((q,((q,a,b),)))
print('alternative plans',len(alts),'existing',sum(q in g for q,p in alts))
tails=[()] if tail in g else [((tail,tail[:k],tail[k:]),) for k in range(1,len(tail)) if (len(tail[:k])==1 or tail[:k] in g) and (len(tail[k:])==1 or tail[k:] in g) and allowed_side(tail[:k],0) and allowed_side(tail[k:],1)]
best=1000;hits=[]
for q,p in alts:
 for tailplan in tails:
  d=g.copy();rs=routes.copy()
  for x,a,b in p+tailplan:d[x]=(a,b)
  d[C]=('V',tail);rs[183,1]=q
  if not all(match(d,rs[s,b],cs) for s,b,cs in groups):continue
  d=close(d,rs)
  if d is None:continue
  n=len(d)
  if n>best:continue
  out=dict(gram);out.update(rules_count=n,roots=roots,rules=[[q,*d[q]] for q in sorted(d)],routes=[dict(source=s,read=b,word=w) for(s,b),w in sorted(rs.items())],properties=[])
  dst=OUT/f'free183-k{n}.json';dst.write_text(json.dumps(out,indent=2)+'\n')
  try:r=audit.audit(dst,short_scan=True)
  except Exception as e:continue
  props=r['search_AST_properties'];out['properties']=[props['leading_zeros'],props['maximum_zero_run'],props['depth']];dst.write_text(json.dumps(out,indent=2)+'\n')
  if props['maximum_zero_run']<=5:
   best=n;(OUT/f'free183-k{n}-local-audit.json').write_text(json.dumps(r,indent=2)+'\n');hits.append(dict(rules=n,properties=props,new_router=q,file=dst.name));print(hits[-1],flush=True)
(OUT/'free183-summary.json').write_text(json.dumps(dict(status='ABSTRACT_ONLY',best_zero5_rules=None if best==1000 else best,plans=len(alts)*len(tails),hits=hits),indent=2)+'\n')
