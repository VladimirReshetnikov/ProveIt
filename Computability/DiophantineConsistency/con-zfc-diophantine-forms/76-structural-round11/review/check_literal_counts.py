"""Independent static parser; never imports or executes upstream programs."""
import json,pathlib,collections
ROOT=pathlib.Path(__file__).parent
out=[]
for p in sorted((ROOT/'packages').rglob('*.json')):
 a=json.loads(p.read_text()); r={'path':str(p.relative_to(ROOT))}
 if 'source' in a and isinstance(a['source'],list):
  known=set(a.get('witnesses',[])+a.get('fixed_numerals',[])+a.get('fixed_ports',[])+list(a.get('derived_fixed_leaves',{})))
  source=a['source']; nodes={};counts=collections.Counter()
  for n,op,u,v in source:
   if n in known or n in nodes: raise ValueError((p,'reused output',n))
   for x in (u,v):
    if not isinstance(x,int) and x not in known and x not in nodes:raise ValueError((p,'unknown input',x))
   if op not in ['+','-','*']:raise ValueError((p,'operator',op))
   nodes[n]=(u,v);counts[op]+=1
  live=set();stack=[a['output']]
  while stack:
   n=stack.pop()
   if n in live or n not in nodes:continue
   live.add(n);stack.extend(nodes[n])
  if len(live)!=len(nodes):raise ValueError((p,'dead gates',set(nodes)-live))
  if len(nodes)!=a['operations']:raise ValueError((p,'count mismatch'))
  r.update(variables=len(a['witnesses']),operations=len(nodes),all_live=True,reported_degree=a['exact_degree'])
 elif 'nodes' in a:
  nodes=a['nodes'];ops=collections.Counter()
  for i,n in enumerate(nodes):
   k=n['kind']
   if k in ['add','sub','mul']:
    if not 0<=n['left']<i or not 0<=n['right']<i:raise ValueError((p,'bad topology',i))
    ops[k]+=1
   elif k not in ['literal','variable','fixed']:raise ValueError((p,'operator',k))
  live=set();stack=[a['output']]
  while stack:
   i=stack.pop()
   if i in live:continue
   live.add(i);n=nodes[i]
   if n['kind'] in ['add','sub','mul']:stack.extend([n['left'],n['right']])
  if len(live)!=len(nodes):raise ValueError((p,'dead nodes'))
  if sum(ops.values())!=a['total_operations']:raise ValueError((p,'count mismatch'))
  r.update(variables=len(a['variables']),operations=sum(ops.values()),all_live=True,reported_degree=a['exact_degree'])
 else:
  if 'residuals' not in a:continue
  r.update(variables=len(a['variables']),residual_count=len(a['residuals']),reported_degree=a['exact_degree'])
  if a.get('variable_count',r['variables'])!=r['variables']:raise ValueError((p,'variable count'))
  if a.get('equation_count',a.get('residual_count',r['residual_count']))!=r['residual_count']:raise ValueError((p,'residual count'))
 out.append(r)
(ROOT/'LITERAL_COUNTS.json').write_text(json.dumps({'scope':'Static live-gate/topology/arity counts only; degrees recorded, not re-proved by this checker. No mathematical equivalence claim.','files':out},indent=2)+'\n')
print('PASS',len(out),'literal files')
