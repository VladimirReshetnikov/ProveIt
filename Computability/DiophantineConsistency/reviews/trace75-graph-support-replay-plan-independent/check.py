from pathlib import Path
import hashlib,json,re,collections,os
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-graph-support-replay-plan';o=h/'observations/attempt01';R=D/'research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')==sha(o/'source.txt')=='6e0ca8bc7e27bed88ef29a890819ae506ba935abf372e406a7ba4ea68b349301';assert sha(o/'terminal.json')=='e2dc258cc13d7b31da2a9a9a4388d75ab5ab0ed6ca14b9a178ea08825511b518' and sha(o/'stdout')=='a6293d79952afa80ce14d558eb2e363795c1ffff9dc3d0898c23ff3f1ccf04da';t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr')
ps=[R/'trace75-graph-support-28-triage/observations/attempt01/stdout',R/'trace75-graph-support-seven-observations/observations/attempt01/stdout',R/'trace75-packing-blocks-observation/observations/attempt01/stdout',R/'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'];ds=['a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570','8f6360726fe0f1917da33d3914c91d09e30b9c71402a20d6758ad1aa5d9f03f9','c2a15eac221a02abca6144f122089d88c607112dc3391a2c9885a9135111d654','b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'];assert all(sha(p)==d for p,d in zip(ps,ds));tri,seven,pack,final=map(load,ps);result=load(o/'stdout');rows={x['module']:x for x in tri['records']};nodes=set(rows);assert len(nodes)==28;heads=final['serialized_headers'];proj=set(final['selected_project']);ext=set(final['selected_outside']);order=result['order'];assert set(order)==nodes and len(order)==28;pos={n:i for i,n in enumerate(order)};up=set();outside=set();edges=0
for n in nodes:
 for d in set(heads[n]):
  if d in nodes:edges+=1;assert pos[d]<pos[n]
  elif d in proj:up.add(d)
  else:assert d in ext;outside.add(d)
assert edges==9 and len(up)==31 and outside=={'Init'} and result['internal_edges']==9
sources={x['module']:x for x in result['sources']};assert set(sources)==nodes;count=0;obsnames={x['module'] for x in seven['records']}|{'DiophantineConsistency.ArithmeticPackingBlocks'};assert len(obsnames)==8
for n in nodes:
 x=rows[n];r=sources[n];p=Path(r['source']);assert sha(p)==r['source_sha256'];assert r['captured_header']==heads[n] and r['has_reported_source_session']==(n in obsnames) and r['overlay_log_candidates']==x['overlay_logs']
 if x['overlay_source']:
  assert len(x['workspace_matches'])==1 and str(p)==x['workspace_matches'][0] and sha(p)==x['overlay_source']['sha256']==sha(x['overlay_source']['path']) and r['source_category']=='current source equals overlay-root source'
 else:assert n=='DiophantineConsistency.ArithmeticPackingBlocks' and sha(p)==pack['reported_source_sha256'] and r['source_category']=='retained reported source; no overlay-root source'
 text=p.read_text();im=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',text,re.M);assert im==[v for v in heads[n] if v!='Init'];reports=re.findall(r'^\s*#print\s+axioms\s+([^\s]+)',text,re.M);assert reports==r['print_axioms_source_tokens'];count+=len(reports)
assert count==60
for names,key,kind in [(up,'direct_project_inputs','selected_project'),(outside,'direct_outside_inputs','selected_outside')]:
 rr={x['module']:x for x in result[key]};assert set(rr)==names
 for n in names:
  b=final[kind][n];p=Path(b['.olean']['path']);assert rr[n]['olean_realpath']==b['.olean']['resolved'] and rr[n]['olean_sha256']==b['.olean']['sha256']
  for suff,v in b.items():
   q=Path(str(p)[:-6]+suff)
   if v is None:assert not os.path.lexists(q)
   else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
fixed=set(final['closures']['Trace75BFSFixedIPRA']['project']);users=collections.defaultdict(set)
for n in fixed:
 for d in heads[n]:
  if d in fixed:users[d].add(n)
reach=set(nodes);todo=list(nodes)
while todo:
 for n in users[todo.pop()]-reach:reach.add(n);todo.append(n)
assert len(reach)==331 and sorted(reach)==result['reverse_reachable'] and 'Trace75BFSFixedIPRA' in reach
print('PASS 28 candidate sources/headers, 9 topological edges, 31 project + Init direct bundles, 60 directive tokens, 8 observations and 331 captured reverse reachable')
