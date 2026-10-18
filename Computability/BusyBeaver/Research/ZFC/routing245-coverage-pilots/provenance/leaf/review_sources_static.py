from pathlib import Path
import json,hashlib,re,collections
B=Path('/tmp/zfc-routing245-lean/coverage-pilots');P=B/'pilot-plan.json';d=json.loads(P.read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();paths={}
def check(q):
 assert sha(q['path'])==q['sha256'];paths[q['path']]=q['sha256']
for q in d['inputs']+[d['emitter'],d['boundary']]:check(q)
prog=Path(d['inputs'][1]['path']).read_text();rows={}
for line in prog.splitlines():
 if line.startswith('private def row'):
  k=int(line.split()[2][3:]);body=line.split(' := ',1)[1][1:-1];es=[]
  for e in body.split(', '):
   e=e.strip('()').split();es.append((e[0][1:],int(e[1]) if len(e)>1 else None))
  rows[k]=es
assert len(rows)==203
leaves=[];pending=[(202,'')]
while pending:
 n,p=pending.pop()
 for bit,e in [('1',rows[n][1]),('0',rows[n][0])]:
  if e[0]=='node':
   assert e[1]<n;pending.append((e[1],p+bit))
  else:leaves.append((p+bit,e))
leaves.sort(key=lambda x:x[0]);assert len(leaves)==6460
sites=json.loads(Path(d['inputs'][0]['path']).read_text());op={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
assert leaves==[(p,(op[k],a))for p,k,a in sites]
assert sum(2 if k=='CD' else 1 for p,k,a in sites)==8391
normalized=[]
for u in d['pilots']:
 for q in [u['source'],u['audit']]:check(q)
 i=u['site_index'];path,edge=leaves[i];assert path==u['path'] and list(edge)==u['edge'] and len(path)==u['depth']
 s=Path(u['source']['path']).read_text();a=Path(u['audit']['path']).read_text()
 bits=re.search(r'def path : List Bool := \[(.*?)\]',s).group(1).split(', ');assert ''.join('1' if x=='true' else '0' if x=='false' else '?' for x in bits)==path
 inst=re.search(r'def instruction : Edge := (.+)',s).group(1).split();assert(inst[0][1:],int(inst[1]) if len(inst)>1 else None)==edge
 assert s.count('decide +kernel')==2 and len(re.findall(r'^theorem ',s,re.M))==2
 assert f'twalk TreeRouting245.tree path 0 = some (instruction, {len(path)})' in s and 'SiteRouting245.checkSite path instruction = true' in s
 assert len(re.findall(r'^#print axioms ',a,re.M))==2 and len(re.findall(r'^example\b',a,re.M))==u['callers']
 assert 'TreeRouting245.walk_eq_tree path 0' in a and 'ProgramRouting245.program.nnodes + 1' in a
 if edge[0]=='decnz':
  assert 'site_checked).1' in a and 'site_checked).2' in a and a.count('SiteRouting245.runTo ')==2
 assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s+a)
 n=re.sub(r'/\-.*?\-/','',s,flags=re.S);n=re.sub(r'SitesRouting245Pilot\d+','PILOT',n);n=re.sub(r'def path : List Bool := \[.*?\]','def path : List Bool := BITS',n);n=re.sub(r'def instruction : Edge := .*','def instruction : Edge := EDGE',n);n=n.replace(f'some (instruction, {len(path)})','some (instruction, DEPTH)');normalized.append(' '.join(n.split()))
assert len(set(normalized))==1
assert [u['site_index']for u in d['pilots']]==[1704,1705,1609,1703,1720,4730,6324]
assert sum(u['guards']for u in d['pilots'])==9 and sum(u['callers']for u in d['pilots'])==25
for q in json.loads((B/'history/metadata-selection-v2/failure.json').read_text())['emitted_files']:
 assert sha(B/'history/metadata-selection-v2'/q['path'])==q['sha256']==sha(B/q['path'])
o=dict(status='SOURCE_PATTERN_AND_LEAF_LINKAGE_REVIEW_CLEAN',plan=dict(path=str(P),sha256=sha(P)),emitter=d['emitter'],source_files=14,current_input_bindings=paths,leaf_count=6460,pilot_indices=[u['site_index']for u in d['pilots']],probes=14,callers=25,guard_cases=9,findings=[],scope='Complete emitter and representative source/audit forms read; every emitted source/audit parsed and normalized, all203 maintained DAG rows independently expanded to6460 ordered leaves and matched metadata, all seven literal links checked. No supplied emitter/checker/symbolic machine simulation/compiler or guard executed. Two prior own-emitter metadata failures are preserved; neither is proof failure. No whole-tree acceptance is claimed. Proof guard is not included because not yet provided.')
out=B/'independent-source-pattern-review.json';assert not out.exists();out.write_text(json.dumps(o,indent=2)+'\n');print(str(out),sha(out))
