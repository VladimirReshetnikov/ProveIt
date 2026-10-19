from pathlib import Path
import re,json,hashlib,ast
B=Path('/tmp/zfc243-source-bridge');R=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
checks=0
def ck(x,m):
 global checks
 checks+=1
 assert x,m
source=(B/'SourceRotation244.lean').read_text();audit=(B/'Audit.lean').read_text();guard=(B/'check.py').read_text();boundary=json.loads((B/'boundary.json').read_text())
ck(sha(B/'SourceRotation244.lean')=='1841efd5e21b70b4384c61cff06f5efe525388f7d0838c0767cc85d28abaafe7','source')
ck(sha(B/'Audit.lean')=='7e95a46fe93957440d3ac2ccb5cc8496967dfaa006ba43fcb1b42fe24853d989','audit')
ck(sha(B/'check.py')=='bb063edcaf0d4a32d368b2ef6ebc8614e5de156ed4e405927af8742e54c322df','guard')
ck(sha(B/'boundary.json')=='db8f50b066b17fa22c4ed2b1aa5a8b409e4dfdc2c2136c2aa3ed467a80a15c23','boundary')
# Independent strict parser of the literal decision trees, not execution of Lean or emitter.
def parse_tree(text,kind):
 pattern=r'if n < \d+ then|else|\(\d+,\d+,\d+\)' if kind=='bounds' else r'if n < \d+ then|else|row\d+'
 toks=re.findall(pattern,text);ck(re.sub(r'\s','',re.sub(pattern,'',text))=='','complete literal tree parse')
 def rec(i):
  s=toks[i]
  if s.startswith('if'):
   k=int(s.split()[3]);a,j=rec(i+1);ck(toks[j]=='else','tree branch');b,j=rec(j+1);return ('if',k,a,b),j
  return (tuple(map(int,s[1:-1].split(','))) if kind=='bounds' else int(s[3:])),i+1
 tree,end=rec(0);ck(end==len(toks),'all tree tokens')
 def at(t,n):return at(t[2] if n<t[1] else t[3],n) if isinstance(t,tuple) and t[0]=='if' else t
 return [at(tree,n) for n in range(203)]
bounds_text=source.split('private def bounds (n : Nat) : Nat × Nat × Nat :=\n')[1].split('\nprivate def H')[0]
vals=parse_tree(bounds_text,'bounds');H,Bb,C=map(list,zip(*vals));Cr=C.copy();Cr[5]=1
ptext=(R/'ProgramRouting245.lean').read_text();lookup=ptext.split('private def rawLookup (n : Nat) : Row :=\n')[1].split('\ndef nodes')[0]
ck(parse_tree(lookup,'rows')==list(range(203)),'exact lookup addresses')
rowlines=re.findall(r'^private def row(\d+) : Row := (.+)$',ptext,re.M);rows={}
for i,s in rowlines:
 edges=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',s)
 ck(len(edges)==2,'two edges');rows[int(i)]=[(k,int(n) if n else None) for k,n in edges]
ck(sorted(rows)==list(range(203)),'203 rows')
new=dict(rows);new[5]=[('decnz',6),('cont',2)];new[6]=[('inc',0),('node',5)]
for tag,rr,cc in [('old',rows,C),('rotated',new,Cr)]:
 ck(H[202]<=204 and Bb[202]==cc[202]==0,'root WF')
 for n,(l,r) in rr.items():
  for e in [l,r]:
   k,v=e;ck((k!='node' or v<203) and (k not in ['brk','cont'] or v>0),'edge valid')
   ck((H[v] if k=='node' else 0)<H[n],'height')
  be=lambda e:Bb[e[1]] if e[0]=='node' else 1 if e[0]=='decnz' else e[1] if e[0]=='brk' else 0
  ce=lambda e:cc[e[1]] if e[0]=='node' else e[1] if e[0]=='cont' else 0
  ck(be(l)<=Bb[n]+1 and be(r)<=Bb[n] and ce(l)<=cc[n] and ce(r)<=cc[n]+1,'escape bounds')
for n,pair in rows.items():
 if n not in [4,5,6]:ck(all(k!='node' or v not in [4,5] for k,v in pair),'safe children')
ck(rows[4]==[('inc',0),('cont',2)] and rows[5]==[('decnz',6),('node',4)] and rows[6]==[('node',5),('inc',0)],'old macro rows')
ck('if n < 203 then rawLookup n else (.halt, .halt)'in ptext,'outside nodes safe')
ck('private def rotatedC (n : Nat) : Nat := if n = 5 then 1 else C n'in source,'only new escape bound')
ck(len(re.findall(r'^#print axioms ',audit,re.M))==9 and len(re.findall(r'^example\b',audit,re.M))==10,'audit census')
ck(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',source+'\n'+audit),'default trusted proof scope')
# Exact current provider DAG and historical parent bindings; do not invoke guard.
pool={};tools={};parent_counts={}
for key,d in boundary['parents'].items():
 ck(sha(d['path'])==d['sha256'],'parent pin');e=json.loads(Path(d['path']).read_text());parent_counts[key]=len(e['before'])
 ck(e['status']=='PASS' and e['before']==e['after'] and e['all_input_provider_postchecks'],'actual parent')
 for p,h in e['before'].items():ck(sha(p)==h,'parent input '+p)
 for c in e['commands']:
  ck(sha(c['log'])==c['log_sha256'] and Path(c['log']).read_text()==c['output'],'parent raw log')
  ck(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'parent command')
 for k in ['source','audit']:ck(sha(e[k]['path'])==sha(e[k]['snapshot'])==e[k]['sha256'],'parent source snapshot')
 f=e['fresh_modules'][0];ck(sha(f['path'])==f['sha256'],'fresh parent')
 ck(e['source_pass_object']==dict(f,source_command_index=0),'preaudit source object')
 ck(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'preaudit first')
 for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
  z={k:q[k] for k in ['module','source','source_sha256','object','object_sha256']};ck(q['module'] not in pool or pool[q['module']]==z,'shared provider');pool[q['module']]=z
 for q in e['toolchain_providers']:tools[q['module']]={k:q[k] for k in ['module','object','object_sha256']}
 for q in e['reused_modules']:
  x=next(x for x in e['actual_first_providers'] if x['module']==q['module']);ck(Path(x['actual_first']).resolve()==Path(q['object']).resolve() and x['sha256']==q['object_sha256'],'historical first')
ck(pool=={q['module']:q for q in boundary['reused_modules']} and len(pool)==8,'exact union')
ck(tools=={q['module']:q for q in boundary['toolchain_providers']} and set(tools)=={'Init'},'exact tools')
for q in boundary['static_inputs']:ck(sha(q['path'])==q['sha256'],'static input')
for q in pool.values():
 for k in ['source','object']:ck(sha(q[k])==q[k+'_sha256'],'provider bytes')
for q in tools.values():ck(sha(q['object'])==q['object_sha256'],'tool bytes')
ck(sha(boundary['compiler']['path'])==boundary['compiler']['sha256'],'compiler bytes only')
imports=lambda s:re.findall(r'^import\s+(\S+)\s*$',s,re.M)
seen=set()
def dfs(m):
 if m=='Init':return
 ck(m in pool,'known import')
 if m in seen:return
 seen.add(m)
 for n in imports(Path(pool[m]['source']).read_text()):dfs(n)
for m in imports(source):dfs(m)
ck(seen==set(pool),'exact DFS')
ast.parse(guard)
# Full source read confirmed inheritance of unchanged process-group execution tail except census.
old=Path('/tmp/zfc243-combined-lean/simulation/check.py').read_text();tail=lambda s:s.split('        deadline=time.monotonic()+120')[1]
ck(tail(old).replace('named_axiom_probes=4,callers=4','named_axiom_probes=9,callers=10')==tail(guard),'execution tail exact except counts')
result=dict(status='INDEPENDENT_SOURCE_API_GUARD_REVIEW_PASS',findings=[],source=desc(B/'SourceRotation244.lean'),audit=desc(B/'Audit.lean'),guard=desc(B/'check.py'),boundary=desc(B/'boundary.json'),reviewer_source=desc(Path(__file__)),reviewer_role='Independent of concrete source/audit/emitter/guard; author of imported checked generic loop/context lemmas, disclosed rather than independent of those implementations.',checks=checks,finite_metadata=dict(rows=203,old_and_new_WF=True,safe_children=True,root=202,height=51,macro_entry=6,excluded_interior=[4,5],rotated_continue_bound=dict(node=5,value=1)),provider_scope=dict(projects=8,tools=['Init'],parent_input_references=parent_counts),mathematical_review=['Edge conversion is constructor inverse and ofDag preserves arbitrary program nodes/root/nnodes.','Finite WF checks establish both DAG height and root break/continue escape conditions, not merely acyclicity.','The generic local theorem is instantiated at old6/5/4 and new6/5, source register6 and destination0; full output and all exits are retained.','Safe context excludes interior nodes4/5; identical other rows and all safe children are checked; arbitrary out-of-range nodes are halt/halt.','Root iteration equivalence followed by RMEquiv.halts_iff_iterHalts proves empty-pointer path halting iff for arbitrary register functions.','Audits contain nine qualified probes and ten clients including nonhalting contrapositive.'],limits=['No compiler or supplied guard/emitter/checker invocation.','Lean elaboration, finite-check resource costs and actual target result remain pending root execution.','No binary runtime/startup, absolute consistency calibration or internal PA theorem claimed.'])
(B/'independent-source-guard-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(review=desc(B/'independent-source-guard-review.json'),checks=checks)))
