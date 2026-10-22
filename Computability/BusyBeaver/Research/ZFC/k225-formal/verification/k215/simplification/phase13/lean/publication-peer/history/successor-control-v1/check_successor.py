from pathlib import Path
import ast, hashlib, json, re
S=Path('/tmp/k215-phase13-publication'); O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
assert sha(S/'freeze.json')=='d7ae992e234a3d35656998ea6f724c64e59a3c6a0ff47ae326686c76f784c649'
f=load(S/'freeze.json'); old=S/'history/helper-v1'; pf=load(old/'freeze.json')
assert sha(old/'freeze.json')==f['predecessor_freeze_sha256']
for n,h in f['files'].items(): assert sha(S/n)==h,n
for n,h in pf['files'].items(): assert sha(old/n)==h,n
assert {n for n in f['files'] if f['files'][n]!=pf['files'][n]}=={'packet.py','controls.py','config.json'}
a=(old/'packet.py').read_text(); b=(S/'packet.py').read_text()
line="   if m in CLIENTS: assert [set(a) for a in r['report_axioms']] == [STANDARD]*len(r['reports'])"
replacement="   if m == 'WFModelCompat12': assert [set(a) for a in r['report_axioms']] == [STANDARD]*3\n   if m == 'ZFNativeCompat12': assert [set(a) for a in r['report_axioms']] == [PQ]+[STANDARD]*6"
assert a.count(line)==1 and a.replace(line,replacement)==b
c1=load(old/'config.json'); c2=load(S/'config.json')
assert {k:v for k,v in c1.items() if k!='files'}=={k:v for k,v in c2.items() if k!='files'}
assert all(c2['files'][k]==v for k,v in c1['files'].items())
for p,r in c2['files'].items(): assert sha(p)==r['sha256'] and Path(p).stat().st_size==r['bytes'],p
failure=load('/tmp/k215-phase13-publication-execution/collect-actual.json')
assert failure['exit_code']==1 and failure['helper_freeze_sha256']==sha(old/'freeze.json')
assert sha(failure['stderr'])==failure['stderr_sha256'] and 'packet.py", line 155' in Path(failure['stderr']).read_text()
# Read-only raw compiler report comparison; no compiler or helper module execution.
P=Path('/tmp/k215-phase13-upstream-check/compatibility-run1'); done=load(P/'completed.json')
STANDARD={'propext','Classical.choice','Quot.sound'}; PQ={'propext','Quot.sound'}
profiles={'WFModelCompat12':[STANDARD]*3,'ZFNativeCompat12':[PQ]+[STANDARD]*6}
rows=[]
for m,expected in profiles.items():
 r=done[m]; data=Path(r['log']).read_bytes(); assert hashlib.sha256(data).hexdigest()==r['log_sha256']
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",data.decode())
 assert reports==[tuple(x) for x in r['reports']]
 assert [set(x.strip() for x in axioms.split(','))for name,axioms in reports]==expected
 rows.append({'module':m,'log_sha256':r['log_sha256'],'reports':r['reports']})
# Extract only the pure named-report functions, with no imports or full validator invocation.
t=ast.parse(b); nodes=[n for n in t.body if isinstance(n,ast.FunctionDef) and n.name in {'reports','named_reports'}]
env={'re':re,'STANDARD':STANDARD};exec(compile(ast.Module(body=nodes,type_ignores=[]),'packet-pure-functions','exec'),env)
tests=[]
for label,raw,want in [('exact PQ',b"'Exact.client' depends on axioms: [propext, Quot.sound]\n",True),('extra choice',b"'Exact.client' depends on axioms: [propext, Classical.choice, Quot.sound]\n",False),('missing propext',b"'Exact.client' depends on axioms: [Quot.sound]\n",False)]:
 try:env['named_reports'](raw,['Exact.client'],[PQ]);got=True
 except AssertionError:got=False
 assert got==want;tests.append({'case':label,'accept':want})
v={'status':'PASS_NARROW_SUCCESSOR_SOURCE_REVIEW','scope':'Metadata-only source and raw-report peer; no collector, saved reader, compiler, producer or archive code execution. Prior failed capture and v1 review remain historical. This does not accept a future packet.', 'freeze_sha256':sha(S/'freeze.json'),'predecessor_freeze_sha256':sha(old/'freeze.json'),'helper_pins':f['files'],'original_peer_sha256':sha(O/'review.json'),'context_files_rehashed':len(c2['files']),'preserved_context_files':len(c1['files']),'raw_compatibility_profiles':rows,'pure_controls':tests,'first_capture_exit_code':failure['exit_code'],'first_capture_record_sha256':sha('/tmp/k215-phase13-publication-execution/collect-actual.json'),'checker_sha256':sha(__file__),'findings':[],'acknowledgment':'The earlier source review missed the redundant all-standard assertion. The successor requires the exact already-checked profiles rather than relaxing to a standard-axiom subset.'}
(O/'review-v2.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({'status':v['status'],'receipt_sha256':sha(O/'review-v2.json')}))
