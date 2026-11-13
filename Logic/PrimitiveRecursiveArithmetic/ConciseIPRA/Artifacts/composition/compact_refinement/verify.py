"""Matched protocol regressions and source-corpus duplicate audit.

The universal argument is in PROOF.txt; these are supporting finite checks.
"""
from pathlib import Path
import ast,io,tokenize,gzip,json,subprocess,sys,hashlib
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'code'
PROGRAMS={'control238':BASE/'control_tokens238.py','candidate236':BASE/'checker_tokens236.py','candidate236_set':BASE/'checker_tokens236_set.py','candidate236_lambda':BASE/'checker_tokens236_lambda.py'}
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
def measure(p):
 t=ast.parse(p.read_text());n=(ast.unparse(t)+'\n').encode()
 return {'tokens':sum(x.type not in SKIP for x in tokenize.tokenize(io.BytesIO(n).readline)),'ast_nodes':sum(1 for _ in ast.walk(t)),'normalized_bytes':len(n),'gzip9_bytes':len(gzip.compress(n,compresslevel=9,mtime=0)),'normalized_sha256':hashlib.sha256(n).hexdigest()}
def run(p,data,opt):
 cmd=[sys.executable,'-I','-S','-B']+(['-O']if opt else[])+[str(p)]
 try:
  q=subprocess.run(cmd,input=data,capture_output=True,text=True,timeout=12)
  return q.returncode==0 and q.stdout=='ACCEPT\n'
 except subprocess.TimeoutExpired:return False
cases=[]
for p in sorted((ROOT/'fixtures').glob('*.jsonl')):
 ls=p.read_text().splitlines();goal=json.loads(ls[0]);ls[0]=json.dumps([[0],goal]);data='\n'.join(ls)+'\n'
 cases.append((p.stem,data))
truth=[0,0];false=[0,[0]];packet='[0,0,0]\n'
for name,g,a in [('open_false_identity',[0,false],false),('open_truth_identity',[0,truth],truth),('false_empty_context',[0],false),('false_truth_context',[0,truth],false),('future_goal',[0],[-1,0])]:
 cases.append((name,json.dumps([g,a])+'\n'+packet))
results=[];failures=[]
for name,data in cases:
 for opt in [False,True]:
  v={p:run(q,data,opt) for p,q in PROGRAMS.items()}
  row={'case':name,'optimized':opt,'accepted':v};results.append(row)
  if len(set(v.values()))!=1:failures.append(row)
# Canonical positive and negative cases certify that agreement is nonvacuous.
positive=['global_computation_zero','global_computation_successor','global_guarded_induction_with_used_hypothesis','global_compound_implication_elimination','open_false_identity','open_truth_identity']
negative=['false_empty_context','false_truth_context','future_goal','reject_context_leak','reject_future_scope_attack','reject_future_witness_capture']
for x in results:
 expected=True if x['case'] in positive else False if x['case'] in negative else None
 if expected is not None and any(v!=expected for v in x['accepted'].values()):failures.append({'expected':expected,**x})
# The two-line pre-major witness boundary is not moved by context construction.
p=(ROOT/'fixtures/future_witness_before_major.jsonl');ls=p.read_text().splitlines();ls[0]=json.dumps([[0],json.loads(ls[0])]);boundary=[]
for name,path in PROGRAMS.items():
 stream=iter(ls);reads=[]
 def inp():
  x=next(stream);reads.append(x);return x
 try:exec(compile(path.read_text(),str(path),'exec'),{'input':inp,'print':lambda *x:None});err=None
 except Exception as e:err=type(e).__name__
 boundary.append({'program':name,'lines_read':len(reads),'exception':err})
 if err!='TypeError' or len(reads)!=2:failures.append(boundary[-1])
metrics={name:measure(p) for name,p in PROGRAMS.items()}
ledger=json.loads((ROOT.parent/'reference/source_census.json').read_text())
audit={'source_entries_scanned':len(ledger['entries']),'candidates':{}}
duplicates={}
for name,path in PROGRAMS.items():
 if name=='control238':continue
 digest=metrics[name]['normalized_sha256']
 matches=[{'origin':row['origin'],'path':row['path']} for row in ledger['entries'] if row['normalized_sha256']==digest]
 audit['candidates'][path.name]={'normalized_sha256':digest,'matches':matches}
 duplicates[name]=matches
(ROOT/'source_audit236.json').write_text(json.dumps(audit,indent=2)+'\n')
receipt={'python':sys.version,'source_entries_scanned':audit['source_entries_scanned'],'metrics':metrics,'cases':len(cases),'process_executions':len(cases)*2*len(PROGRAMS),'failures':failures,'boundary':boundary,'duplicates':duplicates,'results':results,'claim':'Finite differential evidence; all-input equivalence on the documented list-context contract is proved separately.'}
(ROOT/'reproduced236.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
if failures or any(duplicates.values()):raise SystemExit(1)
