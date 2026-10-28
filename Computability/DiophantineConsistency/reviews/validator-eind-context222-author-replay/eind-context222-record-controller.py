import hashlib,json,re,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
OUT=Path(Path('/tmp/eind-context222-controller-latest').read_text().strip())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
inputs=json.loads((OUT/'inputs.json').read_text())
runs=sorted(OUT.glob('run-*.json'));latest={}
for run in runs:
    for r in json.loads(run.read_text()):
        if 'exit_code' in r:latest[r['module']]=r
final=[latest[n] for n in ['ZFCinPA.ValidatorEindContext222','ZFCinPA.ValidatorEindContext222Checks']]
require(len(final)==2 and all(r.get('exit_code')==0 for r in final),'two successful final leaves')
observations=[]
def check(p,h,kind):
    require(sha(p)==h,kind+' '+str(p));observations.append({'path':str(p),'sha256':h,'kind':kind})
check(inputs['compiler'],inputs['compiler_sha256'],'compiler')
check(ROOT/'lake-manifest.json',inputs['manifest_sha256'],'Lake manifest')
for p in inputs['parent_receipts']:check(p['path'],p['sha256'],'accepted parent or outline')
for r in inputs['modules']:
    check(r['source'],r['source_sha256'],'prerequisite source')
    for o in r['objects']:check(o['path'],o['sha256'],'prerequisite artifact')
for r in inputs['external']:check(r['path'],r['sha256'],'explicit external primary')
for r in final:
    for k in ['source','snapshot','log','timing']:check(r[k],r[k+'_sha256'],'final '+k)
    check(r['object']['path'],r['object']['sha256'],'final primary')
    r['lines']=len(Path(r['source']).read_text().splitlines())
require(Path(final[0]['log']).read_text()=='','clean final main')
raw=Path(final[1]['log']).read_text()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw,re.S)
require(len(reports)==12,'twelve reports')
axioms=[{'declaration':name,'axioms':[s.strip() for s in names.split(',')]} for name,names in reports]
require(all(set(r['axioms'])=={'propext','Classical.choice','Quot.sound'} for r in axioms),'standard only')
require(re.sub(r"'[^']+' depends on axioms: \[[^\]]*\]",'',raw,flags=re.S).strip()=='','no other check diagnostics')
rss=max(int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(r['timing']).read_text()).group(1)) for r in final)
drivers=[]
for p in ['/tmp/eind-context222-prepare-controller.py','/tmp/eind-context222-compile-controller.py','/tmp/eind-context222-record-controller.py']:
    drivers.append({'path':p,'sha256':sha(p),'source':Path(p).read_text()})
record={'status':'PASS',
 'scope':'Actual C222 represented Eind stack conjunction under explicit IΣ1: fixed graph and totality, finite projections/cons/currying, bounded endpoint-avoidance vacuity, diagonal context theorem and binder discharge via primitive weq-to-Eind precomposition. No uniform alpha/substitution, arbitrary proof translation, seed validity, CP/GIC or HA derivation.',
 'inputs':inputs,'input_inventory_sha256':sha(OUT/'inputs.json'),
 'final_leaves':final,'axioms':axioms,'fresh_prerequisite_count':0,'fresh_new_leaf_count':2,
 'maximum_rss_kib':rss,'all_source_and_object_postchecks':True,'postcheck_observations':len(observations),
 'postchecks':observations,'free_bytes_after':shutil.disk_usage('/tmp').free,'drivers':drivers,
 'development_runs':[{'path':str(p),'sha256':sha(p),'records':json.loads(p.read_text())} for p in runs],
 'development_notes':[
 'All153 prerequisite sources and504 prerequisite artifacts are reused; Vacuity222 uses the accepted fresh root provider. The117 Foundation providers retain the prior added20 trace-authenticated and2 historical-primary/later-companion distinction. No prerequisite or Foundation compilation is claimed.',
 'The import parser handles repeated public/private/meta modifiers. All40 external boundaries including Aesop are explicit in the authenticated parent inventory. Private LEAN_PATH uses only this overlay and recorded package roots.',
 'The264-line main passed on its first run with an empty log and was not recompiled after the checks-only fix. The initial checks had a Nat-inference ambiguity in a repeated-zero stack and broad-simp heartbeat exhaustion. Explicit V annotations and simp only[nth_adjoin_zero] repaired these focused clients without changing any main declaration or raising caps. Every run and source snapshot is preserved; final_leaves chooses each last successful executed leaf.']}
require(record['free_bytes_after']>=512*1024**2,'reserve')
p=REV/'validator-eind-context222-replay.json';p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'record':str(p),'sha256':sha(p),'lines':[(r['module'],r['lines']) for r in final],'postchecks':len(observations),'max_rss_kib':rss,'free_bytes':record['free_bytes_after']},indent=2))
