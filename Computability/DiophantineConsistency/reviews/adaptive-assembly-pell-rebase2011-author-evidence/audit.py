from pathlib import Path
import hashlib,json,os,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';B=Path(os.environ['ADAPTIVE_HALF_BASE']);P=Path('/tmp/adaptive13-assembly-pell-mg258xlh');seeds={'ArithmeticPellSquaredSeed','ArithmeticPellSquaredSeedChecks','ArithmeticPellAuxiliarySeed','ArithmeticPellAuxiliarySeedChecks'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
bs=read(B/'state.json');ps=read(P/'state.json');pa=read(P/'audit.json');assert bs['status']==ps['status']=='PASS';seen=set();deps={}
def visit(n):
 if n in seen:return
 seen.add(n);src=S/(n+'.lean');assert src.is_file();deps[n]=re.findall(r'^import DiophantineConsistency\.([\w]+)',src.read_text(),re.M)
 for x in deps[n]:visit(x)
for n in seeds:visit(n)
assert 'ArithmeticHalfBinomial' not in seen and 'ArithmeticAdaptivePopulation2011' not in seen
rows=[]
for n in sorted(seen-seeds):
 row=next((x for x in pa['rows'] if x['module']==n),None);assert row,n;src=S/(n+'.lean');old=P/'lib/DiophantineConsistency'/(n+'.olean');new=B/'lib/DiophantineConsistency'/(n+'.olean');assert old.is_file() and new.is_file(),n
 assert sha(src)==row['source_sha256'] and sha(old)==row['object_sha256'] and sha(new)==row['object_sha256'],n
 rows.append({'module':n,'source':str(src),'source_sha256':sha(src),'old_object':str(old),'new_object':str(new),'object_sha256':sha(old)})
seedrows=[]
for n in sorted(seeds):
 r=next(x for x in ps['records'] if x['name']==n);src=S/(n+'.lean');obj=P/'lib/DiophantineConsistency'/(n+'.olean');assert sha(src)==r['source_sha256'] and sha(obj)==r['object_sha256'];seedrows.append({'module':n,'source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj)})
res={'scope':'four accepted seed/check objects and their DiophantineConsistency dependency closure; cross-namespace/package internals inherited','base':str(B),'base_state_sha256':sha(B/'state.json'),'seed_provider':str(P),'seed_state_sha256':sha(P/'state.json'),'rows':rows,'seeds':seedrows};out=Path(os.environ.get('ADAPTIVE_PELL_REBASE_AUDIT_OUT','/tmp/adaptive13-assembly-pell-rebase-audit.json'));out.write_text(json.dumps(res,indent=2)+'\n');print('seed dependencies',len(rows),'seeds',len(seedrows),'source and object hashes match',flush=True)
