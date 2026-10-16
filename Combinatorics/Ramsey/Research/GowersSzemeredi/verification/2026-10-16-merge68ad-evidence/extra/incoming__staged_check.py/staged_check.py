from pathlib import Path
import subprocess,json,re,hashlib
O=Path('/tmp/gowers-incoming68ad-static-review');B='823ad7063d4f098246e204cea91f7756d5fe1aa3';L='5e5af281970d9f5c1ea637fa6b32fa7c4551a810';U='68ad8d39173bf0494fa46154869ccea9b1a3c623'
def git(*a):return subprocess.check_output(['git',*a],text=True)
H=lambda x:hashlib.sha256(x.encode()).hexdigest()
rows=json.loads((O/'source-summary.json').read_text());results=[]
for row in rows:
 if not row['local_overlap']:continue
 f=row['file'];temp=O/'merge-comparison'/Path(f).stem
 r=subprocess.run(['git','merge-file','-p','-L','LOCAL5e5a','-L','BASE823ad','-L','INCOMING68ad',str(temp/'local'),str(temp/'base'),str(temp/'incoming')],text=True,capture_output=True)
 s=r.stdout
 if r.returncode:
  pat=re.compile(r'^<<<<<<< LOCAL5e5a\n(.*?)^=======\n(.*?)^>>>>>>> INCOMING68ad\n',re.M|re.S)
  assert len(list(pat.finditer(s)))==r.returncode
  s=pat.sub(lambda m:m[1],s)
 staged=git('show',':'+f)
 assert s==staged,f
 results.append({'file':f,'conflict_count':r.returncode,'staged_sha256':H(staged),'exact_read_only_merge_with_local_conflict_block':True})
(O/'staged-overlap-check.json').write_text(json.dumps(results,indent=2)+'\n')
removed=json.loads((O/'removed-declarations.json').read_text());refs=[]
for x in removed:
 n=x['name'].split('.')[-1]
 r=subprocess.run(['git','grep','-n','-w','-e',n,U,'--','*.lean'],capture_output=True,text=True)
 assert r.returncode in [0,1]
 refs.append({'name':x['name'],'private':x['private'],'incoming_lean_references':r.stdout.splitlines()})
assert not any(x['incoming_lean_references'] for x in refs)
(O/'removed-name-reference-check.json').write_text(json.dumps(refs,indent=2)+'\n')
# Endpoints and proposition conventions are byte-identical upstream and on the staged merge.
files=['Final.lean','Definitions.lean','Proofs18CoverFejerAllDegrees.lean','Proofs18SharpInterfaces.lean']
finals=[]
for f in files:
 p='Combinatorics/Ramsey/Lean/GowersSzemeredi/'+f;b=git('show',B+':'+p);u=git('show',U+':'+p);l=git('show',L+':'+p);s=git('show',':'+p)
 assert b==u==l==s
 finals.append({'file':p,'sha256':H(b),'baseline_incoming_local_staged_byte_exact':True})
(O/'final-interface-files.json').write_text(json.dumps(finals,indent=2)+'\n')
print(json.dumps({'nine_overlap_checks':results,'all21_removed_names_absent_in_incoming_Lean':True,'final_interfaces':finals},indent=2))
