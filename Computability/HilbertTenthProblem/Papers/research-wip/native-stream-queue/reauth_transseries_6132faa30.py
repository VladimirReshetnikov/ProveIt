"""Independent immutable-byte/locator review; no archived program executes."""
from pathlib import Path
import hashlib,io,json,re,subprocess,zipfile
R=Path('/home/codex/.codex/worktrees/2a71/Proofs');S=Path('/tmp/review_transseries_6132faa30')
PINS={'.md':'298e466baee5d2af0f37ff96f2175a5a7ad29795022406515650506f13c6a6b7','.json':'47e291e7955857182fdbc11e26cee96f85f0519f1a1960498475b1c34e57ed5f','.py':'6cdd6d9828cbcb3d24fc20c05570c702cfd9cac7e7c56cfb5302060807988e78'}
sha=lambda b:hashlib.sha256(b).hexdigest()
cache={};count=0;records=0
def ck(ok,msg):
 global count
 if not ok:raise ValueError(msg)
 count+=1
def git(*xs):return subprocess.check_output(['git','-C',str(R),*xs])
def blob(c,p):
 if (c,p) not in cache:cache[c,p]=git('show',c+':'+p)
 return cache[c,p]
for ext,h in PINS.items():ck(sha(Path(str(S)+ext).read_bytes())==h,'review pin')
j=json.loads(Path(str(S)+'.json').read_text());rev=j['revision'];par=j['parent']
ck(git('rev-parse',rev+'^').decode().strip()==par,'parent')
changed=[line.split('\t',1) for line in git('diff-tree','--no-commit-id','--name-status','-r',rev).decode().splitlines()]
ck(changed==[[f['status'],f['path']] for f in j['changed_files']],'complete changes')
todo=[j]
while todo:
 x=todo.pop()
 if isinstance(x,list):todo.extend(x)
 elif isinstance(x,dict):
  todo.extend(x.values())
  if {'commit','path','blob','bytes','sha256'}<=x.keys():
   b=blob(x['commit'],x['path']);records+=1
   ck(len(b)==x['bytes'] and sha(b)==x['sha256'],'file bytes')
   ck(git('rev-parse',x['commit']+':'+x['path']).decode().strip()==x['blob'],'blob identity')
   if 'lines' in x:ck(len(b.splitlines())==x['lines'],'line count')
for f in j['full_read_diffs']:
 d=git('diff','--no-ext-diff','--no-textconv','--unified=3',par,rev,'--',f['path'])
 ck((len(d),sha(d),len(d.splitlines()))==(f['diff_bytes'],f['diff_sha256'],f['diff_lines']),'whole diff')
span_count=span_lines=0
for f in j['read_files']:
 lines=blob(f['commit'],f['path']).splitlines(keepends=True)
 for s in f['read_spans']:
  lo,hi=s['first'],s['last'];ck(1<=lo<=hi<=len(lines),'span range');b=b''.join(lines[lo-1:hi])
  ck(len(b)==s['bytes'] and sha(b)==s['sha256'],'span bytes');span_count+=1;span_lines+=hi-lo+1
members=placed=entries=0
for a in j['archives']:
 archive=blob(a['commit'],a['path']);ck(archive==blob(a['arrival']['commit'],a['arrival']['path']),'arrival equality')
 with zipfile.ZipFile(io.BytesIO(archive)) as z:
  names=sorted(n.filename for n in z.infolist() if not n.is_dir())
  ck(names==sorted(m['path'] for m in a['members']),'complete archive inventory')
  files={m['relative_path']:z.read(m['path']) for m in a['members']}
  for m in a['members']:
   b=z.read(m['path']);ck(len(b)==m['bytes'] and sha(b)==m['sha256'],'member');members+=1
   if m['placement']:
    p=m['placement'];ck(b==blob(p['commit'],p['path']),'exact placed bytes');placed+=1
  manifest=[]
  for line in files['MANIFEST.sha256'].decode().splitlines():
   if not line.strip():continue
   h,path=line.split(None,1);path=path.strip().lstrip('*')
   ck(sha(files[path])==h,'manifest entry');manifest.append({'path':path,'sha256':h});entries+=1
  ck(manifest==a['manifest_checks'],'complete manifest checks')
for t in j['tex_metadata']:
 labels=set(r['label'] for r in t['labels']);ck(len(labels)==len(t['labels']),'unique labels')
 for lab in t['labels']:
  line=blob(rev,lab['path']).decode().splitlines()[lab['line']-1]
  ck(lab['label'] in re.findall(r'\\label(?:\[[^\]]*\])?\s*\{([^}]+)\}',line),'label locator')
 for ref in t['references']:
  line=blob(rev,ref['path']).decode().splitlines()[ref['line']-1]
  ck(ref['label'] in labels and ref['label'] in line,'reference locator')
 ck(set(t['citation_keys'])<=set(t['bibliography_keys']),'citation targets')
ck((members,placed,entries,span_count,span_lines)==(45,43,43,14,2767),'totals')
out={'input_pins':PINS,'helper_sha256':sha(Path(__file__).read_bytes()),'checks':count,'file_record_instances':records,'unique_git_files':len(cache),'changed_paths':len(changed),'archive_members':members,'exact_placements':placed,'manifest_entries':entries,'read_spans':span_count,'read_lines':span_lines,'diffs':len(j['full_read_diffs']),'scope':'Independent byte/locator reauthentication and separate proof-only review of proper-weights counterexample. No source code/build execution, complete analytic proof audit, or repetition of author numerical checks.'}
dest=Path('/tmp/reauth_transseries_6132faa30.json');dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));print('receipt_sha256',sha(dest.read_bytes()))
