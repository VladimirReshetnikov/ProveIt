"""Fresh independent byte/locator authentication; no predecessor execution."""
from pathlib import Path
import hashlib,json,re,subprocess,posixpath

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
STEM=Path('/tmp/review_new_reciprocal_ddb36da6c')
PINS={'.md':'378986ba3bab75ea1ba84c560f9ec422ec2fdebd641eabddeb2e351209c4b200','.json':'385da6e276f1431c1cd1833847f2a1fb8837d7554fc5ddfb730ff601e1b85909','.py':'ced8c79b27984870fb1e1acd39109b1f5a72f917491e3be79014812a473aab7d'}
sha=lambda b:hashlib.sha256(b).hexdigest()
cache={};checks=0
def check(ok,why):
 global checks
 if not ok:raise ValueError(why)
 checks+=1
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args])
def content(c,p):
 if (c,p) not in cache:cache[c,p]=git('show',c+':'+p)
 return cache[c,p]
def declarations(data,kind):return re.findall(r'\\'+kind+r'\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',data.decode())
for ext,h in PINS.items():check(sha(Path(str(STEM)+ext).read_bytes())==h,'packet pin')
j=json.loads(Path(str(STEM)+'.json').read_text());rev=j['commit'];before=j['parent']
check(git('rev-parse',rev+'^').decode().strip()==before,'parent')
check(git('diff-tree','--no-commit-id','--name-only','-r',rev).decode().splitlines()==[f['path'] for f in j['files']],'complete changed list')
record_count=0
def walk(obj):
 global record_count
 if isinstance(obj,dict):
  if {'commit','path','blob','bytes','sha256'}<=obj.keys():
   b=content(obj['commit'],obj['path']);record_count+=1
   check(len(b)==obj['bytes'] and sha(b)==obj['sha256'],'file bytes')
   check(git('rev-parse',obj['commit']+':'+obj['path']).decode().strip()==obj['blob'],'blob')
   if 'span_sha256' in obj:
    lo,hi=obj['start_line'],obj['end_line'];lines=b.splitlines(keepends=True)
    check(1<=lo<=hi<=len(lines),'span range');s=b''.join(lines[lo-1:hi])
    check(len(s)==obj['span_bytes'] and sha(s)==obj['span_sha256'],'span bytes')
  for v in obj.values():walk(v)
 elif isinstance(obj,list):
  for v in obj:walk(v)
walk(j)
addition=deletion=diff_lines=0
for f in j['files']:
 p=f['path'];d=git('diff','--no-ext-diff','--no-textconv','--unified=3',before,rev,'--',p)
 check(sha(d)==f['diff_sha256'] and len(d)==f['diff_bytes'],'diff')
 if 'hunks' in f:
  lines=d.decode().splitlines();a=sum(s.startswith('+') and not s.startswith('+++') for s in lines);z=sum(s.startswith('-') and not s.startswith('---') for s in lines)
  check((a,z,len(lines))==(f['added_lines'],f['removed_lines'],f['diff_lines']),'diff totals');addition+=a;deletion+=z;diff_lines+=len(lines)
  hs=[]
  for line in lines:
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
   if m:hs.append(dict(zip(['before_start','before_count','after_start','after_count'],[int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1)])))
  check(hs==f['hunks'],'hunk ranges')
 if p.endswith('.tex'):
  for kind,key in [('label','unchanged_label_list'),('bibitem','unchanged_bibliography_keys')]:
   check(declarations(content(before,p),kind)==declarations(content(rev,p),kind)==f[key],'ordered declarations')
for r in j['added_label_routes']:
 line=content(rev,r['source_path']).decode().splitlines()[r['source_line']-1]
 check(r['label'] in line,'source occurrence')
 targets=[]
 for f in j['label_index_files']:
  for n,line in enumerate(content(rev,f['path']).decode().splitlines(),1):
   if r['label'] in declarations(line.encode(),'label'):targets.append({'path':f['path'],'line':n})
 check(targets==r['matches'] and len(targets)==1,'unique target')
for r in j['new_citations']:
 check(r['key'] in declarations(content(rev,r['path']),'bibitem'),'citation target')
 check(r['key'] in content(rev,r['path']).decode().splitlines()[r['line']-1],'citation source')
for r in j['new_local_markdown_links']:
 target=posixpath.normpath(posixpath.join(posixpath.dirname(r['path']),r['literal_target']))
 check(target==r['resolved_path'] and git('rev-parse',rev+':'+target).decode().strip()==r['git_object'],'local link')
ctx=j['prior_review_context'];check(sha(Path(ctx['path']).read_bytes())==ctx['sha256'],'prior review pin')
check((addition,deletion,diff_lines)==(97,5,181),'global diff totals')
out={'review_pins':PINS,'commit':rev,'helper_sha256':sha(Path(__file__).read_bytes()),'checks':checks,'file_record_instances':record_count,'unique_git_files':len(cache),'diffs':len(j['files']),'read_spans':len(j['human_read_spans']),'label_targets':len(j['added_label_routes']),'citation_targets':len(j['new_citations']),'local_links':len(j['new_local_markdown_links']),'scope':'Independent bytes/locators plus full review-MD read; no new complete mathematical proof audit, no predecessor execution.'}
dest=Path('/tmp/reauth_new_reciprocal_ddb36da6c.json');dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));print('receipt_sha256',sha(dest.read_bytes()))
