"""New read-only byte placement audit, authored before freeze."""
import argparse, hashlib, io, json, subprocess, zipfile
from pathlib import Path
REPO=Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT='111c38012'
HOST='Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
PRIOR='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_beyond_ord_e3839ad2c.md'
PIN='04cd0623189d2273958c469e2fc6e1a93c4e92c3293c108043da9d8e4e1d43d6'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
def sha(b):return hashlib.sha256(b).hexdigest()
def item(c,p):
 b=git('show',c+':'+p)
 return b,{'commit':c,'path':p,'bytes':len(b),'sha256':sha(b),'blob':git('rev-parse',c+':'+p).decode().strip()}
def build():
 c=git('rev-parse',COMMIT).decode().strip();parent=git('rev-parse',c+'^').decode().strip()
 changes=[line.split('\t') for line in git('diff-tree','--no-commit-id','--name-status','-r',c).decode().splitlines()]
 need(len(changes)==17 and [s for s,p in changes].count('A')==13 and [s for s,p in changes].count('D')==4,'exact change census')
 archives=[];payloads=[]
 for status,path in changes:
  if status!='D':continue
  need(path.startswith('docs/incoming/') and path.endswith('.zip'),'deleted archive')
  data,record=item(parent,path)
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   record['members']=[]
   for info in z.infolist():
    need(not info.is_dir(),'regular members');raw=z.read(info)
    record['members'].append({'path':info.filename,'bytes':len(raw),'sha256':sha(raw)})
    payloads.append((path,info.filename,raw))
  archives.append(record)
 records=[];placed=set()
 for status,path in changes:
  diff=git('diff','--no-ext-diff','--binary',parent,c,'--',path)
  rec={'status':status,'path':path,'diff_sha256':sha(diff),'diff_bytes':len(diff),'human_diff_read':False}
  if status=='A':
   need(path.startswith(HOST),'target host');raw,rec['after']=item(c,path)
   matches=[(a,n) for a,n,b in payloads if b==raw];need(len(matches)==1,'unique exact mapping')
   rec['archive'],rec['member']=matches[0];placed.add(matches[0])
  else:_,rec['before']=item(parent,path)
  records.append(rec)
 host=[];headings=[]
 for leaf in ['README.md','article.tex','article.pdf']:
  before,b=item(parent,HOST+leaf);after,a=item(c,HOST+leaf);need(before==after,'host unchanged')
  host.append({'before':b,'after':a})
  if leaf=='article.tex':
   headings=[{'line':i,'text':line} for i,line in enumerate(after.decode().splitlines(),1) if line.startswith('\\part{')]
 note=(REPO/PRIOR).read_bytes();need(sha(note)==PIN,'earlier intake')
 return {'schema':'beyond Ord support placement v1','placement':c,'parent':parent,'archives':archives,'changes':records,'unchanged_host':host,'literal_part_headings':headings,'unplaced_members':[{'archive':a,'member':n} for a,n,b in payloads if (a,n) not in placed],'prior_review':{'path':PRIOR,'bytes':len(note),'sha256':PIN},'totals':{'archives':len(archives),'members':len(payloads),'changes':len(records),'placements':len(placed),'unplaced_members':len(payloads)-len(placed),'unchanged_host':len(host),'part_headings':len(headings)},'scope':{'supplied_code_executed':False,'source_arrays_evaluated':False,'new_mathematical_review':False,'new_human_manuscript_read':False,'PDF_rendered':False,'diffs_human_read':False},'helper_sha256':sha(Path(__file__).read_bytes())}
p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();result=build();raw=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
if a.write:
 with a.write.open('xb') as f:f.write(raw)
else:need(a.expect.read_bytes()==raw,'exact receipt')
print(json.dumps({'status':'PASS','totals':result['totals'],'receipt_sha256':sha(raw)}))
