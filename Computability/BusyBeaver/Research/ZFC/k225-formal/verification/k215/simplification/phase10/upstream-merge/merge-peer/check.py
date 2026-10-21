from pathlib import Path
import hashlib,json,subprocess,re
from urllib.parse import unquote
R=Path('/home/codex/.codex/worktrees/ec20/Proofs'); O=Path('/tmp/k215-phase10-upstream-merge-peer')
F='Computability/BusyBeaver/Research/ZFC/k225-formal'; M=F+'/verification/k215/simplification/phase10/upstream-merge'
H='887eb42d50cc687689d367c8dd720045cbcced81'; U='2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'
def git(*args): return subprocess.check_output(['git',*args],cwd=R)
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def blob(rev,p): return git('show',rev+':'+p)
def same(p,ref=None,pin=None):
 b=(R/p).read_bytes(); idx=blob('',p); assert b==idx,p+' index/worktree';
 if ref: assert b==blob(ref,p),p+' checkpoint'
 if pin: assert sha(b)==pin,p+' pin'
 return {'path':p,'sha256':sha(b),'bytes':len(b),'index_blob':git('rev-parse',':'+p).decode().strip()}
assert git('rev-parse','HEAD').decode().strip()==H
assert git('rev-parse','MERGE_HEAD').decode().strip()==U
assert not git('ls-files','-u')
manifest=read(R/M/'merge.json'); decisions=[]
changed=set(git('diff','--name-only',manifest['base_commit'],U).decode().splitlines())
assert changed=={x['path'] for x in manifest['paths']}
for x in manifest['paths']:
 p=x['path']; b=blob(U,p); assert sha(b)==x['upstream_sha256'] and len(b)==x['bytes']
 row=same(p,pin=x['selected_sha256']); assert row['bytes']==x['selected_bytes']
 um=git('ls-tree',U,'--',p).decode().split()[0]; im=git('ls-files','-s','--',p).decode().split()[0]; assert um==im
 if x['decision']=='imported_research_verbatim': assert b==(R/p).read_bytes()
 if x['decision']=='retained_exact_checked_phase10': assert b!=(R/p).read_bytes() and blob(H,p)==(R/p).read_bytes()
 row.update(decision=x['decision'],upstream_sha256=sha(b),mode=im);decisions.append(row)
inv=read('/tmp/k215-phase10-main/full-run1/inventory.json')['modules']; ledger=read('/tmp/k215-phase10-main/canonical-review.json')['ledger']
assert len(inv)==len(ledger)==197 and {x['module'] for x in inv}==set(ledger)
leans=[]
for x in inv:
 l=ledger[x['module']]; assert l['source']==x['source_sha256']; leans.append(same(l['canonical'],H,x['source_sha256']))
adoptions=[same(x['target'],H,x['sha256']) for x in read('/tmp/k215-phase10-main/adoption.json')['files']]; assert len(adoptions)==4
own=read('/tmp/k215-phase10-main/final-files.json')['files']; assert len(own)==123
exceptions={F+'/README.md',F+'/rho8cd/PROVEIT_STATUS.md'}; unchanged=[]
for x in own:
 p=x['path']; assert sha(blob(H,p))==x['sha256'] and len(blob(H,p))==x['bytes']
 if p not in exceptions: unchanged.append(same(p,H,x['sha256']))
assert len(unchanged)==121
packet=[same(x['destination'],H,x['sha256']) for x in read('/tmp/k215-phase10-published/copy-map.json')['files']]; assert len(packet)==28
packet_all=git('ls-tree','-r','--name-only',H,'--',F+'/verification/k215/simplification/phase10/lean').decode().splitlines()
for p in packet_all:same(p,H)
rocq=[same(F+'/rocq/rocq-extension/'+p,H) for p in ['coq/215/DomRho8.v','coq/regeneration215.json','manifest.json','regenerate215.py']]
cm=read(R/M/'copy-map.json'); copies=[]
for x in cm['files']:
 row=same(x['destination'],pin=x['sha256']); assert row['bytes']==x['bytes'] and Path(x['source']).read_bytes()==(R/x['destination']).read_bytes();copies.append(row)
assert len(copies)==13
staged=git('diff','--cached','--name-only').decode().splitlines(); assert len(staged)==24
expected={x['path'] for x in manifest['paths'] if x['decision']!='retained_exact_checked_phase10'}|{x['destination'] for x in cm['files']}|{M+'/'+n for n in ['README.md','copy-map.json','merge.json','whitespace-review.json']}
assert set(staged)==expected
for p in staged:same(p)
links=[]
for p in [F+'/README.md',F+'/rho8cd/PROVEIT_STATUS.md',M+'/README.md',M+'/source-review/review.md']:
 for target in re.findall(r'\]\(([^\s)]+)(?:\s+"[^\"]*")?\)',(R/p).read_text()):
  if re.match(r'^[a-zA-Z]+:',target) or target.startswith('#'):continue
  t=unquote(target.split('#')[0]); dest=(R/p).parent/t
  assert dest.exists(),(p,target)
  links.append({'source':p,'target':target})
w=read(R/M/'whitespace-review.json'); c=subprocess.run(['git','diff','--cached','--check'],cwd=R,capture_output=True,text=True)
assert c.returncode==2
assert len(w['exceptions'])==1 and c.stdout==w['exceptions'][0]['diagnostic']
assert sha((R/w['exceptions'][0]['path']).read_bytes())==w['exceptions'][0]['sha256']
result={'status':'PASS_READ_ONLY_PENDING_MERGE','head':H,'merge_head':U,'staged_paths':staged,'nine_decisions':decisions,'Lean_sources':leans,'adoption_files':adoptions,'checkpoint_files_checked':123,'checkpoint_files_unchanged':121,'checkpoint_prose_exceptions':sorted(exceptions),'packet_map_files':packet,'packet_tracked_files_checked':len(packet_all),'retained_Rocq':rocq,'static_review_copies':copies,'local_links_checked':links,'raw_whitespace_exception':w['exceptions'][0]['path'],'compiler_invocations':0,'delivered_code_executed':False}
(O/'bindings.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','checkpoint_files_checked','checkpoint_files_unchanged','packet_tracked_files_checked']}));print('197 Lean; 4 adoptions; 5 verbatim research; 4 Rocq; 13 static copies; '+str(len(links))+' local links')
