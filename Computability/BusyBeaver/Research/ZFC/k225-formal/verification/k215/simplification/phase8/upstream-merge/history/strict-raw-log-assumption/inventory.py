"""Read-only Git/worktree boundary census; writes only a new caller-selected scratch output."""
import argparse,hashlib,json,subprocess
from pathlib import Path
P='Computability/BusyBeaver/Research/ZFC/k225-formal/'
PRODUCTION=(P+'rocq/',P+'rocqperm/')
RECEIPTS=P+'verification/k215/rocq/normalized-91/'
def digest(b):return hashlib.sha256(b).hexdigest()
def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--repo',type=Path,required=True);a.add_argument('--ours',required=True);a.add_argument('--upstream',required=True);a.add_argument('--out',type=Path,required=True);x=a.parse_args()
 repo=x.repo.resolve()
 def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
 ours=git('rev-parse',x.ours+'^{commit}').decode().strip();upstream=git('rev-parse',x.upstream+'^{commit}').decode().strip()
 paths=git('diff','--name-only','--no-renames','-z',ours,upstream).decode().split('\0');paths=[p for p in paths if p]
 assert len(paths)==31
 prod=[p for p in paths if p.startswith(PRODUCTION)];receipts=[p for p in paths if p.startswith(RECEIPTS)]
 assert len(prod)==27 and len(receipts)==4 and set(prod+receipts)==set(paths)
 def blob(ref,p):
  line=git('ls-tree','-z',ref,'--',p)
  if not line:return {'present':False,'mode':None,'blob':None,'sha256':None,'bytes':None}
  head,name=line.rstrip(b'\0').split(b'\t');mode,kind,oid=head.decode().split();assert name.decode()==p and kind=='blob' and mode in ('100644','100755')
  b=git('cat-file','blob',oid);return {'present':True,'mode':mode,'blob':oid,'sha256':digest(b),'bytes':len(b)}
 def local(p):
  f=repo/p
  if not f.exists():assert not f.is_symlink();return {'present':False,'mode':None,'sha256':None,'bytes':None}
  assert f.is_file()and not f.is_symlink();b=f.read_bytes()
  return {'present':True,'mode':'100755'if f.stat().st_mode&0o111 else'100644','sha256':digest(b),'bytes':len(b)}
 rows=[]
 for p in paths:
  old=blob(ours,p);new=blob(upstream,p);work=local(p)
  assert work=={k:old[k]for k in work},p
  rows.append({'path':p,'action':'retain_checked_production'if p in prod else'accept_verbatim_upstream_receipt','sha256':old['sha256']if p in prod else new['sha256'],'current':old,'upstream':new,'worktree':work})
 priorpath=repo/(P+'verification/k215/simplification/phase7/upstream-merge/retained-production.json')
 prior=json.loads(priorpath.read_text());previous={r['path']:r['sha256']for r in prior['retain']if r['path'].startswith(PRODUCTION)}
 assert len(previous)==27 and previous=={r['path']:r['current']['sha256']for r in rows if r['path']in prod}
 # Merely bind the supplied receipt data; this is not its kernel replay.
 v=json.loads(git('show',upstream+':'+RECEIPTS+'verification.json'))
 compiled=v['compiled'];assert len(compiled)==44
 for mod,record in compiled.items():
  b=blob(upstream,P+'rocq/rocq-extension/coq/215/'+mod+'.v')
  assert b['present']and b['sha256']==record['source_sha256'],mod
 assert blob(upstream,RECEIPTS+'compilation.txt')['sha256']==v['compilation_log_sha256']
 assert blob(upstream,RECEIPTS+'coqchk.txt')['sha256']==v['coqchk']['log_sha256']
 result={'status':'PASS_READ_ONLY_MERGE_BOUNDARY_CENSUS','ours':ours,'upstream':upstream,'production_count':27,'production_existing':sum(r['current']['present']for r in rows if r['path']in prod),'production_absent':sum(not r['current']['present']for r in rows if r['path']in prod),'upstream_receipt_count':4,'retain':[r for r in rows if r['path']in prod],'upstream_receipts':[r for r in rows if r['path']in receipts],'previous_phase7_boundary_sha256':digest(priorpath.read_bytes()),'previous_27_production_pins_exact':True,'all31_current_worktree_states_match_ours':True,'upstream_receipt_data_binding':{'compiled_source_rows':44,'source_hashes_match_upstream':True,'raw_compilation_and_coqchk_log_hashes_match':True,'supplied_status':v['status'],'supplied_closed_reports':v['closed_reports'],'supplied_coqchk_target':v['coqchk']['target'],'supplied_coqchk_exit_code':v['coqchk']['exit_code'],'independent_compiler_or_coqchk_execution':False},'script_sha256':digest(Path(__file__).read_bytes()),'scope':'Exact Git blobs, raw bytes, modes/absences, and supplied-record source/log identity only. No adoption or fresh Rocq proof check.'}
 assert not x.out.exists();x.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in ['status','ours','upstream','production_count','production_existing','production_absent','upstream_receipt_count']},indent=2))
if __name__=='__main__':main()
