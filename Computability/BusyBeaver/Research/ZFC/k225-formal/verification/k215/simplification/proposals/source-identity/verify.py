#!/usr/bin/env python3
"""Verify the sealed archive and replay owned finite audits in a temporary copy."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
STAGES=[
 ('root/audit_ax_inference.py',[],['root/AX_INFERENCE_AUDIT.json','root/drafts/MacroWordInference.lean','root/drafts/L2AxiomsPerm.lean','root/drafts/L2AxiomsDom.lean','root/drafts/L2AxiomsPerm.lean.patch','root/drafts/L2AxiomsDom.lean.patch']),
 ('decoder/audit_direct_program.py',['--output-dir','decoder'],['decoder/DIRECT_PROGRAM_AUDIT.json','decoder/NODE_AND_ROLE_MAP.json']),
 ('decoder/make_direct_role_sketch.py',[],['decoder/DirectProgramCertificateDraft.lean']),
 ('rocq/audit_reuse.py',[],['rocq/REUSE_AUDIT.json','rocq/z465_producer.proposal.patch']),
 ('lean/audit_sources.py',['--out','lean/SOURCE_AUDIT.json'],['lean/SOURCE_AUDIT.json']),
 ('lean/check_guarded_subtype.py',['--out','lean/FINITE_CHECKS.json'],['lean/FINITE_CHECKS.json']),
 ('review/independent_data_check.py',[],['review/INDEPENDENT_DATA_CHECK.json'])]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(c,m):
 if not c:raise ValueError(m)
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',type=Path);args=parser.parse_args()
 require(not sys.flags.optimize,'Run without -O: component diagnostics use assertions.')
 seal=json.loads((ROOT/'SHA256SUMS.json').read_text())
 for name,h in seal.items():
  p=ROOT/name;require(p.resolve().is_relative_to(ROOT.resolve()),'Unsafe manifest member')
  require(p.is_file() and digest(p)==h,'Sealed file mismatch: '+name)
 print('PASS: all sealed files before replay.',flush=True)
 records=[];outputs=[]
 with tempfile.TemporaryDirectory(prefix='k215_proof_review_') as td:
  copy=Path(td)/'packet';copy.mkdir()
  for folder in ['root','decoder','rocq','lean','review']:
   shutil.copytree(ROOT/folder,copy/folder,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  for script,extra,produced in STAGES:
   require('/sources/' not in script,'Upstream execution is forbidden')
   print('Replay: '+script,flush=True)
   result=subprocess.run([sys.executable,'-B',script,*extra],cwd=copy,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),text=True,capture_output=True)
   require(result.returncode==0,'Audit failed: '+script+'\n'+result.stdout+'\n'+result.stderr)
   for name in produced:require(digest(copy/name)==digest(ROOT/name),'Non-reproducible artifact: '+name)
   outputs.extend(produced)
   records.append({'command':['python','-B',script,*extra],'exit_code':0,'byte_identical_outputs':produced,'stdout_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()})
 for name,h in seal.items():require(digest(ROOT/name)==h,'Original file changed: '+name)
 receipt={'status':'PASS','pin':'cbf94cb552a3b49509e0eee80e7455d4eb5974c6','python':'.'.join(map(str,sys.version_info[:3])),'replay_stages':records,'byte_identical_rebuilt_files':sorted(set(outputs)),'original_files_unchanged':True,'Lean_or_Rocq_compiled':False,'upstream_code_executed':False,'scope':'Exact source-data, integrity, finite regression and draft reproduction checks. Not universal semantic proofs, endpoint builds, timing measurements or machine reductions.'}
 if args.out:args.out.write_text(json.dumps(receipt,indent=2)+'\n')
 print('PASS: seven stages; '+str(len(set(outputs)))+' byte-identical rebuilt files; no formal compiler invoked.',flush=True)
if __name__=='__main__':main()
