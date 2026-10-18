#!/usr/bin/env python3
"""Fresh external combined243 replay: blank, affine, literal, optionally expanded.

This calls the three reviewed ordinary Python adapters directly, never a
delivery manifest wrapper or a proof compiler. Run recover_167.py separately
and supply its package's reference/baseline245 directory with --reference.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, signal, subprocess, sys, time

HERE=Path(__file__).resolve().parent
REFERENCE_INDEX_SHA='2d7710b02b200a1f0641fb9bb72fc0a881230f9bef0ca7ebd1164e53a31689ba'
DATA={
 'zfc_combined243.tm':('machine.tm','a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791'),
 'zfc_combined243_old.tm':('machine_old.tm','4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'),
 'renumbering.json':('renumbering.json','4a47f6d323aa460f6208e16babfd67919a27cc7ce7b9f34b33a71795723e630a'),
 'sites_logical.json':('sites_logical.json','3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'),
 'sites_physical.json':('sites_physical.json','ee14a4496cc216de7c242f5e652de47d455169d79856ba36bee3a4fc3d69d86a')}
ADAPTERS={
 'check_runtime_combined243.py':'36194a01234756eea08726179d30de92add0bcb2515b19a0f87d810698babcd7',
 'check_combined243_literal.py':'a4d50bf745986669160465f4674112b43c25da1e00b397e80622736ebc6e8ee4',
 'check_combined243_blank.py':'2f6c2df431c15312231019f9635601aeff0c6d1057c8ca042215ec1391c5190e'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,why):
 if not ok:raise RuntimeError(why)
def load(p):return json.loads(Path(p).read_text())
def desc(p):return dict(path=str(p),sha256=sha(p))
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--candidate',type=Path,default=HERE.parent)
 ap.add_argument('--reference',type=Path,required=True)
 ap.add_argument('--reference-index',type=Path,default=HERE/'reproduction-reference.json')
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--expanded',action='store_true',help='Also run all8390 expanded symbolic cases, with a600-second process limit.')
 a=ap.parse_args();need(__debug__,'Python assertions must be enabled.')
 candidate,reference,output=a.candidate.resolve(),a.reference.resolve(),a.output.resolve()
 need(candidate.is_dir() and reference.is_dir(),'Candidate and recovered reference directories must exist.')
 need(not output.exists(),'Output must be a new directory; attempts are never overwritten.')
 need(not output.is_relative_to(candidate) and not output.is_relative_to(reference),'Output must be outside both input trees.')
 repository=next((p for p in [candidate,*candidate.parents] if (p/'.git').exists()),None)
 need(repository is None or not output.is_relative_to(repository),'Output must be outside the repository.')
 inputs={}
 def pin(p,h):
  p=Path(p);need(not p.is_symlink() and p.is_file() and sha(p)==h,'Changed input: '+str(p));p=p.resolve()
  need(str(p) not in inputs or inputs[str(p)]==h,'Conflicting input identity.')
  inputs[str(p)]=h;return p
 index=pin(a.reference_index,REFERENCE_INDEX_SHA);meta=load(index)
 need(len(meta['files'])==291,'Unexpected reference input census.')
 selected=[];names=set()
 for q in meta['files']:
  rel=PurePosixPath(q['path']);need(not rel.is_absolute() and '..' not in rel.parts and '\\' not in q['path'],'Unsafe reference member.')
  need(q['path'] not in names,'Duplicate reference member.');names.add(q['path'])
  src=pin(reference.joinpath(*rel.parts),q['sha256']);need(src.is_relative_to(reference),'Reference member escaped root.')
  need(src.stat().st_size==q['bytes'],'Reference member size changed.');selected.append((src,Path(*rel.parts)))
 for name,(_,h) in DATA.items():pin(candidate/name,h)
 for name,h in ADAPTERS.items():pin(candidate/'provenance'/name,h)
 pin(Path(__file__).resolve(),sha(__file__))
 output.mkdir();work=output/'candidate';work.mkdir();code=output/'adapters';code.mkdir();ref=output/'reference';ref.mkdir()
 for src,rel in selected:
  dst=ref/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);pin(dst,sha(src))
 for name,(target,h) in DATA.items():shutil.copyfile(candidate/name,work/target);pin(work/target,h)
 for name,h in ADAPTERS.items():shutil.copyfile(candidate/'provenance'/name,code/name);pin(code/name,h)
 record=dict(status='RUNNING',expanded_requested=a.expanded,ordinary_python_replay=True,proof_compiler_executed=False,
  delivery_manifest_wrapper_executed=False,delivery_checksum_manifests_verified=False,reference_index=desc(index),
  source_reference=str(reference),source_candidate=str(candidate),before=dict(inputs),commands=[])
 def save():(output/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
 def post():
  record['after']={p:sha(p)for p in inputs};need(record['after']==record['before'],'Input or copied input changed.')
  record['all_input_postchecks']=True
 save()
 def run(label,args,limit):
  cmd=[sys.executable,'-I','-B',*map(str,args)];start=time.monotonic();timed=False;interrupted=None
  outlog=output/(label+'.stdout.log');errlog=output/(label+'.stderr.log')
  with outlog.open('wb')as out,errlog.open('wb')as err:
   proc=subprocess.Popen(cmd,cwd=output,stdout=out,stderr=err,start_new_session=True)
   try:proc.wait(timeout=limit)
   except BaseException as ex:
    timed=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timed else type(ex).__name__
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    proc.wait()
  record['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-start,timeout_seconds=limit,
   exit_code=proc.returncode,timed_out=timed,interrupted=interrupted,stdout=desc(outlog),stderr=desc(errlog)))
  save();need(proc.returncode==0 and not timed and interrupted is None,'Replay failed: '+label)
 def runtime_result(name,status):
  p=work/name;r=load(p)
  need(r['status']==status and r['complete'] and r['source_leaves']==6459 and r['expected_cases']==8390 and r['counts']['cases']==8390,'Runtime coverage incomplete.')
  need(r['frame_padding']==64 and r['arbitrary_primary_registers'] and r['arbitrary_nonempty_finite_spare_suffix'] and r['positive_progress_checked'],'Runtime frame scope changed.')
  need(r['table_sha256']==DATA['zfc_combined243_old.tm'][1] and r['sites_logical_sha256']==DATA['sites_logical.json'][1],'Runtime inputs changed.')
  sites=load(work/'sites_logical.json' if name.startswith('expanded')else work/'sites_physical.json')
  expected=[(i,p,op,k,z)for i,(p,op,k)in enumerate(sites)for z in ([True,False]if op=='CD'else[None])]
  need([(c['index'],c['pc'],c['op'],c['r'],c['zero'])for c in r['cases']]==expected,'Runtime case order/branches changed.')
  key='time_lower_bound'if name.startswith('expanded')else'minimum_literal_steps'
  need(all(c[key]>0 for c in r['cases']),'Nonpositive runtime block.')
  if name.startswith('expanded'):need(r['literal_rows_covered']==485 and r['unused_rows']==[[27,1]],'Unexpected expanded literal-row coverage.')
  return desc(p)
 try:
  blank=output/'blank'
  run('blank',[code/'check_combined243_blank.py','--table',work/'machine_old.tm','--baseline',ref/'certificate/machine_old.tm','--reference',ref,'--output',blank],120)
  br=load(blank/'independent-blank.json')
  need(br['status']=='PASS_INDEPENDENT_243_TABLE_AND_BLANK_PREFIX' and br['working_states']==243 and br['transitions']==486,'Blank/table check failed.')
  need(br['table_sha256']==DATA['zfc_combined243.tm'][1] and br['old_table_sha256']==DATA['zfc_combined243_old.tm'][1],'Blank table identity.')
  need(br['sparse_dense_exact_agreement_both_numberings'] and br['all_other_cells_zero'] and br['one_count']==351 and 0<br['blank_steps']<=3000000,'Blank whole tape incomplete.')
  run('affine',[code/'check_runtime_combined243.py','--reference',ref,'--candidate',work],120)
  affine=runtime_result('affine-runtime.json','PASS_UNIVERSAL_AFFINE_RUNTIME')
  run('literal',[code/'check_combined243_literal.py','--candidate',work],120)
  lr=load(work/'literal-regression.json')
  need(lr['status']=='PASS_FINITE_LITERAL_REGRESSION' and lr['cases']==8390 and lr['source_leaves']==6459 and lr['working_states']==243,'Literal coverage incomplete.')
  need(lr['table_sha256']==DATA['zfc_combined243_old.tm'][1] and lr['source_sha256']==DATA['sites_logical.json'][1] and lr['whole_tape_endpoints_checked'] and lr['literal_steps']>0,'Literal binding/scope changed.')
  results=dict(blank=desc(blank/'independent-blank.json'),affine=affine,literal=desc(work/'literal-regression.json'),literal_cases=desc(work/'literal-regression-cases.json.gz'))
  if a.expanded:
   run('expanded',[code/'check_runtime_combined243.py','--reference',ref,'--candidate',work,'--expanded'],600)
   results['expanded']=runtime_result('expanded-runtime.json','PASS_UNIVERSAL_EXPANDED_RUNTIME')
  post();record.update(status='PASS_COMBINED243_REPRODUCTION_WITH_EXPANDED'if a.expanded else'PASS_COMBINED243_QUICK_REPRODUCTION',results=results,blank_steps=br['blank_steps'],literal_steps=lr['literal_steps'],cases=8390,
   scope='Exact blank initialization plus finite literal fixtures and affine replay; optional expanded whole-frame symbolic replay is recorded separately. This helper does not prove source-loop equivalence or a Lean/PA endpoint.')
 except BaseException as ex:
  record.update(status='FAIL',error=repr(ex))
  try:post()
  except BaseException as px:record['postcheck_error']=repr(px)
  save();raise
 save();print(json.dumps(dict(status=record['status'],verification=desc(output/'verification.json')),indent=2))
if __name__=='__main__':main()
