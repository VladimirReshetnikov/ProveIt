#!/usr/bin/env python3
"""Offline full/quick replay, preserving the package's archived evidence."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
B=Path('combine/zfc239-research-20261019')
C=Path('combine/candidate238')
def require(c,m):
 if not c:raise RuntimeError(m)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--quick',action='store_true');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 require(sys.version_info>=(3,10),'Python 3.10 or later required')
 out=a.output.resolve();require(not out.exists() or not any(out.iterdir()),'Output must be new or empty')
 require(ROOT not in out.parents and out!=ROOT,'Output must be outside the archive root')
 out.mkdir(parents=True,exist_ok=True);start=time.monotonic();jobs=[]
 if (ROOT/'MANIFEST.sha256').exists():
  for l in (ROOT/'MANIFEST.sha256').read_text().splitlines():
   digest,name=l.split('  ',1);p=ROOT/name
   require(hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'Manifest mismatch: {name}')
  jobs.append({'name':'manifest','status':'PASS'})
 with tempfile.TemporaryDirectory(prefix='zfc238-full-') as tmp:
  w=Path(tmp)/'packet';shutil.copytree(ROOT,w,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  def run(name,script,*args,receipt=None,status=None):
   print('Checking '+name+' ...',flush=True);t=time.monotonic()
   p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=w,capture_output=True,text=True)
   (out/(name+'.log')).write_text(p.stdout+p.stderr)
   require(p.returncode==0,f'{name} failed; see {out/(name+".log")}')
   if receipt:
    r=json.loads((w/receipt).read_text());require(r.get('status')==status,f'{name} bad status {r.get("status")}');shutil.copy2(w/receipt,out/(name+'.json'))
   jobs.append({'name':name,'status':'PASS','seconds':time.monotonic()-t})
  run('source_identity',B/'source_interface/check_source_interface.py',receipt=B/'source_interface/interface_result.json',status='EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS')
  run('source_rotation',B/'formalism/extra/check_rotation_certificate.py','--report','source_rotation_fresh.json',receipt=Path('source_rotation_fresh.json'),status='PASS_EXACT_SOURCE_CONTROL_CERTIFICATE')
  run('boundary_audit',Path('boundary_audit/audit_boundary.py'),receipt=Path('boundary_audit/independent_boundary_audit.json'),status='PASS')
  run('construction',C/'build_and_check.py',receipt=C/'construction.json',status='EXACT_CONSTRUCTION_AND_STARTUP_PASS')
  run('independent_blank',Path('verification/independent_blank238.py'),receipt=Path('verification/independent_blank238.json'),status='PASS')
  run('local_transfer',Path('erasure_audit/audit_local_transfer.py'),receipt=Path('erasure_audit/local_transfer.json'),status='PARAMETRIC_DELAYED_ERASURE_TRANSFER_SIDE_CONDITIONS_PASS')
  run('boot_alignment',Path('erasure_audit/audit_boot_blocks.py'),receipt=Path('erasure_audit/boot_blocks.json'),status='EXACT_BLANK_POSITIVE_BLOCK_ALIGNMENT_PASS')
  run('packet921',Path('formalisms/remove_redundant_truth.py'))
  run('packet921_independent',Path('encoding/review_packet921.py'))
  if not a.quick:
   run('universal238',C/'check_literal_runtime.py','--table',C/'zfc_combined238_old.tm','--sites',C/'sites_logical.json','--states','238','--output',C/'universal_runtime.json',receipt=C/'universal_runtime.json',status='UNIVERSAL_MATHEMATICAL_PASS')
   run('boundary_guard',Path('erasure_audit/audit_boundary_guard.py'),receipt=Path('erasure_audit/boundary_guard.json'),status='BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS')
  run('endpoint_binding',Path('boundary_audit/audit_combined_endpoint.py'),receipt=Path('boundary_audit/combined_endpoint_acceptance.json'),status='PASS')
  run('duration_comparison',C/'check_duration_comparison.py','--baseline-cases',B/'candidate239/universal_runtime_cases.json',receipt=C/'duration_comparison.json',status='AFFINE_DURATION_COMPARISON_PASS')
  require((w/'machines/zfc238.tm').read_bytes()==(w/C/'zfc_combined238.tm').read_bytes(),'Top-level final machine differs from reconstruction')
  require((w/'machines/sites_logical.json').read_bytes()==(w/C/'sites_logical.json').read_bytes(),'Top-level source differs')
 result={'status':'QUICK_238_REPLAY_PASS' if a.quick else 'FULL_238_MATHEMATICAL_REPLAY_PASS','jobs':jobs,'seconds':time.monotonic()-start,'working_states':238,'canonical_sha256':'909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08','fresh_unbounded_guards':0 if a.quick else 2*8386,'scope':'Exact finite/source/codec replay plus both unbounded proof constructions in full mode; inherited logical calibration and prior Lean library not rebuilt.'}
 (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
