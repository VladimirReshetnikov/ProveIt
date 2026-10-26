#!/usr/bin/env python3
"""Verify all delivered equations and reproduce generated data in a temporary copy.

Python 3.10+ standard library only. No network, theorem search, or proof assistant
is used. Independent finite checkers establish the recorded algebraic claims;
unbounded arithmetic and the inherited logical calibration remain mathematical
proof dependencies. This entry point never modifies the delivered artifacts.
An optional --receipt is the only persistent write performed by this command.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
PROFILES=(
 'integer137_degree12','integer121_degree16','integer118_degree22',
 'integer111_degree32','integer106_degree38','integer104_degree64',
 'integer99_degree128','integer94_degree256','integer93_degree328',
 'integer89_degree32768','integer88_degree65540','integer87_degree8388612',
)

class VerificationFailure(Exception):
 pass

def require(condition,message):
 if not condition:raise VerificationFailure(message)

def file_digest(path):
 digest=hashlib.sha256()
 with path.open('rb') as stream:
  while True:
   chunk=stream.read(1024*1024)
   if not chunk:break
   digest.update(chunk)
 return digest.hexdigest()

def validate_receipt_path(path):
 if path is None:return
 require(path.suffix.lower()=='.json','Receipt output must be a JSON file with a .json suffix')
 if path.is_relative_to(ROOT):
  require(path.is_relative_to(ROOT/'verification'),
          'An in-package receipt must be under verification/; mathematical sources, equations, reports, and programs are protected')
 require(path!=ROOT/'verification','Receipt must name a JSON file, not a directory')

def manifest_audit(receipt_path):
 manifest=ROOT/'MANIFEST.sha256'
 if not manifest.exists():return {'status':'NOT_PRESENT','files_checked':0,'own_receipt_skipped':0}
 seen=set();checked=0;skipped=0
 for number,line in enumerate(manifest.read_text(encoding='utf-8').splitlines(),1):
  if not line.strip():continue
  match=re.fullmatch(r'([0-9a-fA-F]{64})[ \t]+\*?(.+)',line)
  require(match is not None,'Malformed manifest line '+str(number))
  expected,name=match.groups();relative=Path(name)
  require(not relative.is_absolute() and '..' not in relative.parts,'Unsafe manifest path '+name)
  path=(ROOT/relative).resolve()
  require(path.is_relative_to(ROOT),'Manifest path escapes package '+name)
  require(path not in seen,'Duplicate manifest path '+name);seen.add(path)
  # The chosen receipt is an output, not an input. Do not open or hash it.
  if receipt_path is not None and path==receipt_path:
   skipped+=1;continue
  require(path.is_file(),'Missing manifest file '+name)
  require(file_digest(path)==expected.lower(),'Manifest mismatch '+name);checked+=1
 return {'status':'PASS','files_checked':checked,'own_receipt_skipped':skipped}

def inventory_audit():
 expected={name+'.json' for name in PROFILES}
 for folder in ('certificates','equations'):
  actual={p.name for p in (ROOT/folder).glob('*.json')}
  require(actual==expected,'The '+folder+' inventory must contain exactly the twelve named projection profiles')
 for variant in ('all5','staged','paired'):
  for name in ('equation.json','certificate.json','metrics.json'):
   require((ROOT/'sources'/variant/name).is_file(),'Missing pooled source '+variant+'/'+name)
 return {'status':'PASS','projection_profiles':len(PROFILES),'pool_variants':3}

def python_command(script,*arguments):
 flags=['-B']
 if sys.flags.optimize:flags.append('-'+'O'*sys.flags.optimize)
 return [sys.executable,*flags,str(script),*map(str,arguments)]

def run_step(work,name,relative,*arguments):
 env=dict(os.environ)
 env['PYTHONDONTWRITEBYTECODE']='1'
 env['PYTHONOPTIMIZE']=str(sys.flags.optimize)
 command=python_command(work/relative,*arguments)
 result=subprocess.run(command,cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,check=False)
 if result.returncode:
  diagnostic=(result.stderr or result.stdout)[-5000:]
  raise VerificationFailure(name+' failed with exit '+str(result.returncode)+': '+diagnostic)
 try:payload=json.loads(result.stdout)
 except json.JSONDecodeError:payload={'console_lines':result.stdout.strip().splitlines()}
 if isinstance(payload,dict) and 'status' in payload:
  require(str(payload['status']).lower() in ('pass','passed'),name+' did not report success')
 return {'name':name,'status':'PASS','python_optimization':sys.flags.optimize,
         'stdout_sha256':hashlib.sha256(result.stdout.encode()).hexdigest(),'result':payload}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--receipt',type=Path,help='Write a fresh JSON receipt to this path; no receipt is written by default')
 args=parser.parse_args()
 receipt_path=args.receipt.expanduser().resolve() if args.receipt else None
 validate_receipt_path(receipt_path)
 inventory=inventory_audit();manifest=manifest_audit(receipt_path);steps=[]
 # A private disposable copy also contains checks whose legacy scripts write
 # local receipts. Explicitly omit the requested output receipt from this copy.
 def ignored(directory,names):
  answer=[]
  for name in names:
   path=Path(directory)/name
   if name=='__pycache__' or name.endswith('.pyc') or (receipt_path is not None and path.resolve()==receipt_path):answer.append(name)
  return answer
 with tempfile.TemporaryDirectory(prefix='conzfc-oriented-audit-') as temporary:
  work=Path(temporary)/'package';shutil.copytree(ROOT,work,ignore=ignored)
  steps.append(run_step(work,'pool_builder_exact_rebuild','code/build_pooling.py','--check'))
  require(steps[-1]['result']['files_compared']==9,'Pool builder did not check all nine files')
  steps.append(run_step(work,'independent_pooling','code/verify_pooling.py'))
  require(set(steps[-1]['result']['variants'])=={'all5','staged','paired'},'Pool verifier did not check all variants')
  steps.append(run_step(work,'parent_frame','code/check_parent_frame.py'))
  require(steps[-1]['result']['count']==17,'Parent frame did not cover all seventeen power requests')
  steps.append(run_step(work,'projection_builder_exact_rebuild','code/build_projections.py','--check'))
  require(len(steps[-1]['result']['profiles'])==len(PROFILES),'Projection builder did not check all profiles')
  steps.append(run_step(work,'independent_projections','code/verify_projections.py'))
  require({p['name'] for p in steps[-1]['result']['profiles']}==set(PROFILES),'Projection verifier did not check exactly the named profiles')
  steps.append(run_step(work,'arithmetic_fixtures','code/check_arithmetic.py'))
  steps.append(run_step(work,'article_builder_exact_rebuild','code/export_article.py','--check'))
  steps.append(run_step(work,'printed_article_exactness','code/check_article.py'))
  require(steps[-1]['result']['pivot_profiles_parsed']==len(PROFILES),'Article checker did not parse all profiles')
  # Rebuild compact constants and circuits, checking their original bytes.
  compact=work/'compact'
  generated=list((compact/'coefficients').glob('*'))+list((compact/'compact_equations').glob('*.json'))
  frozen={p.relative_to(work):p.read_bytes() for p in generated if p.is_file()}
  require(len(list((compact/'compact_equations').glob('*.json')))==3,'Expected three compact equations')
  steps.append(run_step(work,'compact_coefficient_rebuild','compact/reconstruct_coefficients.py'))
  steps.append(run_step(work,'compact_circuit_rebuild','compact/build_compact.py'))
  for path,data in frozen.items():
   require((work/path).read_bytes()==data,'Compact rebuild differs: '+path.as_posix())
  steps.append(run_step(work,'compact_builder_exact_check','compact/build_compact.py','--check'))
  steps.append(run_step(work,'independent_compact_equations','compact/verify_compact.py'))
  require(len(steps[-1]['result']['equations'])==3,'Compact verifier did not check all three equations')
 receipt={'status':'PASS','schema':'conzfc-oriented-release-verification-v1',
          'python_optimization':sys.flags.optimize,'inventory':inventory,'manifest':manifest,
          'temporary_copy_used':True,'steps':steps,
          'scope':'Independent finite algebra, exact degrees, literal coefficients, article parsing, and deterministic reconstruction. Unbounded arithmetic and the inherited refutation calibration remain separate mathematical proof dependencies.'}
 if receipt_path is not None:
  receipt_path.parent.mkdir(parents=True,exist_ok=True)
  receipt_path.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n',encoding='utf-8')
 projection=next(s['result'] for s in steps if s['name']=='independent_projections')
 print(json.dumps({'status':'PASS','projection_profiles':len(PROFILES),'pool_variants':3,
                   'parent_power_requests':17,'compact_equations':3,'successful_steps':len(steps),
                   'python_optimization':sys.flags.optimize,'manifest':manifest,
                   'projection_corruptions_rejected':projection['rejected_corruptions'],
                   'nonzero_modular_derivative_witnesses':projection['nonzero_modular_derivative_witnesses'],
                   'temporary_copy_used':True,'receipt_written':receipt_path is not None},sort_keys=True))

if __name__=='__main__':
 try:main()
 except (VerificationFailure,OSError,ValueError,KeyError) as error:
  print(json.dumps({'status':'FAIL','error':str(error)},sort_keys=True),file=sys.stderr)
  raise SystemExit(1)
