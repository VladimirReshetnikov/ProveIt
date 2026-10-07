#!/usr/bin/env python3
"""Mandatory offline exact and interval replay in ordinary and optimized Python."""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import certificate_io as io

OUTPUTS=('exact_checks.json','interval_tests.json','guard_tests.json','certificate_receipt.json',
         'certificate/core.json','certificate/panels.json','certificate/panel_verification.json',
         'certificate/coefficient.json')

def run_script(root,script,args,optimized):
 command=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])
 command += [str(root/script),*map(str,args)]
 env={'PATH':os.defpath,'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC',
      'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
 completed=subprocess.run(command,cwd=root,env=env,capture_output=True,timeout=1800,shell=False)
 io.need(completed.returncode==0,script+' failed:\n'+(completed.stdout+completed.stderr)[-10000:].decode('utf-8',errors='replace'))
 io.need(not completed.stderr,script+' produced unexpected stderr')
 result=io.load_json(completed.stdout)
 io.need(type(result) is dict and result.get('status')=='PASS',script+' did not return PASS')
 data=io.canonical(result)
 io.need(data==completed.stdout,script+' output is not canonical JSON')
 return data

def run_mode(root,work,optimized):
 work.mkdir()
 guards=run_script(root,'test_guards.py',[],optimized);io.write_new(work/'guard_tests.json',guards)
 exact=run_script(root,'check_exact.py',['--output',work/'exact_checks.json'],optimized)
 io.need(exact==io.read_regular(work/'exact_checks.json'),'Exact stdout and file differ')
 interval=run_script(root,'test_intervals.py',[],optimized);io.write_new(work/'interval_tests.json',interval)
 certificate=run_script(root,'certificate.py',['--output-dir',work/'certificate'],optimized)
 io.write_new(work/'certificate_receipt.json',certificate)
 files,dirs=io.scan(work)
 io.need(set(files)==set(OUTPUTS) and dirs=={'certificate'},'Generated inventory mismatch')
 return {name:io.read_regular(files[name]) for name in OUTPUTS}

def run(output,root=ROOT):
 root=io.check_directory(root);output=io.checked_output(output,root)
 before=io.verify_source(root)
 with tempfile.TemporaryDirectory(prefix='report193-replay-',dir=output.parent) as temporary:
  work=Path(temporary)
  normal=run_mode(root,work/'normal',False)
  optimized=run_mode(root,work/'optimized',True)
  io.need(normal==optimized,'Ordinary and optimized results differ')
  io.need(io.snapshot(root)==before,'Source changed during mandatory replay')
  result={'status':'PASS','report':193,'standard_library_only':True,
          'network_required':False,'floating_diagnostics_run':False,
          'normal_and_optimized_byte_identical':True,
          'panel_count':562,'every_terminal_panel_recomputed_in_both_modes':True,
          'strict_negative_coefficient':True,
          'provenance_sha256':before[io.MANIFEST]['sha256'],
          'files':{name:{'bytes':len(data),'sha256':io.sha(data)} for name,data in sorted(normal.items())},
          'scope':'Exact finite checks and conditional interval certificate; analytic theorems are proved in Report193'}
  output.mkdir(exist_ok=False)
  for mode,values in [('normal',normal),('optimized',optimized)]:
   destination=output/mode;destination.mkdir();(destination/'certificate').mkdir()
   for name,data in values.items():io.write_new(destination/name,data)
  io.write_new(output/'RESULT.json',io.canonical(result))
 return result

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output-dir',type=Path,required=True,help='fresh directory outside code; parent must already exist')
 args=parser.parse_args()
 try:
  result=run(args.output_dir);sys.stdout.buffer.write(io.canonical(result));return 0
 except Exception as exc:
  sys.stderr.buffer.write(io.canonical({'status':'FAIL','error':str(exc)}));return 1

if __name__=='__main__':sys.exit(main())
