#!/usr/bin/env python3
"""Replay bounded PA194QHS pair screens and failed runtime193 startup screens.

Python 3.10+ and a C++17 compiler are required. This program reconstructs no
consistency theorem and makes no claim that 194 states are minimal.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,tempfile

HERE=Path(__file__).resolve().parent

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args):
 r=subprocess.run([str(x)for x in args],text=True,capture_output=True)
 if r.returncode:raise RuntimeError(f'Command failed: {args[0]}\n{r.stderr[-4000:]}')
 return r

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--dense',type=Path,required=True,help='Delivered PA194QHS dense table')
 p.add_argument('--native',type=Path,required=True,help='Delivered PA194QHS native table')
 p.add_argument('--compiler',default='g++')
 p.add_argument('--skip-startup',action='store_true',help='Omit the two runtime193 startup searches')
 a=p.parse_args();receipt=json.loads((HERE/'reduction_search_receipt.json').read_text());expected=receipt['qhs_pair_screen']
 if digest(a.dense)!=expected['dense_sha256']or digest(a.native)!=expected['native_sha256']:raise ValueError('Unexpected QHS table bytes')
 if digest(HERE/'qhs_source_startup_contexts.txt')!=expected['contexts_sha256']:raise ValueError('Unexpected context bytes')
 output={}
 with tempfile.TemporaryDirectory(prefix='qhs-reduction-replay-')as tmp:
  tmp=Path(tmp);action=tmp/'action_merge';startup=tmp/'search_startup_pairs_all'
  run([a.compiler,'-O3','-std=c++17',HERE/'action_merge.cpp','-o',action])
  for name,args in [('blank_radius8',[a.dense,8,300,'-',0]),('source_startup_radius6',[a.native,6,300,HERE/'qhs_source_startup_contexts.txt',74])]:
   r=run([action,*args]);lines=r.stdout.strip().splitlines()if r.stdout.strip()else[]
   if lines:raise RuntimeError(f'Unexpected candidate in {name}: {lines[:2]}')
   output[name]={'candidate_merges':0}
  if not a.skip_startup:
   run([a.compiler,'-O3','-std=c++17',HERE/'search_startup_pairs_all.cpp','-o',startup])
   for mode,table in [('append1','runtime193.native.tm'),('append0','runtime193_append0.native.tm')]:
    r=run([startup,HERE/table,HERE/'pair_edits.tsv',200000,0,1000,HERE/'startup_any_frame_templates.tsv'])
    if r.stdout.strip():raise RuntimeError(f'Unexpected startup: {r.stdout[:500]}')
    terminal=r.stderr.strip().splitlines()[-1]
    m=re.search(r'simulations (\d+) ticks (\d+) halts (\d+) rays (\d+) limits (\d+)',terminal)
    if not m:raise ValueError('No complete startup receipt')
    found=dict(zip(['normalized_onebit_runs','literal_transitions','halts','outward_rays','bounded_runs'],map(int,m.groups())))
    expected=receipt['runtime193_two_edit_startup'][mode]
    if any(found[k]!=expected[k]for k in found):raise ValueError(f'Startup receipt mismatch: {mode}: {found}')
    found['frames']=0;output[mode]=found
 print(json.dumps(output,indent=2))
if __name__=='__main__':main()
