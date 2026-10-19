#!/usr/bin/env python3
"""Recover pinned source dependencies into a new scratch copy, without network."""
from pathlib import Path
import argparse,json,shutil,subprocess
PIN='7ba1598461c6e485c5aeb8f673c0b1d571f8012b'
p=argparse.ArgumentParser();p.add_argument('--upstream',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
u=a.upstream.resolve();out=a.output.resolve();base=Path(__file__).resolve().parent
head=subprocess.check_output(['git','-C',str(u),'rev-parse','HEAD'],text=True).strip()
if head!=PIN:raise SystemExit('Refusing mismatched upstream HEAD: '+head)
if out.exists():raise SystemExit('Output must not exist; choose a fresh scratch directory')
shutil.copytree(base/'research_sub246',out/'research_sub246');src=out/'research_sub246/source';shutil.rmtree(src);src.symlink_to(u,target_is_directory=True)
prefix='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/'
def blob(path):return subprocess.check_output(['git','-C',str(u),'show',PIN+':'+path])
count=0
for batch,ids in [(162,{63}),(163,{64,65,66,67})]:
 placement=json.loads(blob(prefix+f'data/intake-{batch}-placement.json'))
 for item in placement['placements']:
  if item['local_source'] not in ids:continue
  dest=(out/'research_sub246/context_folds/recovered'/str(item['local_source'])/item['delivered']).resolve()
  if not dest.is_relative_to(out):raise SystemExit('Unsafe recovered path')
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob(item['target']));count+=1
print('Prepared',out,'with',count,'pinned recovered files. Upstream was not modified.')
