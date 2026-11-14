#!/usr/bin/env python3
"""Replay selected newly authored searches. Negative answers are bounded only."""
from pathlib import Path
import subprocess,tempfile,json,argparse,re,hashlib
R=Path(__file__).resolve().parent

def need(c,m):
 if not c:raise RuntimeError(m)
def run(cmd):
 p=subprocess.run(list(map(str,cmd)),capture_output=True,text=True)
 need(p.returncode==0,'command failed: '+p.stdout[-4000:]+p.stderr[-4000:]);return p.stdout+p.stderr

def main():
 a=argparse.ArgumentParser();a.add_argument('--all',action='store_true');args=a.parse_args();out=[]
 with tempfile.TemporaryDirectory(prefix='u208-replay-')as d:
  d=Path(d)
  def exe(src,name):
   p=d/name;run(['c++','-O3','-std=c++17',R/src,'-o',p]);return p
  masks=exe('checks/original_source_masks.cpp','masks');s=run([masks,R/'checks/source_cfg.txt',d/'masks.txt'])
  need(json.loads(s)==json.loads((R/'evidence/source_masks_summary.json').read_text()),'abstract closure summary')
  need((d/'masks.txt').read_bytes()==(R/'evidence/source_masks.txt').read_bytes(),'all abstract masks')
  out.append({'check':'ternary source closure','abstract_states':4513459,'all_masks_equal':True})
  macro=exe('search/macro/macros.cpp','macro');s=run([macro,R/'search/macro/positive_control.dat','32'])
  need('HIT 1 -> 2 maxsteps 2,2' in s,'macro positive control');out.append({'check':'two-sided macro positive control','status':'PASS'})
  if args.all:
   jobs=[('coupled_all.cpp','4564c487.dat','trials 35307576 partial 88682 second 73428696 hits 0'),('coupled_all.cpp','89145587.dat','trials 35307576 partial 88196 second 73026288 hits 0'),('halt.cpp','4564c487.dat','trials 342784 partial 1010 second 840320 hits 0'),('halt.cpp','89145587.dat','trials 342784 partial 1010 second 840320 hits 0'),('repair.cpp','repair207.dat','first 341964 second 1554984 hits 0'),('repair3.cpp','repair207.dat','first 685584 second 54648 hits 0')]
   exes={}
   for src,inp,want in jobs:
    if src not in exes:exes[src]=exe('search/table/'+src,src[:-4])
    s=run([exes[src],R/'search/table'/inp]);need('DONE '+want in s,'search count '+src+' '+inp);out.append({'check':src+' '+inp,'result':want})
   for name in ['89145587','4564c487']:
    s=run([macro,R/'search/macro'/f'{name}_12.dat','64']);need('DONE trials 42849 hits 0 'in s,'macro negative');out.append({'check':'macro '+name+' depth12 bound64','trials':42849,'hits':0})
 print(json.dumps({'status':'PASS','scope':'bounded searches only','checks':out},indent=2))
if __name__=='__main__':main()
