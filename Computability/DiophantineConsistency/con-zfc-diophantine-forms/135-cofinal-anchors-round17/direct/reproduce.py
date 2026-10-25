#!/usr/bin/env python3
"""Deterministically rebuild the three selected direct endpoints in isolation."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile
HERE=Path(__file__).resolve().parent
COMMON=['--strong-cap','--odd-frame','--odd-comparison','--cofinal','--self-radix','--semantic-anchor','--signed-center','--odd-auxiliary','--squared-anchor','--orientation-first','--strict-budget']
VARIANTS=[('strict_dimension',[]),('strict_grouped',['--separate-sign-pool','--pool-width','5']),('strict_sparse',['--sparse'])]
def need(b,m):
 if not b:raise ValueError(m)
def run(args):
 p=subprocess.run([sys.executable,*(['-O'] if sys.flags.optimize else []),*map(str,args)],cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 need(p.returncode==0,p.stdout)
 return p.stdout
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args();results={}
 with tempfile.TemporaryDirectory(prefix='conzfc_direct_round17_') as tmp:
  tmp=Path(tmp)
  for name,extra in VARIANTS:
   out=tmp/name;end=tmp/(name+'_centered')
   run([HERE/'build_cap.py',HERE/'portable_input',out,*COMMON,*extra])
   run([HERE/'center_integer.py',out,end])
   count=0
   for fresh,old in [(out,HERE/name),(end,HERE/(name+'_centered'))]:
    want=sorted(p.name for p in old.glob('*.json'));need(want==sorted(p.name for p in fresh.glob('*.json')),'file census mismatch')
    for fn in want:need((fresh/fn).read_bytes()==(old/fn).read_bytes(),'byte mismatch: '+name+'/'+fn);count+=1
   result=json.loads(run([HERE/'check_compiled_cap.py',out,'--centered',end]))
   results[name]={'identical_json_files':count,'checker_status':result['status'],'equation_sha256':hashlib.sha256((end/'equation.json').read_bytes()).hexdigest()}
 output={'status':'passed','optimized':bool(sys.flags.optimize),'variants':results}
 if args.output:args.output.write_text(json.dumps(output,indent=2)+'\n')
 print(json.dumps(output,indent=2))
if __name__=='__main__':main()
