#!/usr/bin/env python3
"""Replay the optional arithmetic-context reduction experiment."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time

HERE=Path(__file__).resolve().parent
NATIVE_SHA='bdbfb392b408dd729899f07ad38de92b86f5d76bbdb87e7a12e5f1137f3d8047'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--package',type=Path,default=HERE.parents[1])
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--reuse-contexts',action='store_true')
 a=ap.parse_args();out=a.output.resolve();assert out!=HERE.resolve()
 out.mkdir(parents=True,exist_ok=True)
 machine=a.package.resolve()/'machines/PA194LCG'
 ref=a.package.resolve()/'verification/reference'
 assert sha(machine/'machine.native.tm')==NATIVE_SHA
 manifest=json.loads((HERE/'MANIFEST.json').read_text())
 for name,digest in manifest.items():assert sha(HERE/name)==digest,name
 commands=[]
 def run(argv,name):
  argv=list(map(str,argv));commands.append(argv)
  with (out/name).open('w') as f:subprocess.run(argv,check=True,stdout=f,stderr=subprocess.STDOUT)
 contexts=out/'literal_contexts.tsv';started=time.time()
 if a.reuse_contexts:
  shutil.copyfile(HERE/'LCFC_literal_contexts_k6.tsv',contexts)
 else:
  run([sys.executable,'-B',HERE/'collect_literal_contexts.py',machine,ref,contexts,'--radius','6'],'envelope.log')
 assert sha(contexts)==manifest['LCFC_literal_contexts_k6.tsv']
 run([sys.executable,'-B',HERE/'check_context_samples.py',machine,contexts,'--radius','6','--samples','1200'],'samples.json')
 sample=json.loads((out/'samples.json').read_text());assert sample['missing_windows']==0 and sample['literal_steps']==551331
 for program in ['joint_return_merge','stutter_merge_contexts','edge_delete_contexts']:
  run(['g++','-O3','-std=c++17',HERE/(program+'.cpp'),'-o',out/program],program+'_compile.log')
 table=machine/'machine.native.tm'
 specs=[('joint_return_merge',[table,6,100,contexts]),
        ('stutter_merge_contexts',[table,6,12,128,74,contexts]),
        ('edge_delete_contexts',[table,6,256,74,24,contexts])]
 results=[]
 for program,args in specs:
  argv=list(map(str,[out/program,*args]));commands.append(argv)
  with (out/(program+'_hits.jsonl')).open('w') as hit,(out/(program+'.log')).open('w') as log:
   subprocess.run(argv,check=True,stdout=hit,stderr=log)
  lines=[x for x in (out/(program+'_hits.jsonl')).read_text().splitlines() if x.strip()]
  assert not lines,(program,'unexpected search result',lines)
  results.append({'program':program,'hits':len(lines)})
 log=(out/'edge_delete_contexts.log').read_text().splitlines()
 assert len([x for x in log if x.startswith('Q ')])==193
 receipt={'status':'PASS','machine':'PA194LCG','native_sha256':NATIVE_SHA,
          'envelope_regenerated':not a.reuse_contexts,'literal_windows':49297,
          'sample_check':sample,'searches':results,'commands':commands,
          'elapsed_seconds':time.time()-started,
          'scope':'Finite optimization templates only; no global state lower bound or absolute iPRA calibration.'}
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
