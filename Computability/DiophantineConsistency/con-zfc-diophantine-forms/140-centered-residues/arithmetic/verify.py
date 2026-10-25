#!/usr/bin/env python3
"""Portable integrated exact replay, with optional byte-exact reconstruction."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
import verify_signed as S
import verify_natural as N

PROFILES=[
 ('signed258','build_signed_radius.py',['--odd-square','--weighted']),
 ('signed259','build_signed_radius.py',['--odd-square']),
 ('audit261','build_signed_radius.py',[]),
 ('natural222','build.py',[]),
 ('natural221_high','build.py',['--source-priority','--support-cap','64']),
 ('natural223_sparse','build.py',['--support-cap','24']),
]
def need(b,msg):
 if not b:raise ValueError(msg)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args()
 provenance=json.loads((HERE/'PROVENANCE.json').read_text())
 for item in provenance['files']:
  p=HERE/item['path'];need(p.is_file(),'missing retained source '+item['path'])
  data=p.read_bytes();need(len(data)==item['bytes']and hashlib.sha256(data).hexdigest()==item['sha256'],'retained source identity '+item['path'])
 results=[]
 for name,builder,options in PROFILES:
  results.append((S.check_endpoint if builder=='build_signed_radius.py'else N.check_endpoint)(HERE/name,True))
 rebuilt=[]
 if a.rebuild:
  with tempfile.TemporaryDirectory(prefix='conzfc_radius_rebuild_')as temp:
   for name,builder,options in PROFILES:
    out=Path(temp)/name
    command=[sys.executable,'-B',*(['-O']if sys.flags.optimize else []),str(HERE/builder),'--output',str(out),*options]
    run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    need(run.returncode==0,run.stdout)
    new=sorted(p.name for p in out.glob('*.json'));old=sorted(p.name for p in (HERE/name).glob('*.json'))
    need(new==old,'generated file census '+name)
    for file in new:need((out/file).read_bytes()==(HERE/name/file).read_bytes(),'rebuild byte mismatch '+name+'/'+file)
    rebuilt.append(dict(profile=name,identical_json_files=len(new)))
 out=dict(status='PASS',optimized=bool(sys.flags.optimize),authenticated_source_files=len(provenance['files']),endpoints=results,rebuilds=rebuilt,
          proof_boundary='Finite exact algebra and artifact binding only; unbounded arithmetic and inherited logical calibration are in the ordinary proofs.')
 if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
