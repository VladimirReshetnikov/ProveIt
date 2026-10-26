#!/usr/bin/env python3
"""Authenticate sibling source, independently check seeds, projections and coefficients."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
import verify_seed_independent as S
ROOT=Path(__file__).resolve().parent
PROFILES=[('integer138_degree8','source/pell209_affine.json',False),('integer114_degree16','seeds/plain_22/equation.json',False),('integer113_degree16','seeds/joint_13_frame/equation.json',False),('control114_degree16','seeds/plain_13/equation.json',True)]
def need(b,msg):
 if not b:raise ValueError(msg)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--signed-component',type=Path);ap.add_argument('--skip-manifest',action='store_true');ap.add_argument('--deep',action='store_true');a=ap.parse_args();binding=json.loads((ROOT/'SOURCE_BINDING.json').read_text());signed=a.signed_component or ROOT/binding['ordinary_proof_component'];source=ROOT/binding['source'];need(hashlib.sha256(source.read_bytes()).hexdigest()==binding['sha256'],'source SHA256');need((signed/binding['equation_path']).read_bytes()==source.read_bytes(),'sibling signed source byte identity');need(hashlib.sha256((signed/binding['certificate_path']).read_bytes()).hexdigest()==binding['certificate_sha256'],'sibling signed source certificate');need((signed/binding['ordinary_proof_path']).is_file(),'signed ordinary proof present')
 if not a.skip_manifest:
  manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
  for p,h in manifest.items():
   rel=Path(p);need(not rel.is_absolute()and'..'not in rel.parts,'safe manifest path');need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==h,'manifest '+p)
 seeds=[S.check_seed(source,ROOT/'seeds'/name)for name in ['joint_13_frame','plain_13','plain_22']]
 command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[]);profiles=[]
 for name,src,control in PROFILES:
  argv=command+[str(ROOT/'verify_monic.py'),'--source',str(ROOT/src),'--profile',str(ROOT/'equations'/name)]+(['--residual-only']if control else[]);r=subprocess.run(argv,capture_output=True,text=True);need(r.returncode==0,r.stderr);profiles.append(json.loads(r.stdout))
 if a.deep:
  r=subprocess.run(command+[str(signed/'verify.py')],capture_output=True,text=True);need(r.returncode==0,r.stderr)
 print(json.dumps({'status':'PASS','source_sha256':binding['sha256'],'source_binding':'sibling signed/conservative209 verified byte-for-byte','optimized':bool(sys.flags.optimize),'seeds':seeds,'profiles':profiles,'deep_signed_replay':a.deep},indent=2,sort_keys=True))
if __name__=='__main__':main()
