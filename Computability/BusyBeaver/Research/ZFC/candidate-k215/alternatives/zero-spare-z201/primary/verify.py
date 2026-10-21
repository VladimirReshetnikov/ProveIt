#!/usr/bin/env python3
"""Portable finite audits; --full-runtime OUT reruns quantified induction."""
import sys
if not __debug__: raise SystemExit("Run without -O: assertions are required for verification.")
from pathlib import Path
import argparse,gzip,json,hashlib,subprocess,sys,tempfile
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--full-runtime',type=Path);a=ap.parse_args()
 manifest=json.loads((P/'MANIFEST.json').read_text())
 for name,digest in manifest.items():assert sha(P/name)==digest,name
 F=P/'inherited/research/command_family'
 with tempfile.TemporaryDirectory()as tmp:
  out=Path(tmp)/'reconstructed'
  subprocess.run([sys.executable,'-B',str(F/'reconstruct_family.py'),'--name','201','--out',str(out)],check=True)
  assert(out/'sites.json').read_bytes()==(P/'sites.json').read_bytes()
  raw=(out/'candidate.native.tm').read_text();assert raw.count('198 0 1 L 40')==1
  raw=raw.replace('198 0 1 L 40','198 0 0 L 40').replace('#! start 0','#! start 74')
  assert raw==(P/'z201.native.tm').read_text()
 for script in('audit201.py','audit_source201.py','independent_review/check_discharge.py'):subprocess.run([sys.executable,'-B',str(P/script)],check=True)
 r=json.loads((P/'runtime/runtime.json').read_text());ss=json.loads((P/'sites.json').read_text());cases=json.loads(gzip.decompress((P/'runtime/runtime_cases.json.gz').read_bytes()))
 assert r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['expected_cases']==r['proved_cases']==6176 and not r['failures']
 assert r['table_sha256']==sha(P/'z201.native.tm')and r['source_sha256']==sha(P/'sites.json')
 assert r['wrapper_sha256']==sha(P/'runtime/original_wrapper.py')
 assert r['checker_sha256']==sha(P/'inherited/baseline/code/runtime-inputs/runtime/symbolic_runtime.py')
 assert r['helper_sha256']==sha(P/'inherited/baseline/code/runtime-inputs/runtime/independent_runtime.py')
 assert[(c['site_index'],c['positive'])for c in cases]==[(i,b)for i,(_,op,k)in enumerate(ss)for b in((False,True)if op=='CD'else(False,))]
 assert all(len(c['duration'])==13 and c['duration'][0]>0 and all(type(x)is int and x>=0 for x in c['duration'])for c in cases)
 assert sum(c['symbolic_steps']for c in cases)==r['symbolic_steps']
 T={tuple(map(int,l.split()[:2]))for l in(P/'z201.native.tm').read_text().splitlines()if l and not l.startswith('#')}
 assert set(map(tuple,r['native_rows_covered_including_blocks']))==T and len(T)==430
 if a.full_runtime:
  out=a.full_runtime.resolve();assert not out.exists()
  subprocess.run([sys.executable,'-B',str(P/'verify201.py'),'--base',str(P/'inherited/baseline'),'--out',str(out)],check=True)
  for f in('runtime_cases.json.gz','startup.json.gz'):assert gzip.decompress((out/f).read_bytes())==gzip.decompress((P/'runtime'/f).read_bytes())
 print('PASS: pinned files, reconstruction, full native/dense safe bootstrap, source discharge, graph nonisomorphism, ordered quantified-case receipts, positive durations and complete row coverage.')
if __name__=='__main__':main()
