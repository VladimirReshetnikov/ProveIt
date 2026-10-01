"""Recompute all68 GMP enclosure certificates and compare every trace entry."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import subprocess,json,gzip
ROOT=Path(__file__).resolve().parents[1];BUILD=ROOT/'build'/'reproduce';BUILD.mkdir(parents=True,exist_ok=True)
exe=BUILD/'check_boundary_parity'
subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'code'/'check_boundary_parity.cpp'),'-lgmpxx','-lgmp','-o',str(exe)],check=True)
def one(m):
 p=BUILD/f'parity_m{m:03d}.json';subprocess.run([str(exe),str(m),str(p)],check=True)
 ref=ROOT/'data'/'certificates'/p.name
 actual=json.loads(p.read_text());expected=json.loads(ref.read_text())
 for k,v in expected.items():
  if k!='elapsed_seconds':assert actual[k]==v,(m,k)
 with gzip.open(str(ref)+'.trace.gz','rb')as f:old=f.read()
 assert Path(str(p)+'.trace').read_bytes()==old,m
 return m
with ThreadPoolExecutor(max_workers=2)as pool:
 for f in as_completed([pool.submit(one,m)for m in range(69,1,-1)]):print('Reproduced complete certificate',f.result(),flush=True)
print('All68 complete matrix enclosures and every saved trace entry reproduced exactly')
