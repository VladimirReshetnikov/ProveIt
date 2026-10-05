from pathlib import Path
from functools import reduce
from math import gcd
import hashlib,json
ROOT=Path(__file__).resolve().parent;SOURCE=ROOT.parent;SNAP=SOURCE/'audit_snapshot'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
expected=json.loads((SNAP/'stable_expected.json').read_text());inputs=json.loads((SNAP/'SHA256.json').read_text())
for v in inputs:need(sha(SNAP/v['file'])==v['sha256'],('input changed',v['file']))
records=[];plain_entries=0;plain_cones=0
for e in expected['profiles']:
 core=e['core_columns'];tag='_'.join(map(str,core));p=ROOT/f'replay_{tag}.json';r=json.loads(p.read_text());need(r['passed'] and len(r['records'])==15,('incomplete',core));records.append({'core':core,'file':p.name,'sha256':sha(p),'base_sha256':r['base_sha256'],'repaired':r['repaired']})
 if not r['repaired']:
  plain_cones+=15;plain_entries+=sum(z['terms'] for z in r['records']);need(all(z['minimum']>=0 and z['negative']==0 for z in r['records']),('plain signs',core))
 else:
  rawpath=SOURCE/f'raw_{tag}_0.txt';raw={}
  with rawpath.open() as f:
   n=int(f.readline())
   for line in f:
    k,c=map(int,line.split());raw[tuple((k>>(6*j))&63 for j in range(7))]=c
  need(len(raw)==n,'raw count');content=reduce(gcd,(abs(v) for v in raw.values()),0) or 1
  h=hashlib.sha256(json.dumps([[list(x),v//content] for x,v in sorted(raw.items())],separators=(',',':')).encode()).hexdigest();need(h==r['base_sha256'],('Rayleigh full target linkage',core));records[-1]['primary_raw_sha256']=sha(rawpath)
need((plain_cones,plain_entries)==(960,43891306),'totals')
k=json.loads((ROOT/'kernel_results.json').read_text());ep=json.loads((ROOT/'endpoint_results.json').read_text());need(k['passed'] and k['kernels']==13,'kernels');need(ep['passed'] and ep['polynomial_identities']==592,'endpoints')
result={'all_passed':True,'scope':'Fresh independent support enumeration, exact inverse and centered-kernel verification, separately written sparse integer product, primitive normalization and simultaneous cone translations. Four Rayleigh profiles have complete independently reconstructed targets; their positive decompositions are verified separately. Six analytic profiles are outside this batch.','cores':68,'plain_cores':64,'plain_cones':plain_cones,'plain_nonnegative_coefficients':plain_entries,'rayleigh_target_cores':4,'rayleigh_target_cones':60,'exact_kernels':13,'endpoint_identities':592,'frozen_inputs_unchanged':len(inputs),'records':records,'source_hashes':{p.name:sha(p) for p in sorted(ROOT.glob('*.py'))}|{'independent_product.cpp':sha(ROOT/'independent_product.cpp')},'endpoint_results_sha256':sha(ROOT/'endpoint_results.json'),'kernel_results_sha256':sha(ROOT/'kernel_results.json'),'snapshot_manifest_sha256':sha(SNAP/'SHA256.json')}
(ROOT/'independent_manifest.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',68,'cores;',plain_cones,'plain cones;',plain_entries,'coefficients; 60 repaired targets;13 kernels;592 endpoint identities')
