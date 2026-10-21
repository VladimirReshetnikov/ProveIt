#!/usr/bin/env python3
"""Portable data/runtime checks, not a Lean or Rocq kernel endpoint."""
import argparse,hashlib,json,sys,subprocess,shutil
from pathlib import Path
if not __debug__:raise SystemExit('Run without -O or -OO; assertions are part of checks.')
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--runtime',action='store_true');a=ap.parse_args();W=a.work.resolve()
assert not W.exists() and P not in W.parents
W.mkdir(parents=True)
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if (P/'MANIFEST.json').exists():
 for name,v in json.loads((P/'MANIFEST.json').read_text()).items():
  assert H(P/name)==v['sha256'] and (P/name).stat().st_size==v['bytes'],name
shutil.copytree(P/'proof_refactor',W/'proof_refactor')
subprocess.run([sys.executable,'-B',str(W/'proof_refactor/audit_compression.py')],check=True,stdout=(W/'compression.log').open('w'))
assert (W/'proof_refactor/Cert215Compact.v').read_bytes()==(P/'proof_refactor/Cert215Compact.v').read_bytes()
assert json.loads((W/'proof_refactor/METRICS.json').read_text())==json.loads((P/'proof_refactor/METRICS.json').read_text())
r=subprocess.run([sys.executable,'-B',str(P/'prefix_credit/check_codec.py')],check=True,capture_output=True,text=True)
credit=json.loads(r.stdout);assert credit==json.loads((P/'prefix_credit/finite_check.json').read_text())
(W/'prefix_credit.json').write_text(r.stdout)
sys.path.insert(0,str(P/'checks'));import independent_runtime as I
T=I.table(P/'hybrid215/machine.native.tm');sites=json.loads((P/'hybrid215/source.sites.json').read_text());receipt=json.loads((P/'hybrid215/GC_ZC215_RUNTIME.json').read_text())
assert H(P/'hybrid215/runtime_input.reference.tm')==receipt['table_sha256']
assert (P/'hybrid215/machine.native.tm').read_text().splitlines()[0]=='#! start 74'
assert (P/'hybrid215/machine.native.tm').read_text().splitlines()[1:]==(P/'hybrid215/runtime_input.reference.tm').read_text().splitlines()[1:]
subprocess.run([sys.executable,'-B',str(P/'hybrid215/verify_composition.py'),'--source',str(P/'hybrid215/source.sites.json'),'--table',str(P/'hybrid215/machine.native.tm'),'--output',str(W/'composition.json')],check=True,stdout=(W/'composition.log').open('w'))
assert H(P/'hybrid215/source.sites.json')==receipt['source_sha256']
assert len(T)==430 and len({q for q,b in T})==215
mapping=json.loads((P/'hybrid215/GC_ZC215_CANONICAL.json').read_text())['native_to_canonical'];M={int(q):v for q,v in mapping.items()}
C=I.table(P/'hybrid215/gc_zc215.canonical.tm');assert len(set(M.values()))==len(M)
assert {(M[q],b):(w,d,M[n]) for(q,b),(w,d,n)in T.items()}==C
root=json.loads((P/'hybrid215/GC_ZC215_BLANK_ROOT.json').read_text());ones=set();q=74;h=0;cd=0;hd=0;dense=bytearray(400001);lo=-200000
for i in range(root['steps']):
 w,d,n=T[q,int(h in ones)];wc,dc,nc=C[cd,dense[hd-lo]];assert(w,d,M[n])==(wc,dc,nc)
 dense[hd-lo]=wc;hd+=dc;cd=nc
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=n
assert q==root['state'] and h==root['head'] and sorted(ones)==root['ones']
assert hd==h and cd==M[q] and ones=={i+lo for i,b in enumerate(dense) if b}
assert root['pc']==sites[0][0] and root['registers']==[1,0,5,0,0,0,0,0,0]
assert ones=={x+h for x in I.frame(root['pc'],root['registers'],root['spares'],root['gap'])}
assert root['spares'] and root['spares'][-1]==0
runtime=None
if a.runtime:
 import symbolic_runtime as S
 L={int(k):v for k,v in json.loads((P/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()}
 for z in sorted({q for q,b in T}|{n for w,d,n in T.values()}):
  if z not in L:L[z]=max(L.values())+1
 U={(L[q],b):(w,d,L[n])for(q,b),(w,d,n)in T.items()};lemmas,blocks=S.prove_blocks(U);cases=[];rows=set()
 for i,site in enumerate(sites):
  for pos in ((False,True) if site[1]=='CD' else (False,)):
   c=S.case(U,lemmas,site,pos,append=0);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=pos,**c))
 (W/'runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
 assert json.loads(json.dumps(cases))==json.loads((P/'hybrid215/GC_ZC215_RUNTIME_CASES.json').read_text())
 assert len(cases)==6177 and len(rows)==430
 assert sum(c['symbolic_steps'] for c in cases)==1698909
 runtime={'cases':len(cases),'symbolic_rules':1698909,'rows':len(rows)}
result={'status':'LISTED_CHECKS_PASS','kernel_compilation':'NOT PERFORMED','compression_rows':2240,'prefix_credit_finite_candidates':credit['candidate_count'],'blank_root_steps':root['steps'],'runtime':runtime,'scope':'Exact data equality, literal blank startup and optional all-natural symbolic runtime; written source/calibration arguments and uncompiled proof prototypes remain separate.'}
(W/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
