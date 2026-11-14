#!/usr/bin/env python3
"""Reproduce the exact unproved195-state scanner candidate and failed contracts.

The source list is bound to an independent path-derived CFG; the literal table
is reconstructed from the supplied196-state parent by exactly one redirect and
one state deletion. The finite trit closure is rederived and independently
audited. No failure below is claimed to disprove the actual blank-run property.
Requires Python3, NumPy, and a C++17 compiler. Assertions must remain enabled.
"""
from pathlib import Path
import importlib.util,json,sys,hashlib,subprocess,itertools
import numpy as np
import tempfile
BASE=Path(__file__).resolve().parent;ROOT=BASE.parent
OUT=BASE/'scanner195';OUT.mkdir(exist_ok=True)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
r=load('scanner_native_runtime',BASE/'inputs/native_symbolic_runtime.py');f=load('scanner_source',BASE/'fast_contexts.py')
assert hashlib.sha256((OUT/'reference196.native.tm').read_bytes()).hexdigest()=='18b587c4f68d5e4bee699703d65499976c149ca2fe53d4f846c3bee8ad612e56'
assert hashlib.sha256((OUT/'reference196.sites.json').read_bytes()).hexdigest()=='47d67dd8effbe4bad7f42d005306f7d1d8ab821058cf1632f4fd5a1dbdbc2e96'
source=json.loads((OUT/'reference196.sites.json').read_text());names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
raw=[[x['path'],names[x['op']],x['arg']]for x in source];ss,ii=f.program(raw)
assert [list(x)for x in ii]==[x['instruction']for x in source]
r.program=lambda:(ss,ii);rows={}
for ln in(OUT/'reference196.native.tm').read_text().splitlines():
 q,b,w,d,t=ln.split();rows[int(q),int(b)]=int(w),d=='R',int(t)
rows[23,0]=(0,False,75);del rows[34,0];del rows[34,1]
assert len(rows)==390 and all(t!=34 for w,d,t in rows.values())
(OUT/'candidate.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {t}\n'for(q,b),(w,d,t)in sorted(rows.items())))
(OUT/'sites.json').write_text(json.dumps(raw)+'\n')
labels=[74]+sorted({q for q,b in rows}-{74})+[254]
index={q:i for i,q in enumerate(labels)}
(OUT/'candidate.tm').write_text(''.join(f'{index[q]} {b} {w} {"R"if d else"L"} {index[t]}\n'for(q,b),(w,d,t)in sorted(rows.items(),key=lambda z:(index[z[0][0]],z[0][1]))))
(OUT/'labels.json').write_text(json.dumps(labels)+'\n')
reachable={74};todo=[74]
for q in todo:
 for bit in(0,1):
  target=rows[q,bit][2]
  if target!=254 and target not in reachable:reachable.add(target);todo.append(target)
assert len(reachable)==195

def seed_probe():
 # Concrete clean-frame counterexample, independently of blank reachability.
 def frame(site):
  tape={-1,48};tape.update(i for i,b in enumerate(raw[site][0])if b=='1');position=49
  for value in[0,0,0,0,0,0,2,0,0]+[1]*26:
   tape.update(range(position+1,position+value+2));position+=value+2
  return tape
 assert source[25]['instruction']==['dec',8,27,26]
 tape=frame(25);expected=frame(27);q=84;head=0
 for step in range(1,20001):
  write,direction,q=rows[q,int(head in tape)]
  (tape.add if write else tape.discard)(head);head+=1 if direction else-1
  if q==84 or q==254:break
 result={'scope':'Concrete clean-frame implementation-contract test. The modified machine is not claimed to reach this frame from blank. No blank-run consistency-property disproval follows.',
         'initial_source_site':25,'initial_logical_registers':[2]+[0]*8,'initial_spares':[1]*26,'initial_header_distance':48,
         'expected_source_site':27,'expected_path':raw[27][0],'expected_head':0,'first_return_steps':step,'state':q,'head':head,
         'tape_difference_cells':len(tape^expected),'actual_ones':sorted(tape),'expected_ones':sorted(expected),'matching_frame':q==84 and head==0 and tape==expected}
 assert step==118 and q==84 and head==0 and len(tape^expected)==43
 (OUT/'seed_frame_probe.json').write_text(json.dumps(result,indent=2)+'\n')
 return result
probe=seed_probe()
binding={'reference_native_sha256':hashlib.sha256((OUT/'reference196.native.tm').read_bytes()).hexdigest(),
         'reference_source_sha256':hashlib.sha256((OUT/'reference196.sites.json').read_bytes()).hexdigest(),
         'candidate_native_sha256':hashlib.sha256((OUT/'candidate.native.tm').read_bytes()).hexdigest(),
         'candidate_dense_sha256':hashlib.sha256((OUT/'candidate.tm').read_bytes()).hexdigest()}
failures=[];contracts=r.contracts()
for ct in contracts:
 if r.run(rows,ct) is None:failures.append([ct[0],ct[1]])
print('unrestricted_failures',failures,flush=True)
graph=[str(len(ii))]
for ins in ii:
 op=ins[0];code=0 if op=='halt' else 1 if op=='jump' else 2 if op=='inc' else 3
 graph.append(' '.join(map(str,(code,)+ins[1:])))
(OUT/'source_graph.txt').write_text('\n'.join(graph)+'\n')
with tempfile.TemporaryDirectory(prefix='scanner195_audit_') as temporary:
 executable=Path(temporary)/'joint_trits'
 subprocess.run(['g++','-O3','-std=c++17',str(BASE/'joint_trits.cpp'),'-o',str(executable)],check=True)
 audit=json.loads(subprocess.run([str(executable),str(OUT/'source_graph.txt'),str(OUT/'invariant.bin')],check=True,capture_output=True,text=True).stdout)
audit['graph_sha256']=hashlib.sha256((OUT/'source_graph.txt').read_bytes()).hexdigest();audit['bitset_sha256']=hashlib.sha256((OUT/'invariant.bin').read_bytes()).hexdigest();(OUT/'invariant_receipt.json').write_text(json.dumps(audit,indent=2)+'\n');print('invariant',audit,flush=True)
n=len(raw);bits=np.unpackbits(np.fromfile(OUT/'invariant.bin',dtype=np.uint8),bitorder='little')[:n*3**9].reshape(n,3**9);masks=np.zeros((n,9),dtype=np.uint8)
for j in range(9):masks[:,j]=bits.reshape(n,3**(8-j),3,3**j).any(axis=(1,3))@np.array([1,2,4],dtype=np.uint8)
(OUT/'marginals.json').write_text(json.dumps(masks.tolist())+'\n')
sys.path.insert(0,str(BASE/'inputs'));import symbolic_runtime as s
s.HEADER_BASE=48;legacy={int(k):v for k,v in json.loads((BASE/'inputs/legacy_mapping.json').read_text()).items()}
for q,b in rows:legacy.setdefault(q,q+1000)
legacy[254]=254;table={(legacy[q],b):(w,1 if d else-1,legacy[t])for(q,b),(w,d,t)in rows.items()};lemmas,blocks=s.prove_blocks(table);original=s.var
choices={1:((0,False),),2:((1,False),),3:((0,False),(1,False)),4:((2,True),),5:((0,False),(2,True)),6:((1,True),),7:((0,True),)}
results=[]
for site,branch in failures:
 op=raw[site][1];arg=raw[site][2];positive=op=='CD'and not branch[1];ms=list(map(int,masks[site]))
 if op=='CD':ms[arg]&=6 if positive else 1
 if not all(ms):results.append({'site':site,'branch':branch,'status':'excluded_by_global_trit_invariant'});continue
 for assignment in itertools.product(*(choices[m]for m in ms)):
  def cv(j):
   if j==11:return s.num(1)
   if not 2<=j<=10:return original(j)
   minimum,variable=assignment[j-2]
   if op=='CD'and positive and j-2==arg:minimum-=1
   return s.add(original(j),s.num(minimum))if variable else s.num(minimum)
  s.var=cv
  try:
   s.case(table,lemmas,raw[site],positive)
   results.append({'site':site,'branch':branch,'status':'restricted_affine_pass','assignment':assignment})
  except BaseException as ex:
   record={'site':site,'path':raw[site][0],'op':op,'arg':arg,'branch':branch,'trit_marginal_masks':ms,'affine_assignment':assignment,'status':'restricted_affine_failure','error':repr(ex),'scope':'Failure on a source-reachable abstract marginal overapproximation; not by itself a concrete blank-run counterexample.'};results.append(record)
   print('RESTRICTED_FAILURE',json.dumps(record),flush=True)
   (OUT/'check.json').write_text(json.dumps({**binding,'states':195,'transition_rows':390,'syntactically_reachable_working_states':len(reachable),'contracts':len(contracts),'unrestricted_failure_count':len(failures),'unrestricted_failures':failures,'results':results,'clean_seed_contract_probe':probe,'conclusion':'Unproved195-state candidate: fails the unrestricted and strengthened affine implementation certificates, and the concrete clean-seed first-return contract. Its actual blank-run consistency property is not disproved by these tests.'},indent=2)+'\n')
   sys.exit(0)
(OUT/'check.json').write_text(json.dumps({'states':195,'contracts':len(contracts),'unrestricted_failures':failures,'results':results,'conclusion':'All initially failing branches discharged by source invariant; full startup and all primitive contracts still required'},indent=2)+'\n')
print('ALL_RESTRICTED_CASES_PASS',flush=True)
