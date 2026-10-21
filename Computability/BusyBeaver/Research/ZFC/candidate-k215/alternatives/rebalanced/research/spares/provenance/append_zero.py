from pathlib import Path
import sys,json,time,hashlib,importlib.util
BASE=Path('/workspace/scratch/1d1a80d76be0/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215')
sys.path.insert(0,str(BASE/'code/runtime-inputs/runtime'));import independent_runtime as r;import symbolic_runtime as s
m={int(k):int(v)for k,v in json.loads((BASE/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()}
T=r.table(BASE/'k215.native.tm');T[198,0]=(0,-1,40)
OUT=Path('/workspace/scratch/1d1a80d76be0/experiments/spares/append-zero');OUT.mkdir(exist_ok=True)
(OUT/'candidate.native.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(T.items())))
m.update({q:q+1000 for q,b in T if q not in m});L={(m[q],b):(w,d,m.get(z,z))for(q,b),(w,d,z)in T.items()}
ss=json.loads((BASE/'sites215.json').read_text());lems,blocks=s.prove_blocks(L);cases=[];start=time.monotonic()
for i,site in enumerate(ss):
 for positive in ([False,True] if site[1]=='CD' else [False]):
  try:
   v=s.case(L,lems,site,positive,append=0);v.pop('trace');v['rows']=sorted(v['rows']);cases.append(dict(site_index=i,positive=positive,**v))
  except Exception as e:
   print('FAIL',i,site,positive,str(e));raise
 if i%1000==0:print('SITE',i,'sec',time.monotonic()-start,flush=True)
(OUT/'runtime_cases.json').write_text(json.dumps(cases))
print('ALL',len(cases),'sec',time.monotonic()-start,flush=True)
spec=importlib.util.spec_from_file_location('validate_native',BASE/'code/runtime-inputs/validate_native.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
st=v.startup(T,limit=1000000);(OUT/'startup.json').write_text(json.dumps(st));print('STARTUP',{k:x for k,x in st.items()if k not in('trace','one_cells')},flush=True)
