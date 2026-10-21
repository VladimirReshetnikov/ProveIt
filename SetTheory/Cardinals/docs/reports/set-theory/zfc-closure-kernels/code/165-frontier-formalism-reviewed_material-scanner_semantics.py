from pathlib import Path
import importlib.util,json,sys
B=Path('/dev/shm/zfc214_68350ec13e56');K=B/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215';M=B/'machine_work'
p=K/'code/runtime-inputs/runtime/independent_runtime.py';sp=importlib.util.spec_from_file_location('ir',p);ir=importlib.util.module_from_spec(sp);sp.loader.exec_module(ir)
T0=ir.table(M/'scanner214.native.tm');mapping={int(k):int(v) for k,v in json.loads((K/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()};mapping.update({q:q+1000 for q,b in T0 if q not in mapping});T={(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in T0.items()};rows=json.loads((K/'sites215.json').read_text());bad=sorted({x['site_index'] for x in json.loads((M/'scanner214_all/runtime.json').read_text())['failures']}); tokens=json.loads((B/'source_work/macro_parse.json').read_text())['tokens']
def pcdecode(conf):
 q,h,ones=conf
 s=''.join(str(int(h+i in ones))for i in range(60))
 match=[i for i,x in enumerate(rows)if s.startswith(x[0])]
 return match, s.rstrip('0')
def framedecode(conf):
 q,h,ones=conf;right=sorted(x for x in ones if x>=h+52)
 if not right:return None
 p=right[0]+1;last=max(ones);vs=[]
 while p<last:
  if p in ones or p+1 not in ones:return None
  st=p+1;p=st
  while p in ones:p+=1
  vs.append(p-st-1)
 if len(vs)<10:return None
 return [vs[j]for j in ir.PHY],vs[9:],right[0]-h-64
out=[]
for i in bad:
 s=rows[i];tok=next((t for t in tokens if t['lo']<=i<t['hi']),None)
 for v in (0,1,2):
  regs=[2]*9;regs[6]=regs[7]=0
  if s[1]=='CD':regs[s[2]]=v
  exp,meta=ir.expected(s,regs,[0]);got,tick,_=ir.run(T,s[0],regs,limit=300000)
  a,pc=pcdecode(got);b,_=pcdecode(exp)
  dec=framedecode(got);out.append(dict(i=i,site=s,macro=tok,regcase=v,steps=tick,actual_site=a,expected_site=b,actual_pc=pc,expected_pc=meta['pc'],regs_changed=None if dec is None else [[j,meta['registers'][j],dec[0][j]]for j in range(9) if meta['registers'][j]!=dec[0][j]],state=got[0],head=got[1],clean=ir.clean_dispatch(*got)))
  print(i,s[1:],tok,'v',v,'=>',a,'want',b,'changed',out[-1]['regs_changed'],'q/h',got[:2],flush=True)
(B/'theory_work/scanner_semantic_cases.json').write_text(json.dumps(out,indent=2)+'\n')
