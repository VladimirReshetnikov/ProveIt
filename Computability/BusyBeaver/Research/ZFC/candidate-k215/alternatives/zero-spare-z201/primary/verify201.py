#!/usr/bin/env python3
"""Check zero-valued spare allocation with existing symbolic induction rules.

The core symbolic checker is unchanged. Its existing append parameter is set
to zero. Every source site and decrement guard is checked; this is an ordinary
mathematical certificate, not a proof-assistant proof. Logical calibration is
a separate obligation.
"""
import argparse,gzip,hashlib,json,sys,time
import sys
if not __debug__: raise SystemExit("Run without -O: assertions are required for verification.")
from pathlib import Path

def compact(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(x).hexdigest()

def blank(table,start,limit=500000):
 q=start;h=0;ones=set();trace=[]
 for tick in range(limit+1):
  if q==84 and ones and min(ones)==h-1:
   rights=sorted(x for x in ones if x>h-1)
   if rights and rights[0]>=h+64:
    header=rights[0];p=header+1;last=max(ones);values=[];good=True
    while p<=last:
     if p in ones or p+1 not in ones:good=False;break
     p+=1;n=0
     while p in ones:n+=1;p+=1
     values.append(n-1)
    if good and len(values)>=10:
     physical_to_logical=(6,2,0,4,3,7,8,5,1)
     regs=[values[i]for i in physical_to_logical]
     return {'steps':tick,'state':q,'head':h,'header':header,
       'gap':header-h-64,'registers':regs,'physical_registers':values[:9],
       'spares':values[9:],'one_cells':sorted(ones),'trace':trace}
  assert tick<limit,'Startup bound exhausted'
  b=int(h in ones);w,d,z=table[q,b];trace.append([q,h,b,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 a.out.mkdir(parents=True,exist_ok=False)
 sys.path.insert(0,str(a.base/'code/runtime-inputs'));import validate_native as v
 native=(a.base.parent/'research/command_family/201/candidate.native.tm').read_bytes();source=(a.base.parent/'research/command_family/201/sites.json').read_bytes()
 assert sha(native)=='4fa3067eac0d4fa9d633fc5d41cb64ed0092252c332dc81d71606a08a8f2227e'
 assert sha(source)=='0b7e1e035796b954b96a358b8e634b921abb36118ce84baf02b4e61c29b95c80'
 T=v.s.r.table(a.base.parent/'research/command_family/201/candidate.native.tm');assert T[198,0]==(1,-1,40)
 T[198,0]=(0,-1,40)
 raw=('#! start 74\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode()
 (a.out/'z215.native.tm').write_bytes(raw);(a.out/'sites215.json').write_bytes(source)
 states={q for q,b in T};reach={74};todo=[74]
 for q in todo:
  for b in(0,1):
   z=T[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 assert states==reach and len(states)==215
 m={int(k):int(w)for k,w in json.loads((a.base/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:
  if q not in m:m[q]=q+1000
 assert len({m[q]for q in states|{254}})==216
 L={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
 lemmas,blocks=v.s.prove_blocks(L)
 st=blank(T,74)
 assert(st['steps'],st['state'],st['head'],st['registers'])==(118411,84,-5,[2,0,2,0,0,0,0,0,0])
 (a.out/'startup.json.gz').write_bytes(gzip.compress(compact(st),mtime=0))
 print('STARTUP',{k:x for k,x in st.items()if k not in ('trace','one_cells','spares')},'spares',len(st['spares']),flush=True)
 ss=json.loads(source);cases=[];rows=set();t0=time.monotonic();failed=[]
 for i,site in enumerate(ss):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   try:
    ans=v.s.case(L,lemmas,site,positive,append=0)
    rows.update(ans['rows']);ans['rows']=sorted(ans['rows']);ans.pop('trace')
    cases.append({'site_index':i,'positive':positive,**ans})
   except Exception as e:failed.append({'site_index':i,'positive':positive,'reason':str(e)});break
  if failed:break
  if(i+1)%1000==0:print('SITE',i+1,'CASES',len(cases),'SECONDS',time.monotonic()-t0,flush=True)
 total=sum(2 if op=='CD'else 1 for pc,op,arg in ss)
 inv={v:k for k,v in m.items()}
 row_native=sorted((inv[q],b)for q,b in rows)
 for block in blocks:
  for event in block['trace']:
   if event[0]!='list':rows.add(tuple(event[1][:2]))
 report={'status':'UNIVERSAL_MATHEMATICAL_PASS'if not failed and len(cases)==total else'NOT_PROVED',
   'working_states':len(states),'graph_reachable_states':len(reach),'rows':len(T),
   'start':74,'dispatcher':84,'halt':254,'append_value':0,'source_sites':len(ss),
   'expected_cases':total,'proved_cases':len(cases),'failures':failed,
   'table_sha256':sha(raw),'source_sha256':sha(source),'checker_sha256':sha(Path(v.s.__file__).read_bytes()),
   'helper_sha256':sha(Path(v.s.r.__file__).read_bytes()),'wrapper_sha256':sha(Path(__file__).read_bytes()),
   'seconds':time.monotonic()-t0,'symbolic_steps':sum(x['symbolic_steps']for x in cases),
   'minimum_duration_constant':min(x['duration'][0]for x in cases),
   'blocks':blocks,'native_rows_covered_including_blocks':sorted((inv[q],b)for q,b in rows),
   'startup':{k:x for k,x in st.items()if k not in ('trace','one_cells')},
   'scope':'All natural primary values at each guard, arbitrary natural gap, arbitrary first spare value and arbitrary finite remaining spare list, complete zero exterior. Induction over unary scans and block lists. Source consistency calibration is separate. No proof-assistant-kernel claim.'}
 (a.out/'runtime_cases.json.gz').write_bytes(gzip.compress(compact(cases),mtime=0))
 (a.out/'runtime.json').write_text(json.dumps(report,indent=2)+'\n')
 print({k:x for k,x in report.items()if k not in ('blocks','native_rows_covered_including_blocks','startup')},flush=True)
 assert report['status']=='UNIVERSAL_MATHEMATICAL_PASS'

if __name__=='__main__':main()
