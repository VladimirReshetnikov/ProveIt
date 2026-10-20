from pathlib import Path
import subprocess,time,json
from independent_runtime import table

root=Path(__file__).resolve().parent
base=table(root/'../audit-work/conditional_g222.k.tm')
def emit(T):
 return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))
variants=[tuple(map(int,line.split())) for line in(root/'hybrid222-neutrals.txt').read_text().splitlines()]
focus={118,159,155,153,166,300,301,304,305,306}
variants.sort(key=lambda r:(r[0] not in focus,r[0]))
start=time.monotonic();success=[]
for i,change in enumerate(variants):
 q,b,w,d,z=change;T=dict(base);T[q,b]=(w,d,z)
 path=root/'neutral-current.k.tm';path.write_text(emit(T))
 r=subprocess.run([str(root/'fold_search'),str(path),'24'],text=True,capture_output=True,cwd=root)
 assert r.returncode==0,r.stderr
 if r.stdout.strip():
  for line in r.stdout.splitlines():
   kind,keep,drop,w0,d0,z0,w1,d1,z1=line.split();keep,drop,w0,d0,z0,w1,d1,z1=map(int,(keep,drop,w0,d0,z0,w1,d1,z1))
   phi=lambda q:keep if q==drop else q
   new={(s,a):(ww,dd,phi(zz))for(s,a),(ww,dd,zz)in T.items()if s!=drop}
   new[keep,0]=(w0,d0,phi(z0));new[keep,1]=(w1,d1,phi(z1))
   record={'neutral':change,'fold':line,'states':len(new)//2}
   out=root/f'potential221-{len(success)}.k.tm';out.write_text(emit(new));record['table']=str(out)
   success.append(record);print('SUCCESS',json.dumps(record),flush=True)
  (root/'neutral-success.json').write_text(json.dumps(success,indent=2)+'\n')
 if i%25==0:print('progress',i+1,'/',len(variants),'seconds',round(time.monotonic()-start,1),flush=True)
print('FINISHED',len(variants),'variants',len(success),'successes',round(time.monotonic()-start,1),flush=True)
