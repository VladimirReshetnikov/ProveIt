from pathlib import Path
import sys,json,concurrent.futures,subprocess,time,itertools
sys.dont_write_bytecode=True
sys.path.insert(0,'analysis/comparison');import source_inventory as I
out=Path('analysis/reduction_search/combinations');out.mkdir(exist_ok=True)
t=I.read(I.base/'machine/variant_plain/u208.native.tm')
rots=[(18,100,0),(142,143,1),(156,162,1),(52,154,0),(162,203,1),(207,7,1),(132,222,0),(129,146,0),(135,221,0),(225,210,1)]
def change(rot):
 p,q,side=rot
 if side==0:
  a,b,c=t[q,0][2],t[q,1][2],t[p,1][2]
  return{(p,0):(0,1,a),(p,1):(1,1,q),(q,0):(0,1,b),(q,1):(1,1,c)}
 a,b,c=t[p,0][2],t[q,0][2],t[q,1][2]
 return{(p,0):(0,1,q),(p,1):(1,1,c),(q,0):(0,1,a),(q,1):(1,1,b)}
changes=list(map(change,rots))
def run(mask):
 nt=dict(t);selected=[]
 for j,rot in enumerate(rots):
  if mask>>j&1:nt.update(changes[j]);selected.append(rot)
 p=out/f'{mask:04d}.tm';p.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(nt.items())))
 run=subprocess.run(['analysis/reduction_search/integrated_folds',str(p),'unused','7'],capture_output=True,text=True,check=True)
 rec={'mask':mask,'rotations':selected,'candidates':run.stdout.strip().splitlines()}
 if rec['candidates']:
  print('CANDIDATES',json.dumps(rec),flush=True);(out/f'{mask:04d}.json').write_text(json.dumps(rec,indent=2)+'\n')
 else:p.unlink()
 return rec
masks=[mask for mask in range(1,1<<len(rots))if not(mask>>2&1 and mask>>4&1)]
start=time.monotonic();results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=3)as ex:
 for i,rec in enumerate(ex.map(run,masks)):
  results.append(rec)
  if i%50==0:print('PROGRESS',i+1,'/',len(masks),'seconds',time.monotonic()-start,flush=True)
(out/'results.json').write_text(json.dumps({'seconds':time.monotonic()-start,'results':results},indent=2)+'\n')
