from pathlib import Path
import concurrent.futures,hashlib,json,subprocess,sys,time
sys.dont_write_bytecode=True
import source_inventory as I
L=I.L
root=Path('.').resolve();work=root/'analysis/comparison/rotations';work.mkdir(exist_ok=True)
exe=root/'analysis/comparison/finite_fast'

def encode(t):return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))

def rotate(t,rows,rotation):
 tree,occ,rots=I.inventory(t,rows);p,q,side=rotation[:3];nt=dict(t)
 for path,node in occ[p]:
  if side==0:
   a,b=node[0];c=node[1];replacement=(a,(b,c))
  else:
   a=node[0];b,c=node[1];replacement=((a,b),c)
  tree=L.replace(tree,path,replacement)
 if side==0:
  a,b,c=t[q,0][2],t[q,1][2],t[p,1][2]
  nt.update({(p,0):(0,1,a),(p,1):(1,1,q),(q,0):(0,1,b),(q,1):(1,1,c)})
 else:
  a,b,c=t[p,0][2],t[q,0][2],t[q,1][2]
  nt.update({(p,0):(0,1,q),(p,1):(1,1,c),(q,0):(0,1,a),(q,1):(1,1,b)})
 return nt,L.sites(tree)

def merge(t):
 t=dict(t);folds=[]
 while True:
  rows={};dup=None
  for q in sorted({q for q,b in t}):
   k=tuple(t[q,b]for b in(0,1))
   if k in rows:dup=q,rows[k];break
   rows[k]=q
  if dup is None:break
  q,r=dup;folds.append(dup)
  t={(s,b):(w,d,r if z==q else z)for(s,b),(w,d,z)in t.items()if s!=q}
 return t,folds

def candidate(label,t,rows,history):
 name=label+'_'+'_'.join(f'{p}-{q}-{s}'for p,q,s,*_ in history)
 nt,ns=rotate(t,rows,history[-1]);mt,folds=merge(nt)
 d=work/name;d.mkdir(exist_ok=True)
 (d/'machine.tm').write_text(encode(mt));(d/'sites.json').write_text(json.dumps(ns,separators=(',',':'))+'\n')
 (d/'sites.tsv').write_text(''.join(f'{p}\t{o}\t{-1 if a is None else a}\n'for p,o,a in ns))
 result=subprocess.run([str(exe),str(d/'machine.tm'),str(d/'sites.tsv')],capture_output=True,text=True)
 record={'name':name,'history':history,'folds':folds,'states':len(mt)//2,'pass':result.returncode==0,'message':result.stdout+result.stderr}
 (d/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 return record,mt,ns

def main():
 began=time.monotonic();allresults=[]
 for label,tp,sp in [('A',I.base/'machine/variant_plain/u208.native.tm',I.base/'machine/variant_plain/u208.sites.json')]:
  t=I.read(tp);rows=json.loads(sp.read_text());_,_,rots=I.inventory(t,rows)
  with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
   for record,nt,ns in ex.map(lambda rot:candidate(label,t,rows,[rot[:3]]),rots):
    allresults.append(record);print(json.dumps(record),flush=True)
 print('TIME',time.monotonic()-began)
 (work/'single_results.json').write_text(json.dumps(allresults,indent=2)+'\n')
if __name__=='__main__':main()
