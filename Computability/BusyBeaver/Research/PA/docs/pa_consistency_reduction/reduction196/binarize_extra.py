from pathlib import Path
import sys,inspect,json,random,time
import binarize_exact as B
from optimize_antecedents import O
source=inspect.getsource(O.evaluate).replace('if B.zero_shape(t)[1]>6:return 1000,0,0,[]','if False:return 1000,0,0,[]')
ns=dict(O.__dict__);exec(source,ns);unbounded=ns['evaluate']

def run(path,trials=1000,bound=7):
 src=inspect.getsource(B.binarize).replace('>6','>'+str(bound))
 ns=dict(B.__dict__);exec(src,ns);binarize=ns['binarize']
 data=json.load(open(path));best=1000;seen=set();start=time.time()
 for seed in range(trials):
  for l,(h,t)in binarize(data,seed).items():
   if h>=48 or t in seen:continue
   seen.add(t);s,n,c,ds=unbounded(t)
   if s>=1000:continue
   z=O.B.zero_shape(t)[1];extra=0 if z<=6 else z-5;s+=extra
   if s<best:
    best=s;print('BEST',Path(path).name,s,n,c,'zero',z,'height',h,'seed',seed,flush=True)
    out=Path(path).with_name(Path(path).stem+f'_extra{bound}_best.json');O.output(t,tuple(range(6)),out)
    if s<196:print('TARGET',str(out),ds,flush=True)
 print('DONE',best,'trees',len(seen),'seconds',time.time()-start,flush=True)
if __name__=='__main__':run(sys.argv[1],int(sys.argv[2])if len(sys.argv)>2 else 1000,int(sys.argv[3])if len(sys.argv)>3 else 7)
