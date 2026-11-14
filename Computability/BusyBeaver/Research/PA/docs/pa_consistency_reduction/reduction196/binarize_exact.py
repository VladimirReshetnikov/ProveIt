"""Binarize a solved n-ary SLP with a six-zero path bound and macro contexts."""
from pathlib import Path
import sys,json,functools,random,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import optimize_parameters as O
import symbolic as S

def binarize(data,seed=0):
 rng=random.Random(seed);rules=data['rules'];raw=S.source_tree()[1]
 atomdepth={v:max(len(p)for p,op in S.flatten(raw[k]))for k,v in data['tokens'].items()}
 atomdepth.update(i=0,B=0)
 @functools.lru_cache(None)
 def make(name):
  if name not in rules:return {O.B.LEADING[name]:(atomdepth[name],name)}
  pieces=rules[name];L=len(pieces);dp={}
  for i,x in enumerate(pieces):dp[i,i+1]=make(x)
  for n in range(2,L+1):
   for i in range(L-n+1):
    j=i+n;out={}
    for k in range(i+1,j):
     for la,(ha,a)in dp[i,k].items():
      if la+1>6 or a=='G':continue
      for lb,(hb,b)in dp[k,j].items():
       if b in('R','S'):continue
       h=1+max(ha,hb);l=la+1;t=(a,b)
       if l not in out or h<out[l][0]or(h==out[l][0]and rng.random()<.25):out[l]=h,t
    dp[i,j]=out
  return dp[0,L]
 return make(data['root'])

def run(path,trials=100):
 data=json.loads(Path(path).read_text());best=1000;bestt=None;seen=set();begin=time.time()
 for seed in range(trials):
  possible=binarize(data,seed)
  if not possible:
   print('NO_FEASIBLE_BINARIZATION',path,flush=True);break
  for leading,(height,t)in possible.items():
   if height>=48 or t in seen:continue
   seen.add(t);s,n,c,ds=O.evaluate(t)
   if s<best:
    best=s;bestt=t
    print('BEST',Path(path).name,s,n,c,'height',height,'leading',leading,'seed',seed,'folds',ds,flush=True)
    p=Path(path).with_name(Path(path).stem+'_binary_best.json');O.output(t,tuple(range(6)),p)
    out=json.loads(p.read_text());out['word']=data['word'];out['nary_source']=str(path);p.write_text(json.dumps(out,indent=2))
 return best,bestt
if __name__=='__main__':
 for path in sys.argv[1:]:run(path)
