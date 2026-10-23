"""Independent finite-field polynomial evaluation of inert JSON records."""
import json, numpy as np
from pathlib import Path
ROOT=Path(__file__).resolve().parent
p=1000003
# Each convolution has <=2200 terms, so int64 remains exact at this prime.
def trim(a):
 a=a%p
 nz=np.flatnonzero(a)
 return a[:int(nz[-1])+1] if len(nz) else np.array([0],dtype=np.int64)
def add(a,b,sgn=1):
 c=np.zeros(max(len(a),len(b)),dtype=np.int64);c[:len(a)]+=a;c[:len(b)]+=sgn*b;return trim(c)
def mul(a,b):return trim(np.convolve(a,b))
ans=[]
for fp in sorted(ROOT.glob('*_product.json')):
 o=json.loads(fp.read_text());v={n:np.array([0,ii+2],dtype=np.int64) for ii,n in enumerate(o['witnesses'])};v.update({n:np.array([ii+17],dtype=np.int64) for ii,n in enumerate(o['fixed_numerals'])})
 def get(x):return v[x] if isinstance(x,str) else np.array([x],dtype=np.int64)
 for n,op,x,y in o['source']:
  aa,bb=get(x),get(y);v[n]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
 degree=len(v[o['output']])-1;ans.append({'file':fp.name,'degree':degree,'operations':o['operations']});print(ans[-1])
(ROOT/'DEGREE_DIAGNOSTICS.json').write_text(json.dumps(ans,indent=2)+'\n')
