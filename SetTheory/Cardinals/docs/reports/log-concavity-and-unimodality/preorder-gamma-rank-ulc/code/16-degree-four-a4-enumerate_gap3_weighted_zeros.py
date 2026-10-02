"""Find and exactly verify weighted leading zero directions from sums of binary zeros."""
from integer_sos_common import *

def compute(tid,maxsum=3):
 d=T[tid]['variables'];p=dict(T[tid]['gap3']);top=[(e,c) for e,c in p.items() if degree(e)==6]
 exp=np.array([[(e>>(3*i))&7 for i in range(d)] for e,c in top],dtype=np.int64)
 coeff=np.array([c*(math.factorial(6)//math.prod(math.factorial(v) for v in row)) for row,(e,c) in zip(exp,top)],dtype=np.int64)
 def exact(v):return sum(int(c)*math.prod(int(x)**int(q) for x,q in zip(v,row)) for c,row in zip(coeff,exp))
 binary=[tuple((s>>i)&1 for i in range(d)) for s in range(1,1<<d) if exact(tuple((s>>i)&1 for i in range(d)))==0]
 cand=set(binary)
 for k in range(2,maxsum+1):
  for rays in itertools.combinations_with_replacement(binary,k):
   v=tuple(map(sum,zip(*rays)));g=math.gcd(*v);cand.add(tuple(x//g for x in v))
 cand=sorted(cand);zeros=[]
 for j in range(0,len(cand),128):
  vv=np.array(cand[j:j+128],dtype=np.int64)
  value=np.prod(vv[:,None,:]**exp[None,:,:],axis=2)@coeff
  for v,val in zip(cand[j:j+128],value):
   if val==0:
    assert exact(v)==0;zeros.append(v)
   elif val<0:assert exact(v)>=0,('negative leading direction',tid,v,exact(v))
 result={'template':tid,'degree':6,'binary_directions':len(binary),'candidate_directions':len(cand),'weighted_zero_directions':zeros}
 (D/f'gap3_weighted_leading_zeros_{tid}.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
 print('WEIGHTED_ZEROS',tid,'binary',len(binary),'candidates',len(cand),'zeros',len(zeros),flush=True)
 return zeros
if __name__=='__main__':
 for tid in map(int,sys.argv[1:]):compute(tid)
