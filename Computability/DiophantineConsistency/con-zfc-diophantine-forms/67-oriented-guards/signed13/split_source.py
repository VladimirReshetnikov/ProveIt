"""Degree-separated source emitter with one off-target positivity pad.
The source certificate is copied as data; verifier is run independently.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import hashlib,json
from circuit import DAG
ROOT=Path(__file__).resolve().parent
KAPPA=2134940
class ReuseDAG(DAG):
    """Deterministic exponent reuse; local adaptation of wave8 Sun emitter."""
    def __init__(self):
        super().__init__();self.power_cache={};self.known_exponents={}
    def power(self,a,n):
        if n<0:raise ValueError('negative exponent')
        if n==0:return self.const(1)
        if n==1:return a
        if (a,n) in self.power_cache:return self.power_cache[a,n]
        known=self.known_exponents.setdefault(a,{1:a})
        pairs=[(i,n-i) for i in known if n-i in known]
        if pairs:
            i,j=min(pairs,key=lambda ij:abs(ij[0]-ij[1]));out=self.times(known[i],known[j])
        else:
            h=self.power(a,n//2);out=self.times(h,h)
            if n%2:out=self.times(out,a)
        self.power_cache[a,n]=out;known[n]=out;return out

def source_split(d,variant,unused_code=None):
    compact='compact' in variant
    data=json.loads((ROOT/'split/split_code.json').read_text());kernels=json.loads((ROOT/'split/split_kernels.json').read_text())
    add,mul,sub,pw,c,save=d.plus,d.times,d.minus,d.power,d.const,d.save
    variables=['epsilon','g','h','s','w','phi','i','j','z1','z2','z3','residue','normroot'];v={n:d.var(n) for n in variables}
    recipes={};coefs={}
    def coefficient(rec):
        key=json.dumps(rec,sort_keys=True)
        if key not in recipes:recipes[key]=(f's{len(recipes):03d}',rec)
        name=recipes[key][0]
        if name not in coefs:coefs[name]=c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.fixed(name)
        return coefs[name]
    b=save('b',mul(c(2),pw(v['epsilon'],2)));B=save('B',mul(d.fixed('base_scale'),pw(b,2)))
    @lru_cache(None)
    def bp(n):return pw(B,n)
    def sparse(terms):
        terms=sorted(terms);e,out=terms.pop()
        while terms:
            f,coef=terms.pop();out=add(mul(out,bp(e-f)),coef);e=f
        return mul(out,bp(e))
    ks=[]
    for row in kernels['kernels']:
        ks.append(save('D'+str(row['degree']),sparse([(t['exponent'],coefficient(t['coefficient'])) for t in row['terms']])))
    W=max(data['weights']);Q=max(data['targets']);Kh=data['convolution_height'];E=Kh+W+2
    ell=save('ell',sparse([(w,c(1)) for w in data['weights']]))
    targets=save('targets',sparse([(q,c(1)) for q in data['targets']]))
    U=save('Usource',add(ell,v['g']));G=save('Gsource',add(ks[0],mul(U,add(ks[1],mul(U,ks[2])))))
    pad=save('positivity_pad',bp(1946));Gp=save('Gplus',add(G,pad))
    N0=save('N0',bp(W+1));mask=save('mask',sub(sub(N0,c(1)),mul(sub(b,c(1)),ell)))
    Tc=save('Tcode',add(mask,mul(sub(B,c(2)),targets,N0)))
    Jc=save('Jcode',add(mul(c(2),Gp),targets));Sc=save('Scode',add(v['g'],mul(Jc,N0)))
    L=save('block',bp(E) if compact else mul(c(2),b,bp(E)))
    R=save('R',sub(sub(mul(L,add(L,Sc,Tc,c(1))),Sc),c(1)))
    Hpop=E+W+23;delta=(Hpop-15)%2;nexp=1089;cexp=18146981
    N=save('N',mul(d.fixed('threshold_scale'),pw(v['epsilon'],3) if compact else pw(b,delta),bp(nexp)))
    cap=save('cap',mul(b,bp(W)));Gcap=save('Gcap',mul(c(32),cap))
    meta={'variables':variables,'W':W,'H':Q,'Kh':Kh,'E':E,'Hpop':Hpop,'threshold_b_power':0 if compact else delta,'threshold_epsilon_power':3 if compact else 0,'compact_calibration':compact,'threshold_B_power':nexp,'base_scale_exponent':KAPPA,'threshold_scale_exponent':cexp,'positivity_pad_exponent':1946,
      'coefficient_recipes':[{'name':name,'terms':r} for name,r in recipes.values()],
      'weights':data['weights'],'target_order':data['order'],'targets':data['targets'],'source_parent_sha256':kernels['source_sha256'],'split_code_sha256':kernels['code_sha256'],'source_type':'degree-separated kernels with one off-target positivity pad'}
    return v,b,N,R,cap,Gcap,meta
