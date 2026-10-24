#!/usr/bin/env python3
"""Independent literal radix checks and finite controls; imports no constructor."""
import argparse,json,math
from pathlib import Path

def require(ok,msg):
    if not ok: raise ValueError(msg)

def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return {m:c for m,c in out.items() if c}

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}

def expander(meta,leaves):
    cuts={tuple(a):{(i,):1} for i,a in enumerate(leaves)}
    memo={}
    def atom(a):
        a=tuple(a)
        if a in cuts:return cuts[a]
        if a[0]=='c':return {():a[1]} if a[1] else {}
        if a in memo:return memo[a]
        index=a[1]
        require(str(index) in meta['gates'],'unbound non-gate atom '+str(a))
        row=meta['rows'][meta['gates'][str(index)]]
        terms={tuple(m):c for c,m in row['terms']}
        sign=terms.pop((index,),0)
        require(abs(sign)==1,'non-monic gate')
        require(not any(index in m for m in terms),'cyclic gate')
        out={}
        for mon,c in terms.items():
            term={():-sign*c}
            for v in mon:term=mul(term,atom(('v',v)))
            out=add(out,term)
        memo[a]=out
        return out
    return atom

def inspect(meta):
    ra=meta['radix'];am=meta['amplification']
    require(ra['aggregate_bound_removed'] is True,'aggregate bound flag')
    require(am['K']==am['R'],'K is not R')
    minimum=am['horizon_minimum']
    require(type(minimum) is int and minimum>=12,'unreviewed horizon')
    require(am['local_degree_bound']==8388608,'local exponent drift')
    require(am['label_degree_bound']==4194304,'label exponent drift')
    require(not any(r['label']=='crt.aggregate_representative_bound' for r in meta['rows']),
            'aggregate bound row remains')
    independent=[r for r in meta['ranges'] if r[3]!='crt.range.derived_label_sum']
    require(len(independent)==9,'independent representative count')
    require(len(meta['ranges'])==10,'range count')
    reps=[r[0] for r in independent]
    leaves=[ra['V']]+reps
    expand=expander(meta,leaves)
    expect={():1}|{(i,):1 for i in range(10)}
    require(expand(ra['base'])==expect,'literal radix base differs')
    matches=[p for p in meta['powers'] if p['base']==ra['base'] and p['exponent']==am['K']]
    require(len(matches)==1,'radix power request')
    expandq=expander(meta,[am['N'],matches[0]['output']])
    require(expandq(ra['radix'])=={(0,1):1},'q is not N times power output')
    names={v['name']:i for i,v in enumerate(meta['variables'])}
    txfy=[am['t'],['v',names['x']],['v',names['y']],am['F']]
    ex=expander(meta,txfy)
    require(ex(am['K'])=={():2,(0,):1,(1,):1,(2,):1,(3,):1},'R literal identity')
    for _,k,N,label in meta['ranges']:
        require(N==am['N'],'range modulus drift')
        gap=add(ex(am['K']),ex(k),-1)
        require(gap.get((),0)>=1 and all(c>=0 for c in gap.values()),'range index not strictly below K: '+label)
    floor=math.factorial(minimum)
    require(floor==am['factorial_floor'],'factorial floor')
    ell=am['label_degree_bound'];E=am['local_degree_bound']
    require(3*ell*(minimum+1)<=2*floor,'derived budget base')
    a=floor.bit_length()-1
    require(am['floor_exponent']==a,'floor exponent')
    require(a*E<2**a and 2*E<=2**a,'local growth base')
    return {'independent_representatives':9,'range_calls':10,'radix_power_bound':True,
            'literal_radix_base':True,'amplification_is_R':True,'strict_lower_index_bounds':10,
            'horizon_minimum':minimum,'factorial_floor':floor,'floor_power_of_two_exponent':a}

def controls():
    cases=0
    for N in range(1,5):
      for V in range(1,6):
       for S in range(1,30):
        for K in range(2,9):
         q=N*(V+1+S)**K
         require(q%N==0 and q>V*V and q>(S+1)**K,'basic radix bound')
         for n in range(1,S+1):
          for j in range(K+1):
           value=math.comb(n,j) if j<=n else 0
           require(value<q,'ordinary carry bound')
           cases+=1
    derived=0
    for S in range(1,12):
     for ell in range(1,5):
      for k in range(1,5):
       K=max(2,ell*k);q=((S+2)**K)
       J=(S+1)**ell
       for j in range(k+1):
        require((math.comb(J,j) if j<=J else 0)<q,'derived carry bound')
        derived+=1
    factorial=0
    for t in range(1,11):
     for F in range(1,10):
      rho=F*t*t;V=(rho+1)**t
      for j in range(t+1):
       require(math.comb(rho+t,j)<=V,'factorial digit bound')
       require(math.comb(F*F+t,j)<=V*V,'product digit bound')
       factorial+=1
    return {'ordinary_binomial_cases':cases,'derived_binomial_cases':derived,'factorial_bootstrap_cases':factorial,
            'scope':'Finite arithmetic controls supplement the unbounded proof.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('metadata',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();meta=json.loads(a.metadata.read_text())
    result={'literal':inspect(meta),'controls':controls()}
    corrupt=json.loads(json.dumps(meta));corrupt['radix']['base']=corrupt['radix']['V']
    try:inspect(corrupt)
    except ValueError:result['changed_base_rejected']=True
    else:raise ValueError('changed radix accepted')
    corrupt=json.loads(json.dumps(meta));corrupt['amplification']['K']=['c',1]
    try:inspect(corrupt)
    except ValueError:result['changed_exponent_rejected']=True
    else:raise ValueError('changed exponent accepted')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text)

if __name__=='__main__':main()
