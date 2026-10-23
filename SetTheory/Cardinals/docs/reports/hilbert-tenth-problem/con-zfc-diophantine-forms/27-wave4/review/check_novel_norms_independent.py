#!/usr/bin/env python3
"""Independent finite circuit audit. Does not prove compiler semantics."""
from pathlib import Path
import json, random
ROOT=Path(__file__).resolve().parents[1]

def evaluate(p, data):
    out=dict(data)
    for name,op,a,b in p['source']:
        a=a if isinstance(a,int) else out[a]
        b=b if isinstance(b,int) else out[b]
        out[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
    return out

def multiply(x,y,radicands):
    result={}
    for a,v in x.items():
      for b,w in y.items():
        powers=tuple(a[i]+b[i] for i in range(3))
        coef=v*w
        for power,rad in zip(powers,radicands):coef*=rad**(power//2)
        key=tuple(power%2 for power in powers)
        result[key]=result.get(key,0)+coef
    return {k:v for k,v in result.items() if v}

def norm(a, split):
    # Direct product over all choices of the three square-root signs.
    rad=(a['G'],a['A'],a['D']); acc={(0,0,0):1}
    first_coefficient=a['HM'] if split else a['H']*a['L']
    for su in [-1,1]:
      for st in [-1,1]:
       for sf in [-1,1]:
        r={(0,0,0):a['S'],(1,0,0):-su*a['L'],(0,1,0):-st*first_coefficient}
        f={k:a['d']*v for k,v in multiply(r,r,rad).items()}
        f[(0,0,0)]=f.get((0,0,0),0)-a['H']**2*a['e']
        f[(0,0,1)]=f.get((0,0,1),0)+sf*a['H']**2*(2*a['Q']*a['v']*a['b'])
        acc=multiply(acc,f,rad)
    assert not any(k!=(0,0,0) and v for k,v in acc.items())
    return acc.get((0,0,0),0)

def audit(path,split,seed):
    p=json.loads(path.read_text());rng=random.Random(seed)
    needed=set(p['witnesses']+p['fixed_numerals']);names=set(needed)
    for n,op,l,r in p['source']:
        assert n not in names and op in ['+','-','*']
        assert all(isinstance(x,int) or x in names for x in [l,r]);names.add(n)
    final=[p['output']] if 'output' in p else [a for a,b in p['comparisons']]+[b for a,b in p['comparisons'] if isinstance(b,str)]
    live=set(final)
    for n,op,l,r in reversed(p['source']):
      if n in live:live.update(x for x in [l,r] if isinstance(x,str))
    assert all(n in live for n,op,l,r in p['source']) and needed<=live
    signs={};count=0
    for _ in range(96):
        values={name:rng.randrange(-2,4) for name in sorted(needed)}
        a=evaluate(p,values)
        if 'N' not in a:a['N']=a['N00']-a['GN11']
        assert a['N']==norm(a,split)
        assert a['N1']%8==0 and (a['N']-a['N0']**2)%64==0
        if 'output' in p and p['output']=='polynomial':assert a[p['output']]==a['Nk']*a['Nt']*(1+a['N'])-1
        if 'output' in p and p['output']=='sos':assert a[p['output']]==(a['Nk']-1)**2+(a['Nt']-1)**2+a['N']**2
        for name in ['H','L','G','A','D','v']:
            key=name+':'+str((a[name]>0)-(a[name]<0));signs[key]=signs.get(key,0)+1
        count+=1
    return {'file':str(path.relative_to(ROOT)),'variables':len(p['witnesses']),'operations':len(p['source']),'fixtures':count,'all_ports_and_gates_live':True,'sign_coverage':signs}

def ratio_bounds():
    count=0
    for q in [16,17,31]:
     for w in [0,1,4]:
      for s in [-7,-3,-1,1,3,7]:
       for eta,zeta in [(1,1),(2,3),(11,1)]:
        for i in [-3,-1,1,3]:
         for T in [-3,0,2]:
          for R in [q*(q*q-1)+1,q**4-3]:
           X=w*q;Y=s*q**3;k=eta+zeta;c=k*Y+eta;a=(X+1)*Y;H=4*a+3
           Delta=a*a+H;I=i*c*c;D=1+Delta*I*I;Q=(Delta*I)**2;b=c+R*D
           v=c*T;G=1+Delta*c*c;ell=X*k*Y*Y;A=1+ell*(ell+k)
           W=2*(i*I*(1+5*R*a*c)+v*v);B=abs(H)*W;L=1+H*W
           assert a*c>0 and i*I>0 and W>0 and B>8
           assert D*c*c<G*I*I
           assert D*D<4*(a*c*i*I)**2*G
           assert R*a*c*i*I>2
           assert 2*abs(i*T)*c*c<=i*I+v*v
           assert 2*abs(L)>B and 8*abs(L)<9*B
           if X:assert 64*G<81*A
           count+=1
    return count

if __name__=='__main__':
    paths=[(ROOT/'norms/two_weight_norm12_system.json',True),(ROOT/'norms/two_weight_norm12_product.json',True),(ROOT/'norms/two_weight_norm12_sos.json',True),(ROOT/'integers/integer24_original_system.json',False),(ROOT/'integers/integer24_original_product.json',False),(ROOT/'integers/integer24_original_sos.json',False),(ROOT/'integers/integer24_split2_system.json',True),(ROOT/'integers/integer24_split2_product.json',True),(ROOT/'integers/integer24_split2_sos.json',True),(ROOT/'integers/integer24_ratio_system.json',True),(ROOT/'integers/integer24_ratio_product.json',True),(ROOT/'integers/integer24_ratio_sos.json',True)]
    out={'scope':'Independent exact algebra and liveness only. Uniform soundness is established by the separate mathematical review, conditional on the inherited compiler and Pell theorems.','audits':[audit(p,s,713+i) for i,(p,s) in enumerate(paths)],'ratio_weight_signed_boundary_fixtures':ratio_bounds()}
    (ROOT/'review/NOVEL_NORM_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
