#!/usr/bin/env python3
"""27 unrestricted integer variables by signed weighted root amalgamation.

Finite checks verify algebra and counts, not the semantic Pell/compiler proof.
"""
from pathlib import Path
import json, random
from collections import Counter

HERE = Path(__file__).resolve().parent
def require(test, message):
    if not test: raise ValueError(message)

def evaluate(source, values):
    vals=dict(values)
    for n,op,a,b in source:
        x=a if isinstance(a,int) else vals[a]
        y=b if isinstance(b,int) else vals[b]
        vals[n]=x+y if op=='+' else x-y if op=='-' else x*y
    return vals

def ledger(p):
    known=set(p['witnesses']+p['fixed_numerals'])
    for n,op,a,b in p['source']:
        require(n not in known and op in ('+','-','*'),'invalid gate')
        require(all(isinstance(x,int) or x in known for x in (a,b)),'undefined input')
        known.add(n)
    need={p['output']}
    for n,op,a,b in reversed(p['source']):
        if n in need: need.update(x for x in (a,b) if isinstance(x,str))
    require(all(n in need for n,_,_,_ in p['source']),'dead gate')
    require(set(p['witnesses']+p['fixed_numerals'])<=need,'dead input')
    cnt=Counter(row[1] for row in p['source'])
    p['ledger']={'operations':len(p['source']),'multiplications':cnt['*'],
                 'additions_subtractions':cnt['+']+cnt['-'],
                 'all_gates_live':True,'all_ports_live':True}

def degree_line(p,seed,prime):
    rng=random.Random(seed)
    vals={v:[rng.randrange(1,17),rng.randrange(1,17)] for v in p['witnesses']}
    vals.update({v:[c] for v,c in zip(p['fixed_numerals'],[31,127,10,45])})
    def plus(a,b,sgn):
        c=[((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
        while len(c)>1 and not c[-1]: c.pop()
        return c
    for n,op,a,b in p['source']:
        x=[a] if isinstance(a,int) else vals[a];y=[b] if isinstance(b,int) else vals[b]
        if op=='*':
            z=[0]*(len(x)+len(y)-1)
            for j,xx in enumerate(x):
                for k,yy in enumerate(y): z[j+k]=(z[j+k]+xx*yy)%prime
            while len(z)>1 and not z[-1]: z.pop()
        else:z=plus(x,y,1 if op=='+' else -1)
        vals[n]=z
    result=len(vals[p['output']])-1
    require(result==p['exact_degree'],'degree diagnostic failed')
    return {'prime':prime,'seed':seed,'degrees':[result]}

def build():
    src = json.loads((HERE/'parent_polynomial13_84.json').read_text())
    guards = ['Jrep','F','alpha','transport_quotient','s','eta','zeta']
    witnesses=[]; pre=[]
    for name in guards:
        x,y,z = [name+'_'+s for s in ('x','y','z')]
        witnesses += [x,y,z]
        pre += [[name+'_x2','*',x,x], [name+'_xx','+',name+'_x2',x],
                [name+'_y2','*',y,y], [name+'_xy','+',name+'_xx',name+'_y2'],
                [name+'_z2','*',z,z], [name+'_xyz','+',name+'_xy',name+'_z2'],
                [name,'+',name+'_xyz',1]]
    witnesses += ['h','i_raw','auxiliary_quotient','w_raw','gamma','t_raw']
    pre += [['i_twice','*',2,'i_raw'], ['i','+','i_twice',1],
            ['w','*','w_raw','w_raw'], ['t_twice','*',2,'t_raw'], ['t','+','t_twice',1]]
    source=list(pre)
    for row in src['source']:
        if row[0]=='M':
            source += [['M_half',row[1],row[2],row[3]], ['M','*',2,'M_half']]
        else: source.append(row)
    out={k:v for k,v in src.items() if k in ['fixed_numerals','output']}
    out.update(name='signed_integer27_even_weight',domain='unrestricted integers',
               witnesses=witnesses,source=source,exact_degree=1116,
               residual_exact_degrees=[35,13,4,1064],
               coefficient_binding={'manifest_from_package_root':'INSTANCE.json',
                   'default_recipe_from_package_root':'compiler/PRUNED_T4_CONSTANTS.json',
                   'fallback':'14-integer29 inherited06-blank67 tuple',
                   'mask_convention':'MF is shifted',
                   'scope':'Whole tuples only; signed canonical transfer must cover odd i and square w.'},
               source_pin='f0ae4e0991ca44a7bb4e5671d42e33d775e48035')
    ledger(out)
    require(len(witnesses)==27 and out['ledger']['operations']==139,'wrong size')
    return out

def independent(values):
    def pos(name):
        x,y,z=[values[name+'_'+s] for s in ('x','y','z')]
        return x*x+x+y*y+z*z+1
    J,F,alpha,z,s,eta,zeta=[pos(n) for n in ['Jrep','F','alpha','transport_quotient','s','eta','zeta']]
    h,T,gamma=[values[n] for n in ['h','auxiliary_quotient','gamma']]
    i=2*values['i_raw']+1;w=values['w_raw']**2;t=2*values['t_raw']+1
    beta,K,MC,MF=[values[n] for n in ['Bm1','Kconstant','MC','MF']]
    q=beta*J+1;Cw=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y
    k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H
    Dmain=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Nm=Dmain**2-Delta*c*c;Nk=k-h*E-R;Nt=(K+w)*Cw+q-F-z*(q-1)
    A=1+(E*k*Y)*(E*k*Y+k);Q=(Delta*i*c*c)**2;D=1+Delta*i*i*c**4
    v=c*T;Z=c+R*D;d=Q-1;e=Q*(D*v*v+Z*Z)-1;M=2*(D+v*v)
    C=d*(t*t+M*M*A)-e;B=2*Q*v*Z
    U=C*C+D*B*B-4*d*d*t*t*M*M*A
    Res=U*U-D*(2*C*B)**2
    return Nm*Nk*Nt*(1+Res)-1

def main():
    p=build(); rng=random.Random(270027)
    for _ in range(100):
        vals={x:rng.randrange(-2,3) for x in p['witnesses']}
        vals.update(dict(zip(p['fixed_numerals'],[31,127,10,45])))
        require(evaluate(p['source'],vals)[p['output']]==independent(vals),'formula diagnostic failed')
    diagnostics=[degree_line(p,2710,1000000007),degree_line(p,2711,1000000009)]
    (HERE/'integer27_product139.json').write_text(json.dumps(p,indent=2)+'\n')
    result={'variables':27,'operations':p['ledger'],'degree':1116,'random_formula_checks':100,
            'degree_diagnostics':diagnostics,
            'scope':'Exact algebra checks and univariate degree lower bounds; no endpoint or compiler formalization.'}
    (HERE/'integer27_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
