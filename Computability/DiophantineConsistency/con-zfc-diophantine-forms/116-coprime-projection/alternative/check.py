#!/usr/bin/env python3
"""Independent exact arithmetic and literal-artifact regressions.

This is a finite checker, not a proof assistant or consistency decision.
It intentionally does not import build.py or the inherited DAG builder.
"""
from pathlib import Path
from math import factorial, prod
from copy import deepcopy
import hashlib
import json
import random
import sys

HERE=Path(__file__).resolve().parent
sys.set_int_max_str_digits(0)


def need(test,message):
    if not test: raise RuntimeError(message)


def evaluate(obj,env,modulus=None):
    values=[]
    for i,node in enumerate(obj['nodes']):
        op=node['op']
        if op=='const':
            need(type(node['value']) is int,'integer constant')
            value=node['value']
        elif op=='var': value=env[node['name']]
        elif op in ('add','mul'):
            need(all(type(j) is int and 0<=j<i for j in node['args']),'topology')
            args=[values[j] for j in node['args']]
            value=sum(args) if op=='add' else prod(args)
        elif op=='pow_fixed':
            need(type(node['exponent']) is int and node['exponent']>=0,'fixed polynomial exponent')
            need(type(node['base']) is int and 0<=node['base']<i,'power topology')
            value=pow(values[node['base']],node['exponent']) if modulus is None else pow(values[node['base']],node['exponent'],modulus)
        else: raise RuntimeError('nonpolynomial operation: '+op)
        values.append(value if modulus is None else value%modulus)
    return values


def degree_ledger(obj):
    degrees=[]
    for node in obj['nodes']:
        op=node['op']
        if op=='const': d=0
        elif op=='var': d=1
        elif op=='add': d=max((degrees[i] for i in node['args']),default=0)
        elif op=='mul': d=sum(degrees[i] for i in node['args'])
        elif op=='pow_fixed': d=degrees[node['base']]*node['exponent']
        else: raise RuntimeError('nonpolynomial operation')
        degrees.append(d)
    return degrees


def rows(requests,aux,retained_A=None):
    z,U,v,q,b=aux['z'],aux['U'],aux['v'],aux['q'],aux['b']
    Y=[k+loc['y'] for (n,k,m),loc in zip(requests,aux['local'])]
    D=prod(Y); V=D*D*(v+1); B=1+4*D*(q+1)
    A=B-U*b if retained_A is None else retained_A
    W=2+sum(sum(req) for req in requests)
    N=lambda a,x,y:x*x-(a*a-1)*y*y-1
    out={'scale':A*A-W**3*(W+2)*(z+1)**2-1,
         'auxiliary_norm':N(A,U,V)}
    if retained_A is not None: out['base_congruence']=B-A-U*b
    for i,((n,k,m),loc,yy) in enumerate(zip(requests,aux['local'],Y)):
        T=2*A*n-n*n-1
        X=yy*(A-n)+m+T*loc['h']
        S=X+U*loc['s']; R=k+4*yy*loc['t']
        out['main_norm_'+str(i)]=N(A,X,yy)
        out['index_norm_'+str(i)]=N(B,S,R)
    return out,{'A':A,'B':B,'D':D,'V':V,'W':W,'Y':Y}


def env_for(requests,aux,retained_A=None):
    out={n+str(i):value for i,req in enumerate(requests) for n,value in zip(('n','k','m'),req)}
    out.update({'p_'+name:aux[name] for name in ('z','U','v','q','b')})
    out.update({'p_'+name+str(i):loc[name] for i,loc in enumerate(aux['local']) for name in ('y','h','s','t')})
    if retained_A is not None: out['p_A']=retained_A
    return out


def pell(a,k):
    """Independent binary powering in Z[s]/(s^2-a^2+1)."""
    d=a*a-1
    def times(p,q): return p[0]*q[0]+d*p[1]*q[1],p[0]*q[1]+p[1]*q[0]
    out=(1,0); base=(a,1)
    while k:
        if k&1: out=times(out,base)
        base=times(base,base); k//=2
    return out


def common_index(a,ks):
    pairs=[pell(a,k) for k in ks]; D=prod(y for x,y in pairs); modulus=4*D*D
    x,y=1,0; period=None
    for j in range(1,1000001):
        x,y=(a*x+(a*a-1)*y)%modulus,(x+a*y)%modulus
        if (x,y)==(1,0): period=j; break
    need(period is not None,'finite test period budget')
    U,V=pell(a,period)
    need(U%modulus==1 and V%modulus==0,'period lift')
    b=((1-a)*pow(U,-1,4*D))%(4*D)
    if b==0: b+=4*D
    B=a+U*b
    q=(B-1)//(4*D)-1
    need(q>=0 and B==1+4*D*(q+1),'CRT base')
    return pairs,U,V,b,B,q,D,period


def full_one_power_fixture(n,negative=False):
    k=1;m=n;W=2+n+k+m
    if negative:
        alpha,beta=pell(W+1,4*W)
        need(alpha%4==1 and beta%W==0,'negative fixture congruences')
        aux={'z':beta//W-1,'U':alpha,'v':0,'q':(alpha-5)//4,'b':2,
             'local':[{'y':0,'h':0,'s':2,'t':0}]}
    else:
        A,beta=pell(W+1,W)
        U,V=pell(A,2)
        b=((1-A)*pow(U,-1,4))%4
        if b==0:b=4
        B=A+U*b
        aux={'z':beta//W-1,'U':U,'v':V-1,'q':(B-1)//4-1,'b':b,
             'local':[{'y':0,'h':0,'s':b,'t':0}]}
    return [(n,k,m)],aux


def independent_tiling_ports(obj,env,mod):
    """Separately transcribed modular evaluator of the inherited packed circuit."""
    tiles=obj['tiles'];k=len(tiles);C=obj['constants']['C'];D=obj['constants']['D'];A0=obj['constants']['A0']
    Q=env['Q'];G=env['g']+1;Z=env['Z'];P=1+(C-1)*G;H=A0*P
    R=D*pow(P,3,mod)%mod;B=(D//2)*pow(P,3,mod)%mod;L=pow(R,2*k,mod)
    coeff=[[],[],[],[],[],[],[]]
    for tile in tiles:
        w,e,n,s=[tile[name] for name in ['west','east','north','south']]
        for row,value in zip(coeff,[1,(Q-1)*(w==0),Q*(w==0)-C*(e==0),C*e-w,Q*s-n,-(C-1)*(n==0),Q*(s==0)-P*(n==0)]):
            row.append(value)
    cc=[-G,1-P,0,0,0,Q-1,0]
    F=[]
    for aa,constant in zip(coeff,cc):
        K=sum((H+a)*pow(R,k-1-i,mod) for i,a in enumerate(aa))
        F.append((K*Z+(B-H*G+constant)*pow(R,k-1,mod))%mod)
    F[-1]=(F[-1]+Q*pow(D,2*k,2*mod)//2*pow(P,6*k-1,mod))%mod
    M0=G*sum(pow(R,i,mod) for i in range(k))
    M1=pow(R,2*k-1,mod)-1-(R-1-B)*pow(R,k-1,mod)
    Mt=L-1-(R-1-B)*pow(R,k-1,mod)
    A=(M0+M1*sum(pow(L,j,mod) for j in range(1,7))+Mt*pow(L,7,mod))%mod
    Y=(Z+sum(f*pow(L,j,mod) for j,f in enumerate(F,1)))%mod
    n=(A+1)*Y%mod;d=P*(n+env['v0']+1)%mod;e=d*(env['u']+env['t']+1)%mod
    W0=(e*(2*env['q0']+1)+d*env['u']+1)%mod
    sync=(e-1-(d-1)*(Y+(d-1)*env['j']))%mod
    return [(2,n,e),((d+1)%mod,A,W0)],sync


def main():
    rng=random.Random(2026102414);records={};checks=0
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    for name,digest in pins['sources'].items():
        need(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest,'source pin '+name)
    artifacts={name:json.loads((HERE/name).read_text()) for name in
               ['POWER_ONE_9AUX.json','POWER_TWO_13AUX.json','POWER_TWO_14AUX.json','FOUR_CORNER_21NAT.json','FOUR_CORNER_22NAT.json']}
    for name,obj in artifacts.items():
        degrees=degree_ledger(obj)
        need(degrees[obj['output']]==obj['degree_upper_bound'],'full degree binding '+name)
        need(obj['special_function_graphs']==[],'no hidden graph '+name)
        need(sorted({n['name'] for n in obj['nodes'] if n['op']=='var'})==obj['variables'],'whole coordinate ledger '+name)
        need(len(obj['variables'])==obj['variable_count'],'count '+name)
        for _ in range(100):
            env={n:rng.randrange(0,12) for n in obj['variables']}
            for mod in [101,1009,65537]:
                values=evaluate(obj,env,mod)
                aux={n:env['p_'+n] for n in ('z','U','v','q','b')}
                r=obj.get('request_count',2)
                aux['local']=[{n:env['p_'+n+str(i)] for n in ('y','h','s','t')} for i in range(r)]
                if 'tiles' in obj:requests,sync=independent_tiling_ports(obj,env,mod)
                else:requests=[tuple(env[n+str(i)] for n in ('n','k','m')) for i in range(r)];sync=None
                expected,_=rows(requests,aux,env.get('p_A'))
                if sync is not None:expected['synchronization']=sync
                need(set(expected)==set(obj['residuals']),'whole residual ledger')
                for label,idx in obj['residuals'].items():
                    need(values[idx]==expected[label]%mod,'independent residual '+label+' '+name)
                need(values[obj['output']]==sum(x*x for x in expected.values())%mod,'whole SOS identity')
                checks+=1
        records[name]={'modular_full_polynomial_checks':300,'degree_upper_bound':obj['degree_upper_bound'],'variables':obj['variable_count']}
    # Exact degree attainment on the diagonal. Forward differences compute
    # the leading coefficient of this univariate specialization independently.
    for name in ['POWER_ONE_9AUX.json','POWER_TWO_13AUX.json']:
        obj=artifacts[name];degree=obj['degree_upper_bound']
        vals=[evaluate(obj,{n:t for n in obj['variables']})[obj['output']] for t in range(degree+2)]
        for _ in range(degree):vals=[b-a for a,b in zip(vals,vals[1:])]
        need(len(vals)==2 and vals[0]==vals[1] and vals[0]!=0,'exact generic degree attainment')
        need(vals[0]%factorial(degree)==0,'integral diagonal coefficient')
        records[name]['diagonal_leading_coefficient']=vals[0]//factorial(degree)
    fixtures=[]
    for negative in [False,True]:
        for n in range(1,9):
            requests,aux=full_one_power_fixture(n,negative)
            rr,ports=rows(requests,aux)
            need(all(v==0 for v in rr.values()),'full constructive power fixture')
            obj=artifacts['POWER_ONE_9AUX.json'];env=env_for(requests,aux)
            need(evaluate(obj,env)[obj['output']]==0,'fixture exact DAG')
            need((ports['A']<0)==negative,'fixture branch')
            changed=deepcopy(aux);changed['local'][0]['h']+=1
            need(any(v!=0 for v in rows(requests,changed)[0].values()),'witness mutation rejection')
            fixtures.append({'n':n,'k':1,'negative_A':negative,'largest_witness_bits':max(v.bit_length() for v in env.values())})
    # CRT/index subsystem checks with genuinely different indices. The scale
    # row is deliberately excluded because here A is chosen small for testing.
    crt=[]
    for a,ks in [(2,[1]),(2,[1,2]),(2,[2,3]),(3,[1,2]),(3,[2,3])]:
        pairs,U,V,b,B,q,D,period=common_index(a,ks)
        requests=[];local=[]
        for k,(X,Y) in zip(ks,pairs):
            n=min(2,a-1);m=n**k;S,R=pell(B,k)
            h=sum(n**(k-1-j)*pell(a,j)[1] for j in range(k))
            requests.append((n,k,m))
            local.append({'y':Y-k,'h':h,'s':(S-X)//U,'t':(R-k)//(4*Y)})
            need((S-X)%U==0 and (R-k)%(4*Y)==0,'CRT quotient integrality')
        aux={'z':0,'U':U,'v':V//(D*D)-1,'q':q,'b':b,'local':local}
        rr,pp=rows(requests,aux)
        need(pp['A']==a and all(v==0 for key,v in rr.items() if key!='scale'),'whole shared index and power subsystem')
        crt.append({'A':a,'indices':ks,'period':period,'largest_UV_bits':max(U.bit_length(),V.bit_length())})
    # The key signed-base factorization obstruction, exhaustive on a finite box.
    negative_candidates=0;negative_zeros=0
    for alpha in range(2,60):
        for n in range(1,8):
            tau=2*alpha*n+n*n+1
            for m in range(alpha):
                for Y in range(1,alpha):
                    X=-(alpha+n)*Y+m
                    negative_candidates+=1
                    if X*X-(alpha*alpha-1)*Y*Y==1:
                        negative_zeros+=1;need(Y==1 and m==n,'negative-base classification')
    # Format corruptions cannot pass the ordinary-polynomial validator.
    rejected=0
    for op in ['pow_variable','binomial','pell_graph']:
        bad=deepcopy(artifacts['POWER_ONE_9AUX.json']);bad['nodes'][-1]={'op':op}
        try:evaluate(bad,{n:1 for n in bad['variables']})
        except RuntimeError:rejected+=1
        else:raise RuntimeError('hidden operation not rejected')
    result={'status':'PASS','python_optimized':not __debug__,'scope':'Finite exact checks; universal proof is PROOF.md, not established by enumeration.',
            'source_files_authenticated':len(pins['sources']),'full_modular_polynomial_checks':checks,
            'artifacts':records,'full_positive_and_negative_fixtures':fixtures,'shared_index_fixtures':crt,
            'negative_base_candidates':negative_candidates,'negative_base_norm_zeros':negative_zeros,
            'nonpolynomial_mutations_rejected':rejected,'witness_mutations_rejected':len(fixtures)}
    filename='CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json'
    (HERE/filename).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
