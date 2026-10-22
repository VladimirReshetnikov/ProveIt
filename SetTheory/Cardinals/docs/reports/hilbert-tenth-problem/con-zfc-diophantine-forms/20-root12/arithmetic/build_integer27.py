#!/usr/bin/env python3
"""Lift the pinned thirteen-coordinate resultant to 27 unrestricted integers.
Every gate is binary +, -, or *, including numeral multiplications.
Finite diagnostics corroborate algebra; they do not establish compiler semantics.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from instance_binding import binding
from collections import Counter
from fractions import Fraction
import json, random, hashlib
HERE=Path(__file__).resolve().parent
SRC=HERE/'sources'/'09-combined13'/'arithmetic'
GUARDED=['Jrep','F','alpha','transport_quotient','s','eta','zeta']
FREE=['h','auxiliary_quotient','gamma','t']
PIN='f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
def require(p,m):
    if not p: raise ValueError(m)
def evaluate(p,values):
    v=dict(values)
    def get(x):return x if type(x) is int else v[x]
    for n,op,a,b in p['source']:
        a,b=get(a),get(b)
        v[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return v
def ledger(p):
    known=set(p['witnesses']+p['fixed_numerals'])
    for n,op,a,b in p['source']:
        require(n not in known,'duplicate register')
        require(op in ['+','-','*'],'invalid op')
        require(all(type(x) is int or x in known for x in [a,b]),'unbound operand')
        known.add(n)
    outputs=[p['output']] if 'output' in p else [x for pair in p['comparisons'] for x in pair]
    need={x for x in outputs if type(x) is str}
    for n,op,a,b in reversed(p['source']):
        require(n in need,'dead gate')
        need.update(x for x in [a,b] if type(x) is str)
    require(set(p['witnesses']+p['fixed_numerals'])<=need,'unused port')
    c=Counter(row[1] for row in p['source'])
    return dict(operations=len(p['source']),multiplications=c['*'],additions_subtractions=c['+']+c['-'],all_gates_live=True,all_ports_live=True)
def lift(name):
    base=json.loads((SRC/name).read_text()); p={k:v for k,v in base.items() if k not in ['source','ledger','degree_diagnostics','residual_exact_degrees','exact_degree','coefficient_binding']}
    src=[]; variables=[]
    for n in GUARDED:
        x,y,z=[n+'_'+t for t in ['x','y','z']]; variables += [x,y,z]
        src += [[n+'_x2','*',x,x],[n+'_y2','*',y,y],[n+'_z2','*',z,z],
                [n+'_tri','+',n+'_x2',x],[n+'_sum2','+',n+'_tri',n+'_y2'],
                [n+'_sum3','+',n+'_sum2',n+'_z2'],[n,'+',n+'_sum3',1]]
    variables += ['odd_i_parameter','square_w_parameter']+FREE
    src += [['twice_i','*',2,'odd_i_parameter'],['i','+','twice_i',1],['w','*','square_w_parameter','square_w_parameter']]
    src += base['source']; p.update(source=src,witnesses=variables,domain='all integers')
    p['historical_source_provenance']={'source_commit':PIN,'recipe':'sources/09-combined13/upstream/06_k215_constants.json','compiler':'original 06-blank67; cell_bits = 5^67; MF is the shifted source mask','note':'This deliberately does not inherit package 09 default T-shape coefficients.'}
    p['historical_source_provenance']['inherited_packet_binding']=base.get('coefficient_binding')
    p['coefficient_binding']=binding(p['fixed_numerals'])
    p['positive_substitution']='Pos(x,y,z) = x*x+x+y*y+z*z+1'
    p['positive_original_coordinates']=GUARDED
    p['odd_original_coordinate']='i=2*odd_i_parameter+1'
    p['square_original_coordinate']='w=square_w_parameter*square_w_parameter'
    p['unrestricted_original_coordinates']=FREE
    if 'comparisons' in p:
        p.update(name='integer27_system130',residual_exact_degrees=[35,13,4,1064],exact_maximum_degree=1064)
    elif name.startswith('sos'):
        p.update(name='integer27_sos141',exact_degree=2128)
    else:
        p.update(name='integer27_product136',exact_degree=1116)
    p['ledger']=ledger(p)
    p['source_sha256']=hashlib.sha256(json.dumps(src,separators=(',',':')).encode()).hexdigest()
    require(len(variables)==27,'wrong dimension')
    require(p['ledger']['operations']==len(base['source'])+52,'wrong count')
    return base,p

def degree_line(p,prime,seed):
    rng=random.Random(seed)
    vals={n:[rng.randrange(1,17),rng.randrange(1,17)] for n in p['witnesses']}
    vals.update({n:[v] for n,v in zip(p['fixed_numerals'],[31,127,10,45])})
    def get(x):return [x] if type(x) is int else vals[x]
    def add(a,b,sgn=1):
        c=[((a[j] if j<len(a) else 0)+sgn*(b[j] if j<len(b) else 0))%prime for j in range(max(len(a),len(b)))]
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    for n,op,a,b in p['source']:
        a,b=get(a),get(b)
        if op=='*':
            c=[0]*(len(a)+len(b)-1)
            for j,x in enumerate(a):
                for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%prime
            while len(c)>1 and c[-1]==0:c.pop()
        else:c=add(a,b,1 if op=='+' else -1)
        vals[n]=c
    if 'output' in p:
        degrees=[len(vals[p['output']])-1]; expected=[p['exact_degree']]
    else:
        degrees=[len(add(get(a),get(b),-1))-1 for a,b in p['comparisons']]; expected=p['residual_exact_degrees']
    require(degrees==expected,('degree mismatch',p['name'],degrees,expected))
    return dict(prime=prime,seed=seed,degrees=degrees)

def substitution_checks(base,p):
    rng=random.Random(27136)
    for j in range(96):
        v={n:rng.randrange(-4,5) for n in p['witnesses']+p['fixed_numerals']}
        lifted=evaluate(p,v)
        orig={n:lifted[n] for n in base['witnesses']+base['fixed_numerals']}
        require(all(orig[n]>0 for n in GUARDED),'positivity failure')
        require(orig['i']%2==1 and orig['w']>=0,'restricted coordinate failure')
        old=evaluate(base,orig)
        require(all(lifted[n]==old[n] for n,_,_,_ in base['source']),'substitution mismatch')
    return 96

def component_checks():
    # Both signs of t, f and y occur in isolated compatible root components.
    count=0
    for rho in [2,3,5]:
        Q=rho*rho; d=Q-1; chi,psi=1,0
        for ell in range(1,6):
            chi,psi=rho*chi+(rho*rho-1)*psi,chi+rho*psi
            if ell not in [3,5]:continue
            V=-chi//rho
            for f in [-3,2,4]:
                D=f*f;v=1;z=v*f-V; M=D+v*v
                for sy in [-1,1]:
                    y=sy*psi
                    for st in [-1,1]:
                        tau=st*100*(z+abs(y)+1);A=tau*tau;t=M*tau+y
                        e=Q*(D*v*v+z*z)-1;B=2*Q*v*z
                        C=d*(t*t+M*M*A)-e
                        U=C*C+D*B*B-4*d*d*t*t*M*M*A
                        require(U*U-D*(2*C*B)**2==0,'root resultant')
                        fr=Fraction(-U,2*C*B); tr=Fraction(C+B*fr,2*d*t*M); yr=t-M*tr
                        require((fr,tr,yr)==(f,tau,y),'root reconstruction')
                        count+=1
    # The integer gap obstruction used for T=0.
    gap_cases=0
    for Q in range(3,80):
        for z in range(2,Q):
            require(z*z-1<(Q-1)*(2*z+1),'gap bound')
            gap_cases+=1
    return dict(signed_root_component_cases=count,gap_inequality_cases=gap_cases)

def main():
    receipt={'status':'PASS','source_commit':PIN,'scope':'Exact circuit/substitution/component and degree diagnostics, not a proof-assistant compiler certificate or a solution-existence computation.','packets':[]}
    for name in ['polynomial13_84.json','system13_78.json','sos13_89.json']:
        b,p=lift(name);checks=substitution_checks(b,p)
        ds=[degree_line(p,1000000007,271),degree_line(p,1000000009,136)]
        p['degree_diagnostics']=ds
        (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        receipt['packets'].append(dict(name=p['name'],variables=len(p['witnesses']),ledger=p['ledger'],substitution_cases=checks,degree_diagnostics=ds))
    receipt['isolated_checks']=component_checks()
    (HERE/'integer27_verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
