#!/usr/bin/env python3
"""New, local circuit emitter. Inert JSON input only; no upstream program execution."""
from pathlib import Path
from fractions import Fraction
import json, random, hashlib
HERE = Path(__file__).resolve().parent
PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'
BASE = json.loads((HERE/'upstream/retained16_system59.json').read_text())

class Poly:
    def __init__(self, terms=None): self.t = terms or {}
    @staticmethod
    def literal(x): return Poly({(): x}) if x else Poly()
    @staticmethod
    def var(x): return Poly({((x,1),):1})
    def __add__(self,b):
        o=dict(self.t)
        for m,c in b.t.items():
            o[m]=o.get(m,0)+c
            if not o[m]: del o[m]
        return Poly(o)
    def __sub__(self,b): return self+Poly({m:-c for m,c in b.t.items()})
    def __mul__(self,b):
        o={}
        for m,c in self.t.items():
            for n,d in b.t.items():
                z=dict(m)
                for v,e in n:z[v]=z.get(v,0)+e
                k=tuple(sorted(z.items()));o[k]=o.get(k,0)+c*d
        return Poly({k:v for k,v in o.items() if v})
    def degree(self, variables):
        return max((sum(e for v,e in m if v in variables) for m in self.t),default=-1)

def evaluate(p,env):
    e=dict(env)
    def get(x): return x if type(x) is int else e[x]
    for out,op,a,b in p['source']:
        av,bv=get(a),get(b)
        e[out]=av+bv if op=='+' else av-bv if op=='-' else av*bv
    return e

def make(name, lifts=(), auxiliary_gap=False):
    rows=[];comparisons=[list(v) for v in BASE['comparisons']]
    witnesses=list(BASE['witnesses'])
    if auxiliary_gap:witnesses[witnesses.index('y')]='e'
    # The source gate producing r becomes r_calc; r is a new independent witness.
    # Its operands still refer to earlier lifted inputs, not to their calculated gates.
    for out,op,a,b in BASE['source']:
        if auxiliary_gap and out=='y2':continue
        if auxiliary_gap and out=='V2':
            rows += [['y','+','V','e'],['y2','*','y','y']]
        if out in lifts:
            witnesses.append(out);rows.append([out+'_calc',op,a,b]);comparisons.append([out,out+'_calc'])
        else: rows.append([out,op,a,b])
    p=dict(name=name,witness_domain='strictly positive integers',witnesses=witnesses,
        fixed_numerals=BASE['fixed_numerals'],source=rows,comparisons=comparisons,
        positive_lifts=list(lifts),auxiliary_gap=auxiliary_gap,source_commit=PIN,
        upstream_file='22-monic12/data/retained16_system59.json',
        coefficient_binding='COEFFICIENT_BINDING.json',
        selected_coefficient_variant='wang943-mixed-radix4-zero-fields-5pow9',
        coefficient_port_map={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
        binding_note='All four fixed integers use the mixed-radix 943 tuple in sibling coefficients; MF_source=MF_native+B-1. No mixture with historical fallbacks is permitted.')
    return p

def formula(p,e):
    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,gamma=[e[n] for n in ['J','F','alpha','z','f','h','i','o','j','s','w','tau','eta','zeta','gamma']]
    beta,K,MC,MF=[e[n] for n in ['beta','K0','MC','MF']]
    q=beta*J+1;X=w*q
    targets={}
    def lift(n,x):
        if n in p['positive_lifts']:targets[n]=x;return e[n]
        return x
    Y=lift('Y',s*q**3);E=lift('E',X*Y);k=eta+zeta;kY=lift('kY',k*Y)
    L=lift('Lfirst',E*kY);c=lift('c',kY+eta);a=E+Y;H=4*a+3;Delta=a*a+H
    D=X+a*c+gamma*H;C=q-F-alpha;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    V=lift('V',o*f-c);U=j*c-R;I=lift('I',i*c*c);A0=lift('A0',Delta*(f*f-1))
    y=V+e['e'] if p['auxiliary_gap'] else e['y']
    res=[tau*tau-L*(L+k)-1,D*D-Delta*c*c-1,A0*(V*V-y*y)+y*y-1,k-h*E-R-1,(K+w)*C-F-z*(q-1),I*I-A0,U-V]
    res += [e[n]-targets[n] for n in p['positive_lifts']]
    return res

def audit(p):
    known=set(p['witnesses']+p['fixed_numerals'])
    for out,op,a,b in p['source']:
        if out in known or op not in ['+','-','*']:raise ValueError('DAG definition')
        if any(type(v) is not int and v not in known for v in [a,b]):raise ValueError('Unbound DAG operand')
        known.add(out)
    live={x for pair in p['comparisons'] for x in pair if type(x) is str}
    for out,op,a,b in reversed(p['source']):
        if out not in live:raise ValueError('Dead gate '+out)
        live.update(x for x in [a,b] if type(x) is str)
    if not set(p['witnesses']+p['fixed_numerals']) <= live:raise ValueError('Dead port')
    p['ledger']=dict(operations=len(p['source']),multiplications=sum(r[1]=='*' for r in p['source']), additions_subtractions=sum(r[1]!='*' for r in p['source']))
    vs={n:Poly.var(n) for n in p['witnesses']+p['fixed_numerals']}
    def get(x):return Poly.literal(x) if type(x) is int else vs[x]
    for out,op,a,b in p['source']:
        av,bv=get(a),get(b);vs[out]=av+bv if op=='+' else av-bv if op=='-' else av*bv
    polynomials=[get(a)-get(b) for a,b in p['comparisons']]
    degrees=[r.degree(set(p['witnesses'])) for r in polynomials]
    p['residual_exact_degrees_formal_ports']=degrees;p['exact_maximum_degree']=max(degrees)
    # Every degree must have a leading term with positive-power beta and no other fixed ports.
    # Such a term survives uniformly for every positive beta and every other fixed tuple.
    cert=[]
    W=set(p['witnesses']); fixed=set(p['fixed_numerals'])
    for r,d in zip(polynomials,degrees):
        groups={}
        for m,c in r.t.items():
            if sum(ex for v,ex in m if v in W)!=d:continue
            wm=tuple((v,ex) for v,ex in m if v in W);fm=tuple((v,ex) for v,ex in m if v not in W)
            groups.setdefault(wm,{})[fm]=c
        safe=[(wm,cf) for wm,cf in groups.items() if len(cf)==1 and all(v=='beta' for fm in cf for v,ex in fm)]
        if not safe:raise ValueError('No uniform leading certificate')
        wm,cf=sorted(safe,key=repr)[0]
        cert.append(dict(witness_monomial=list(wm),coefficient_terms=[dict(monomial=list(fm),coefficient=c) for fm,c in cf.items()]))
    p['uniform_degree_certificates']=cert
    rng=random.Random(2026102301)
    for it in range(160):
        e={v:rng.randrange(-3,5) for v in p['witnesses']+p['fixed_numerals']}
        if it>=80:e={k:Fraction(v,rng.randrange(1,5)) for k,v in e.items()}
        vals=evaluate(p,e)
        def g(x):return x if type(x) is int else vals[x]
        got=[g(a)-g(b) for a,b in p['comparisons']]
        expected=formula(p,e)
        # Source order, not the user's lift tuple order, determines comparison order.
        order=[r[0][:-5] for r in p['source'] if r[0].endswith('_calc')]
        expected=expected[:7]+[expected[7+p['positive_lifts'].index(n)] for n in order]
        if got!=expected:raise ValueError('Independent formula mismatch')
    p['source_sha256']=hashlib.sha256(json.dumps(p['source'],separators=(',',':')).encode()).hexdigest()
    return dict(name=p['name'],variables=len(p['witnesses']),equations=len(p['comparisons']),degree=p['exact_maximum_degree'],residual_degrees=degrees,**p['ledger'],signed_integer_and_rational_cases=160,uniform_degree_proof='Exact symbolic expansion with per-residual monomial coefficient c*beta^r, c nonzero.',all_gates_and_ports_live=True)

def sos(p):
    rows=list(p['source']);rs=[]
    for j,(a,b) in enumerate(p['comparisons']):
        n='residual_'+str(j);s='square_'+str(j);rows += [[n,'-',a,b],[s,'*',n,n]];rs.append(s)
    out=rs[0]
    for j,r in enumerate(rs[1:]):n='sum_'+str(j);rows.append([n,'+',out,r]);out=n
    return dict(name=p['name']+'_sos',witness_domain=p['witness_domain'],witnesses=p['witnesses'],fixed_numerals=p['fixed_numerals'],source=rows,output=out,exact_degree=2*p['exact_maximum_degree'],operations=len(rows),system_dependency=p['name']+'.json',coefficient_binding=p['coefficient_binding'],selected_coefficient_variant=p['selected_coefficient_variant'],coefficient_port_map=p['coefficient_port_map'])

def main():
    cases=[('retained16_auxgap60',(),True),('lift17_Y59',('Y',),False),('lift18_YE59',('Y','E'),False),('lift19_YEc59',('Y','E','c'),False),('lift20_YEcA059',('Y','E','c','A0'),False)]
    results=[]
    for name,lifts,gap in cases:
        p=make(name,lifts,gap);receipt=audit(p);results.append(receipt)
        (HERE/(name+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        q=sos(p);(HERE/(q['name']+'.json')).write_text(json.dumps(q,indent=2)+'\n')
        receipt.update(sum_of_squares_operations=q['operations'],sum_of_squares_degree=q['exact_degree'])
        rng=random.Random(8100)
        for _ in range(100):
            v={x:rng.randrange(-2,4) for x in p['witnesses']+p['fixed_numerals']}
            actual=evaluate(q,v)[q['output']]
            if actual!=sum(x*x for x in formula(p,v)):raise ValueError('SOS formula mismatch')
        receipt['sum_of_squares_identity_cases']=100
    (HERE/'VERIFICATION.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
