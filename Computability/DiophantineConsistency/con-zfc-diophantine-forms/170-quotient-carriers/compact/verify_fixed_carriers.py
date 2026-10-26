#!/usr/bin/env python3
"""Independent exact source/degree/binding audit; Python standard library only.

The finite checks authenticate the delivered objects. They do not replace
the unbounded Pell/refutation proof in FIXED_CARRIER_PROOF.md.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import copy, gzip, hashlib, json, random

ROOT = Path(__file__).resolve().parent
PROFILES = [
    ('fixed_13_residue_70_degree206.json', 'raw', 13, 70, 206, (40,18,12)),
    ('fixed_13_residue_71_degree162.json', 'reduced', 13, 71, 162, (40,18,13)),
    ('fixed_13_residue_q4_72_degree154.json', 'q4', 13, 72, 154, (41,18,13)),
    ('fixed_12_rational_74_degree438.json', 'rational', 12, 74, 438, (42,20,12)),
]
PARENT_DIGESTS = {
    'equation_14_raw.json':'3f1912e0f37fdf8df116698e5a4ae5718d1c743fb7f35239ceb64e6ea97a65db',
    'equation_14_reduced.json':'4793bc610935d3f96b664658d34ec1bc1a3c6a9c7c77d0e2515e8e098daa42ff',
    'equation_13_anchored.json':'84b307586101c5deb9535046301e94ef769e915f5ad25339d1bd956772e0ad5d',
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

class Poly:
    """Exact sparse integer polynomial, with variable names as monomials."""
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = value.terms.copy()
        elif isinstance(value, dict):
            self.terms = {m:c for m,c in value.items() if c}
        else:
            self.terms = {():int(value)} if value else {}

    @staticmethod
    def var(name):
        return Poly({((name,1),):1})

    def __add__(self, other):
        other=Poly(other); out=self.terms.copy()
        for m,c in other.terms.items(): out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__

    def __neg__(self): return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other): return self+-Poly(other)
    def __rsub__(self,other): return Poly(other)+-self

    def __mul__(self,other):
        other=Poly(other); out={}
        for a,x in self.terms.items():
            for b,y in other.terms.items():
                d=dict(a)
                for v,e in b: d[v]=d.get(v,0)+e
                m=tuple(sorted(d.items()));out[m]=out.get(m,0)+x*y
        return Poly(out)
    __rmul__=__mul__

    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'Nonpolynomial exponent')
        out=Poly(1);base=self
        while n:
            if n&1:out=out*base
            n//=2
            if n:base=base*base
        return out

    def __eq__(self,other): return self.terms==Poly(other).terms

    def leading(self, witnesses):
        if not self.terms:return -1,Poly()
        weights={m:sum(e for v,e in m if v in witnesses) for m in self.terms}
        d=max(weights.values())
        return d,Poly({m:c for m,c in self.terms.items() if weights[m]==d})

def operation(op,a,b):
    if op=='+':return a+b
    if op=='-':return a-b
    if op=='*':return a*b
    raise ValueError('Unknown operation '+str(op))

def graph_eval(packet,values,prime=None):
    env=dict(values)
    def get(x):return x if isinstance(x,int) else env[x]
    for name,op,l,r in packet['source']:
        value=operation(op,get(l),get(r))
        env[name]=value if prime is None else value%prime
    return env

def topology(packet, variables, operations, counts):
    inputs=packet['witnesses']+packet['fixed_numerals']
    require(packet['domain']=='strictly positive integers','Changed domain')
    require(len(set(inputs))==len(inputs),'Duplicate input')
    require(len(packet['witnesses'])==variables,'Incorrect variable count')
    require(len(packet['source'])==operations==packet['operations'],'Incorrect gate count')
    actual=Counter(row[1] for row in packet['source'])
    require((actual['*'],actual['+'],actual['-'])==counts,'Incorrect operation breakdown')
    require(dict(actual)==packet['operation_counts'],'Changed count metadata')
    seen=set(inputs); rows={}
    for row in packet['source']:
        require(len(row)==4,'Malformed row')
        name,op,l,r=row
        require(name not in seen,'Duplicate or shadowed register')
        require(op in {'+','-','*'},'Nonpolynomial operation')
        require(all(isinstance(x,int) or x in seen for x in (l,r)),'Forward reference')
        seen.add(name); rows[name]=row
    live=set(); todo=[packet['output']]
    while todo:
        x=todo.pop()
        if isinstance(x,int) or x in live:continue
        live.add(x)
        if x in rows:todo.extend(rows[x][2:])
    require(live==seen,'Dead input or gate')
    return {'all_inputs_live':len(inputs),'all_gates_live':len(rows)}

def exact_cuts(packet,kind):
    # These definitions are written independently of the producer's surgery.
    cuts={
        'qm':'beta*J', 'q':'qm+1', 'q2':'q*q', 'q3':'q2*q',
        'X':'w*q', 'Y':'s*q3', 'E':'X*Y', 'k':'eta+zeta',
        'ell':'E*k*Y', 'A':'1+ell*(ell+k)', 'c':'k*Y+eta',
        'a':'E+Y', 'H':'4*a+3', 'Delta':'a*a+H',
        'main_root':'X+a*c+gamma*H', 'c2':'c*c', 'Dc2':'Delta*c2',
        'N1':'main_root*main_root-Dc2', 'qF':'q-F', 'C':'qF-alpha',
        'R':'(qm*qF+alpha)*(q2-1)+(MC+q*MF)*J',
        'Nt':'(K0+w)*C+qF-z*qm',
        'V':'f2*(c*T-R)-c',
    }
    if kind=='rational':
        cuts.update(t='E*n+k-R-1',mult='i*(a+2)*main_root',
                    S0='mult*Dc2',I='mult*c2',W='A*I*S0',f2='1+W',
                    Q='Delta*W',G='A*f2',
                    Eprod='Q*(t*t-E*E*G*V*V)-t*t+E*E*G',
                    output='N1*Nt*(3*Eprod+1)-1')
    else:
        cuts.update(t=('q2*q2*n-k+R' if kind=='q4' else 'E*n-k+R'),
                    carrier_i=('q2*i' if kind=='q4' else 'E*i'),
                    f2='f*f',Ns='f2-W',
                    Eprod='Q*(t*t-A*V*V)-t*t+A',
                    output='N1*Nt*(3*Eprod+1)*Ns-1')
        if kind=='raw':
            cuts.update(I='carrier_i*c2',S0='carrier_i*Dc2',W='A*I*S0',Q='Delta*W')
        else:
            cuts.update(iA='carrier_i*A',S='iA*Dc2',I='iA*c2',W='I*S',Q='Delta*(f2-1)')
    names=packet['witnesses']+packet['fixed_numerals']+[r[0] for r in packet['source']]
    symbols={x:Poly.var(x) for x in names}
    env={x:symbols[x] for x in packet['witnesses']+packet['fixed_numerals']}
    cones={x:set() for x in env}; covered=set();checked=[]
    for name,op,l,r in packet['source']:
        a=Poly(l) if isinstance(l,int) else env[l]
        b=Poly(r) if isinstance(r,int) else env[r]
        env[name]=operation(op,a,b)
        cones[name]={name}|(set() if isinstance(l,int) else cones[l])|(set() if isinstance(r,int) else cones[r])
        if name in cuts:
            expected=eval(cuts[name],{'__builtins__':{}},symbols)
            require(env[name]==expected,'Exact formula mismatch at '+name)
            covered|=cones[name]; env[name]=symbols[name];cones[name]=set();checked.append(name)
    require(covered=={r[0] for r in packet['source']},'Formula cones miss a gate')
    require(set(checked)==set(cuts),'A specified formula cut was not reached')
    return {'exact_polynomial_cuts':len(checked),'covered_gates':len(covered)}

def degrees_and_leader(packet,kind,degree):
    variables=set(packet['witnesses'])
    names=packet['witnesses']+packet['fixed_numerals']
    sy={x:Poly.var(x) for x in names}
    rows={r[0]:r for r in packet['source']}
    full_cache=dict(sy)
    def full(name):
        if isinstance(name,int):return Poly(name)
        if name not in full_cache:
            _,op,l,r=rows[name];full_cache[name]=operation(op,full(l),full(r))
        return full_cache[name]
    # Unroll the actual complete main-norm cone, including its cancellation.
    norm=full('N1')
    q=sy['beta']*sy['J']+1;X=sy['w']*q;Y=sy['s']*q**3
    a=X*Y+Y;c=(sy['eta']+sy['zeta'])*Y+sy['eta'];H=4*a+3
    Z=X+sy['gamma']*H
    require(norm==2*a*c*Z+Z**2-H*c**2,'Main-norm cancellation identity failed')
    env={x:sy[x].leading(variables) for x in names}
    register_degrees={}
    for name,op,l,r in packet['source']:
        if name=='N1':
            value=norm.leading(variables)
        else:
            da,pa=(0,Poly(l)) if isinstance(l,int) else env[l]
            db,pb=(0,Poly(r)) if isinstance(r,int) else env[r]
            if op=='*':value=(da+db,pa*pb)
            elif da>db:value=(da,pa)
            elif db>da:value=(db,pb if op=='+' else -pb)
            else:
                p=operation(op,pa,pb)
                require(bool(p.terms),'Unaccounted leading cancellation at '+name)
                value=(da,p)
        env[name]=value;register_degrees[name]=value[0]
    q0=sy['beta']*sy['J'];k0=sy['eta']+sy['zeta']
    e0=sy['w']*sy['s']*q0**4;c0=k0*sy['s']*q0**3
    A0=(sy['w']*sy['s']**2*k0*q0**7)**2
    Lt=sy['w']*(q0-sy['F']-sy['alpha'])-sy['z']*q0
    if kind=='raw':
        leader=24*sy['gamma']*sy['i']**4*A0**3*e0**12*c0**11*sy['f']**4*sy['T']**2*Lt
        target={'J':124,'w':18,'s':35,'eta':17,'i':4,'f':4,'T':2,'gamma':1,'z':1,'beta':124}; coefficient=-24
    elif kind=='reduced':
        leader=24*sy['gamma']*sy['i']**2*A0**3*e0**8*c0**7*sy['f']**6*sy['T']**2*Lt
        target={'J':96,'w':14,'s':27,'eta':13,'i':2,'f':6,'T':2,'gamma':1,'z':1,'beta':96}; coefficient=-24
    elif kind=='q4':
        leader=24*sy['gamma']*sy['i']**2*A0**3*e0**6*c0**7*sy['f']**6*sy['T']**2*q0**4*Lt
        target={'J':92,'w':12,'s':25,'eta':13,'i':2,'f':6,'T':2,'gamma':1,'z':1,'beta':92}; coefficient=-24
    else:
        leader=-24*sy['gamma']*sy['i']**8*A0**5*e0**30*c0**27*sy['T']**2*Lt
        target={'J':272,'w':40,'s':77,'eta':37,'i':8,'T':2,'gamma':1,'z':1,'beta':272}; coefficient=24
    actual_degree,actual_leader=env[packet['output']]
    require(actual_degree==degree==packet['exact_degree'],'Incorrect exact degree')
    require(actual_leader==leader,'Complete homogeneous leader mismatch')
    require(leader.terms.get(tuple(sorted(target.items())))==coefficient,'Distinguished coefficient missing')
    return {'exact_degree':degree,'leading_terms':len(leader.terms),
            'nonzero_coefficient_multiplier':coefficient,'beta_exponent':target['beta'],
            'monomial':{x:e for x,e in target.items() if x!='beta'},
            'register_degrees':{x:register_degrees[x] for x in ['N1','Nt','W','Q','V','Eprod']}}

def formula(v,kind):
    J,F,alpha,z,n,i,T,s,w,eta,zeta,gamma=(v[x] for x in ['J','F','alpha','z','n','i','T','s','w','eta','zeta','gamma'])
    beta,K0,MC,MF=(v[x] for x in ['beta','K0','MC','MF'])
    q=beta*J+1;C=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y
    k=eta+zeta;ell=E*k*Y;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=(a+2)**2-1
    D=X+a*c+gamma*H;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    N1=D*D-Delta*c*c;Nt=(K0+w)*C+(q-F)-z*(q-1);A=1+ell*(ell+k)
    if kind=='rational':
        m=(a+2)*D*i;I=m*c*c;W=Delta*A*I*I;f2=1+W;Q=Delta*W
        G=A*f2;V=f2*(c*T-R)-c;Z=E*n+k-R-1
        B=(Q-1)*Z*Z-E*E*G*(Q*V*V-1)
        return N1*Nt*(3*B+1)-1
    f=v['f'];scale=q*q if kind=='q4' else E;modulus=q**4 if kind=='q4' else E
    I=scale*i*c*c
    if kind=='raw':W=Delta*A*I*I;Q=Delta*W
    else:I=A*I;W=Delta*I*I;Q=Delta*(f*f-1)
    Ns=f*f-W;V=f*f*(c*T-R)-c;t=modulus*n-k+R
    B=(Q-1)*t*t-A*(Q*V*V-1)
    return N1*Nt*(3*B+1)*Ns-1

def coefficient_check():
    binding=json.loads((ROOT/'COEFFICIENTS.json').read_text());values={};receipts=[]
    for name,meta in binding['ports'].items():
        compressed=(ROOT/'coefficients'/meta['file']).read_bytes();raw=gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Wrong raw coefficient '+name)
        require(hashlib.sha256(compressed).hexdigest()==meta['gzip_sha256'],'Wrong gzip byte payload '+name)
        value=int.from_bytes(raw,'little');values[name]=value
        require(value.bit_length()==meta['bits'],'Wrong coefficient bitlength')
        require(value.to_bytes((value.bit_length()+7)//8,'little')==raw,'Noncanonical integer bytes')
        receipts.append({'port':name,'raw_bytes':len(raw),'raw_sha256':meta['raw_sha256']})
    require(sum(x['raw_bytes'] for x in receipts)==295388,'Wrong total coefficient payload')
    beta,K0,MC,MF=(values[x] for x in ['beta','K0','MC','MF'])
    require(beta>=31 and beta%2==1 and K0>0 and 0<MC<beta<MF<2*beta,'Coefficient hypotheses fail')
    return binding,values,receipts

def scalar_and_parent_checks(packet,kind,values):
    parent=json.loads((ROOT/packet['parent']).read_text());rng=random.Random(20261025)
    checks=0
    for prime in [1000000007,1000000009,2147483647]:
        constants={k:v%prime for k,v in values.items()}
        for sample in range(12):
            v={x:rng.randrange(-5,8) for x in packet['witnesses']};v.update(constants)
            env=graph_eval(packet,v,prime)
            require(env[packet['output']]==formula(v,kind)%prime,'Independent scalar formula mismatch')
            if env['E']==0:continue
            old={x:v[x] for x in parent['witnesses'] if x in v};old.update(constants);old['h']=3
            if kind=='rational':
                old['t']=env['t']*pow(env['E'],-1,prime)%prime
            else:
                old['i']=v['i']*(env['q2'] if kind=='q4' else env['E'])%prime
                old['t']=env['t']
            pe=graph_eval(parent,old,prime)
            for name in ['N1','Nt','W','Q','V']:
                require(pe[name]==env[name],'Parent register relation failed at '+name)
            if kind=='rational':
                require(env['Eprod']==env['E']**2*pe['Eprod']%prime,'Cleared rational residual mismatch')
            else:
                require(env['Eprod']==pe['Eprod'],'Residue substitution mismatch')
                require((pe[parent['output']]+1-pe['Nk']*(env[packet['output']]+1))%prime==0,'Deleted-factor identity mismatch')
            checks+=1
    return {'actual_coefficient_modular_samples':checks,'signed_polynomial_inputs':True}

def parent_bindings(packet,binding):
    path=ROOT/packet['parent'];raw=path.read_bytes();digest=hashlib.sha256(raw).hexdigest()
    require(digest==packet['parent_sha256'],'Frozen parent hash mismatch')
    # The three parent digests are also checked against a separate manifest.
    expected=json.loads((ROOT/'FIXED_PARENT_MANIFEST.json').read_text())
    require(expected==PARENT_DIGESTS,'Frozen-parent manifest changed')
    require(digest==expected[path.name],'Unexpected frozen parent')
    require(packet['coefficient_binding']['ports']=={
        k:{n:x for n,x in m.items() if n!='gzip_sha256'} for k,m in binding['ports'].items()
    },'Source has a different fixed tuple')
    return {'parent':packet['parent'],'parent_sha256':digest}

def negative_controls(packets):
    caught=[]
    for label,alter,check in [
        ('reachable arithmetic mutation',lambda p:p['source'][-1].__setitem__(3,2),lambda p:exact_cuts(p,'raw')),
        ('degree metadata mutation',lambda p:p.__setitem__('exact_degree',207),lambda p:degrees_and_leader(p,'raw',206)),
        ('operation metadata mutation',lambda p:p.__setitem__('operations',69),lambda p:topology(p,13,70,(40,18,12))),
    ]:
        p=copy.deepcopy(packets[0]);alter(p)
        try:check(p)
        except ValueError:caught.append(label)
        else:raise ValueError('Negative control escaped: '+label)
    return caught

def main():
    binding,values,coefficient_receipts=coefficient_check();out=[];packets=[]
    for name,kind,n,ops,degree,counts in PROFILES:
        packet=json.loads((ROOT/name).read_text());packets.append(packet)
        receipt={'file':name,'sha256':hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),
                 'variables':n,'operations':ops,'operation_counts':dict(zip(['*','+','-'],counts))}
        receipt.update(topology(packet,n,ops,counts));receipt.update(exact_cuts(packet,kind))
        receipt.update(degrees_and_leader(packet,kind,degree));receipt.update(parent_bindings(packet,binding))
        receipt.update(scalar_and_parent_checks(packet,kind,values));out.append(receipt)
    result={'status':'pass','profiles':out,'coefficients':coefficient_receipts,
            'negative_controls_rejected':negative_controls(packets),
            'scope':'Exact source, topology, local integer-polynomial identities, full homogeneous leaders, fixed-byte bindings, and finite formula/substitution samples. The unbounded consistency equivalence is the separate ordinary proof.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
