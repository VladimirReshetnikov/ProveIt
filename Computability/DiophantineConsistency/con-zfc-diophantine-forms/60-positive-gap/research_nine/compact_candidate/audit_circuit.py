#!/usr/bin/env python3
"""Independent audit of the compact nine-variable circuits.

Reads only JSON and authenticated integer payloads; never imports the builder.
Exact finite checks and symbolic identities are distinguished from modular
implementation diagnostics. This does not certify the inherited semantic
compiler or decide consistency.
"""
from pathlib import Path
from collections import Counter
import argparse, gzip, hashlib, json, random

ROOT=Path(__file__).resolve().parent
VARIABLES=['b','g','h','s','w','C','i','j','n']
PORTS=['beta','K0','MC','MF']
BITS=[590069,592884,590069,590070]
MEXP=1182955
KAPPA=1182967
CEXP=9463725

def require(ok,why):
    if not ok: raise ValueError(why)

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def add(a,b,sgn=1):
    z=dict(a)
    for e,c in b.items():z[e]=z.get(e,0)+sgn*c
    return {e:c for e,c in z.items() if c}

def mul(a,b):
    z={}
    for e,c in a.items():
        for f,d in b.items():
            k=tuple(x+y for x,y in zip(e,f));z[k]=z.get(k,0)+c*d
    return {e:c for e,c in z.items() if c}

class Polynomial:
    """Small exact sparse polynomial ring used only for tail identities."""
    def __init__(self,n,terms=None):self.n=n;self.terms=terms or {}
    @classmethod
    def constant(cls,n,v):return cls(n,{(0,)*n:v} if v else {})
    @classmethod
    def variable(cls,n,i):return cls(n,{tuple(int(j==i) for j in range(n)):1})
    def coerce(self,x):return x if isinstance(x,Polynomial) else self.constant(self.n,x)
    def __add__(self,x):return Polynomial(self.n,add(self.terms,self.coerce(x).terms))
    __radd__=__add__
    def __neg__(self):return Polynomial(self.n,{e:-c for e,c in self.terms.items()})
    def __sub__(self,x):return self+-self.coerce(x)
    def __rsub__(self,x):return self.coerce(x)+-self
    def __mul__(self,x):return Polynomial(self.n,mul(self.terms,self.coerce(x).terms))
    __rmul__=__mul__
    def __pow__(self,e):
        z=self.constant(self.n,1)
        for _ in range(e):z=z*self
        return z

def symbolic_tail_checks():
    P,K,D,k,G,H,E,O,V0,V1,a0,b1,J,n,W,C=[Polynomial.variable(16,i) for i in range(16)]
    identities={}
    identities['first_Pell_majorant']=(P*K)**2-((P**2-1)*K**2+1)-(K**2-1)
    F=k**2*D**2*(D-1)+1
    Tp=k*(8*D**2-4*D-1)
    err=(8*D+1)*k**2-64*D
    identities['paired_Pell_majorant']=Tp**2-64*D*F-err
    I=(G**2-1)*H**2+1
    delta=err*(G*H)**2+64*D*F*(H**2-1)
    identities['radicand_defect']=(Tp*G*H)**2-64*D*F*I-delta
    theta=E-O*(V0+V1)
    expanded=E**2-2*E*O*(V0+V1)+O**2*((V0**2-a0)+(V1**2-b1)+2*V0*V1)
    identities['inner_norm_cancellation']=theta**2-O**2*(a0+b1)-expanded
    Q=3*W*C-2*(W**2-1)
    identities['positive_numerator']=J*(n+W**2)+Q-(J*n+(J-2)*W**2+3*W*C+2)
    A0,C0,k0=[Polynomial.variable(3,i) for i in range(3)]
    D0=(A0**2-1)*C0**2+1
    identities['paired_F_substitution']=(A0**2-1)*(k0*D0*C0)**2+1-(k0**2*D0**2*(D0-1)+1)
    for name,p in identities.items():require(not p.terms,'Symbolic identity failed: '+name)
    return list(identities)

def fragment_check(body,target,boundaries,formula):
    """Extract an actual DAG fragment and compare its exact small polynomial."""
    names=body['named_nodes'];n=len(boundaries)
    atoms={name:Polynomial.variable(n,i) for i,name in enumerate(boundaries)}
    cache={names[name]:atom for name,atom in atoms.items()}
    require(len(cache)==n,'Aliased fragment boundary')
    def visit(index):
        if index in cache:return cache[index]
        node=body['nodes'][index];kind=node['kind']
        if kind=='literal':out=Polynomial.constant(n,node['value'])
        else:
            require(kind in ('add','sub','mul'),'Uncut fragment input at '+target)
            lhs,rhs=visit(node['left']),visit(node['right'])
            out=lhs+rhs if kind=='add' else lhs-rhs if kind=='sub' else lhs*rhs
        cache[index]=out;return out
    require(visit(names[target]).terms==formula(atoms).terms,'Exact DAG fragment '+target)

def exact_tail_graph_checks(body):
    """Connect the small identities to the literal primary/certificate DAGs."""
    checks=[
      ('D',['A','C'],lambda x:(x['A']**2-1)*x['C']**2+1),
      ('E',['k','D','C'],lambda x:x['k']*x['D']*x['C']),
      ('F',['A','E'],lambda x:(x['A']**2-1)*x['E']**2+1),
      ('GH',['G','H'],lambda x:x['G']*x['H']),
      ('I',['GH','H'],lambda x:x['GH']**2-x['H']**2+1),
      ('V0',['P','K'],lambda x:x['P']*x['K']),
      ('a0',['V0','K'],lambda x:x['V0']**2-x['K']**2+1),
      ('a1',['D','F','I'],lambda x:x['D']*x['F']*x['I']),
      ('Tpair',['k','D'],lambda x:x['k']*(8*x['D']**2-4*x['D']-1)),
      ('V1',['Tpair','GH'],lambda x:x['Tpair']*x['GH']),
      ('F9',['inner','Omega','a0','a1'],lambda x:x['inner']**2-256*x['Omega']**4*x['a0']*x['a1'])]
    if body['degree_certificate_form']:
        checks += [
          ('dferror',['D','k'],lambda x:(8*x['D']+1)*x['k']**2-64*x['D']),
          ('Delta1',['dferror','GH','D','F','H'],lambda x:x['dferror']*x['GH']**2+64*x['D']*x['F']*(x['H']**2-1)),
          ('inner',['E0','Omega','V0','V1','K','Delta1'],lambda x:x['E0']**2-2*x['E0']*x['Omega']*(x['V0']+x['V1'])+x['Omega']**2*(x['K']**2-1+x['Delta1']+2*x['V0']*x['V1']))]
    else:
        checks += [
          ('Theta',['E0','Omega','V0','V1'],lambda x:x['E0']-x['Omega']*(x['V0']+x['V1'])),
          ('inner',['Theta','Omega','a0','a1'],lambda x:x['Theta']**2-x['Omega']**2*(x['a0']+64*x['a1']))]
    for target,boundaries,formula in checks:fragment_check(body,target,boundaries,formula)
    return [target for target,_,_ in checks]

def common_ancestor_check(primary,certificate):
    """Exact expression fingerprints, normalizing multiplication associativity.

    The two artifacts use different addition chains for powers of the same
    source radix.  Sparse multiplicative normal forms identify those chains
    exactly; this does not use random evaluation or distribute large powers.
    """
    canonical_ids={}
    def intern(value):
        # Exact serialized-key equality, not a probabilistic hash comparison.
        key=json.dumps(value,sort_keys=True,separators=(',',':'))
        if key not in canonical_ids:canonical_ids[key]=len(canonical_ids)
        return canonical_ids[key]
    def fingerprints(body):
        out=[];forms=[]
        for node in body['nodes']:
            kind=node['kind']
            if kind=='mul':
                lc,lf=forms[node['left']];rc,rf=forms[node['right']]
                scalar=lc*rc;factors=dict(lf)
                for key,power in rf.items():factors[key]=factors.get(key,0)+power
                if not factors:key=intern({'kind':'literal','value':scalar})
                elif scalar==1 and len(factors)==1 and list(factors.values())==[1]:key=next(iter(factors))
                else:key=intern(['product',scalar,sorted(factors.items())])
                form=(scalar,factors)
            elif kind=='literal':
                key=intern(node);form=(node['value'],{})
            else:
                payload=[kind,out[node['left']],out[node['right']]] if kind in ('add','sub') else node
                if kind=='add':payload=[kind]+sorted(payload[1:])
                key=intern(payload);form=(1,{key:1})
            out.append(key);forms.append(form)
        return {name:out[index] for name,index in body['named_nodes'].items()}
    require(primary['coefficient_recipes']==certificate['coefficient_recipes'],'Different fixed recipes')
    pa,ca=fingerprints(primary),fingerprints(certificate)
    common=(set(pa)&set(ca))-{'inner','F9'}
    mismatches=sorted(name for name in common if pa[name]!=ca[name])
    require(not mismatches,'Different common ancestors '+','.join(mismatches))
    return len(common)

def load_ports(binding_path):
    binding=json.loads(binding_path.read_text());vals={};rows=[]
    aliases={'beta':'beta','K':'K0','MC':'MC','MF_source':'MF'}
    files=binding['materialization']['files']
    require(set(x['port'] for x in files)==set(aliases),'Incomplete or mixed tuple')
    for f in files:
        path=binding_path.parent/f['file'];compressed=path.read_bytes();raw=gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest()==f['sha256'],'Raw coefficient hash')
        require(hashlib.sha256(compressed).hexdigest()==f['gzip_sha256'],'Compressed coefficient hash')
        value=int.from_bytes(raw,'little');name=aliases[f['port']]
        require(value.bit_length()==f['bits']==BITS[PORTS.index(name)],'Port bit length')
        require(len(raw)==f['raw_bytes'],'Port byte length')
        vals[name]=value;rows.append({'port':name,'bits':f['bits'],'raw_sha256':f['sha256']})
    require(vals['beta']==(1<<590069)-1,'Incorrect beta specialization')
    return vals,{'binding_sha256':digest(binding_path),'raw_ports':rows,'raw_bytes':sum(x['raw_bytes'] for x in files)}

def recipe(terms,ports,modulus=None):
    ans=0
    for t in terms:
        powers=t['powers'];c=t['coefficient']
        require(type(c) is int and len(powers)==4 and all(type(e) is int and e>=0 for e in powers),'Invalid coefficient recipe')
        for name,e in zip(PORTS,powers):c*=pow(ports[name],e,modulus) if modulus else ports[name]**e
        ans+=c
    return ans%modulus if modulus else ans

def coefficients(body,ports,modulus=None):
    values={}
    for row in body['coefficient_recipes']:
        require(row['name'] not in values,'Duplicate coefficient name')
        values[row['name']]=recipe(row['terms'],ports,modulus)
    values['base_scale']=pow(2,KAPPA,modulus) if modulus else 1<<KAPPA
    values['threshold_scale']=pow(2,CEXP,modulus) if modulus else 1<<CEXP
    return values

def graph_check(body):
    require(body['variables']==VARIABLES,'Variable metadata')
    nodes=body['nodes'];seen=[];counts=Counter()
    for i,n in enumerate(nodes):
        kind=n['kind']
        if kind in ('add','sub','mul'):
            require(type(n['left']) is int and type(n['right']) is int and 0<=n['left']<i and 0<=n['right']<i,'DAG order')
            counts[kind]+=1
        elif kind=='variable':seen.append(n['name'])
        else:require(kind in ('literal','fixed'),'Unknown node kind')
    require(seen==VARIABLES,'Missing or extra quantified input')
    require(dict(counts)==body['operation_counts'] and sum(counts.values())==body['total_operations'],'Operation ledger')
    keep=set();stack=[body['output']]
    while stack:
        i=stack.pop()
        if i in keep:continue
        keep.add(i);n=nodes[i]
        if n['kind'] in ('add','sub','mul'):stack.extend((n['left'],n['right']))
    require(keep==set(range(len(nodes))),'Dead gate or unused leaf')
    require(all(type(i) is int and i in keep for i in body['named_nodes'].values()),'Invalid named node')
    return dict(counts)

def metadata_check(body,ports):
    expected={'coherent_tuple':'compact44','W':100,'Kcode':2047,'Ecode':2149,'Hpop':2272,
              'threshold_b_power':1,'threshold_B_power':1128,'block_scale_power_of_two':0,
              'base_scale_exponent':KAPPA,'threshold_scale_exponent':CEXP,'coefficient_bound_exponent':MEXP}
    for key,val in expected.items():require(body[key]==val,'Metadata '+key)
    require(body['port_bit_lengths']==BITS,'Coefficient profile')
    bounds=[]
    for row in body['coefficient_recipes']:
        bnd=sum(abs(t['coefficient'])*(1<<sum(e*bb for e,bb in zip(t['powers'],BITS))) for t in row['terms'])
        bounds.append(bnd)
        require(abs(recipe(row['terms'],ports))<1<<MEXP,'Actual fixed coefficient exceeds bound')
    require(max(bounds).bit_length()==MEXP,'Recipe bound exponent')
    require(KAPPA==MEXP+12 and 2*CEXP==16*KAPPA-22,'Exact constant calibration')
    # Compare coefficient and constant of k, not merely a sample of exponents.
    require(2272*KAPPA-22==2*CEXP+2256*KAPPA,'Threshold constant coefficient')
    require(2272*2-30==2+2256*2,'Threshold k coefficient')

def degree_check(body,certificate,ports):
    """Independent exact diagonal heads, with a,c formal and other ports numeric."""
    fixed=coefficients(body,ports);rows=[]
    for idx,n in enumerate(body['nodes']):
        kind=n['kind']
        if kind=='variable':degree,head=1,{(0,0):1}
        elif kind=='literal':degree,head=0,({(0,0):n['value']} if n['value'] else {})
        elif kind=='fixed':
            degree=0
            head={(1,0):1} if n['name']=='base_scale' else {(0,1):1} if n['name']=='threshold_scale' else {(0,0):fixed[n['name']]}
        else:
            da,ha=rows[n['left']];db,hb=rows[n['right']]
            if kind=='mul':degree,head=da+db,mul(ha,hb)
            elif da>db:degree,head=da,ha
            elif db>da:degree,head=db,({e:-c for e,c in hb.items()} if kind=='sub' else hb)
            else:degree,head=da,add(ha,hb,-1 if kind=='sub' else 1)
            require(bool(head) or degree==0,'Unresolved positive-degree cancellation at node '+str(idx))
        rows.append((degree,head))
    degree,head=rows[body['output']]
    require(degree==certificate['exact_degree']==1797796,'Exact output degree')
    expected={(898488,400):1<<186}
    require(head==expected,'Exact diagonal leading coefficient')
    for name,index in body['named_nodes'].items():
        require(rows[index][0]==certificate['named_degrees'][name],'Named degree '+name)
        encoded=certificate['named_leaders'][name]
        if encoded is not None:
            expected_head={(x['base_scale_power'],x['threshold_scale_power']):int(x['scalar_odd_part'])*(1<<x['scalar_power_of_two']) for x in encoded}
            require(rows[index][1]==expected_head,'Named leading form '+name)
    return {'exact_degree':degree,'leading_coefficient':'2^186 * a^898488 * c^400','named_degree_checks':len(body['named_nodes'])}

def evaluate(body,inputs,ports,p):
    fixed=coefficients(body,ports,p);values=[]
    for n in body['nodes']:
        kind=n['kind']
        if kind=='variable':z=inputs[n['name']]
        elif kind=='literal':z=n['value']
        elif kind=='fixed':z=fixed[n['name']]
        else:
            a,b=values[n['left']],values[n['right']]
            z=a+b if kind=='add' else a-b if kind=='sub' else a*b
        values.append(z%p)
    return values[body['output']],{name:values[i] for name,i in body['named_nodes'].items()}

def direct_formula(v,ports,p,layout,kernels):
    z={}
    def put(name,value):z[name]=value%p;return z[name]
    b,g,h,s,w,C,i,j,n=[v[x] for x in VARIABLES]
    B=put('B',pow(2,KAPPA,p)*b*b)
    dp=[]
    for row in kernels['kernels']:
        dp.append(put('D'+str(row['degree']),sum(recipe(t['coefficient'],ports,p)*pow(B,t['exponent'],p) for t in row['terms'])))
    ell=put('ell',sum(pow(B,e,p) for e in layout['weights']))
    targets=put('targets',sum(pow(B,e,p) for e in layout['targets']))
    N0=put('N0',pow(B,101,p));mask=put('mask',N0-1-(b-1)*ell)
    Us=put('Usource',ell+g);Gs=put('Gsource',dp[2]*Us*Us+dp[1]*Us+dp[0])
    Jc=put('Jcode',2*Gs+targets);Sc=put('Scode',g+N0*Jc);Tc=put('Tcode',mask+N0*(B-2)*targets)
    L=put('L',b*pow(B,2149,p));N=put('N',pow(2,CEXP,p)*b*pow(B,1128,p))
    R=put('R',L*(Sc+Tc+1)-Sc-1);t=put('capbase',b*pow(B,100,p))
    U=put('U',N*N*w);Y=put('Y',N*N*s);M=put('M',R*Y)
    P=put('P',2*M*M*U);K=put('K',R+1+h*(P-1));A=put('A',M*(U+1))
    B1=put('B1',2*R+1);W=put('W1',b*w);put('C',C)
    J=put('J',4*A-5);Q=put('Q',3*W*C-2*(W*W-1))
    D=put('D',(A*A-1)*C*C+1);k=put('k',i*J*C);E=put('E',k*D*C)
    F=put('F',(A*A-1)*E*E+1);G=put('G',A+F*(C*D+1-A))
    H=put('H',C+F*(B1+(j-1)*C));GH=put('GH',G*H);I=put('I',(G*G-1)*H*H+1)
    a0=put('a0',(P*P-1)*K*K+1);a1=put('a1',D*F*I)
    m=put('margin',K*K*(4*t-g)-16*t*(C-K*Y)**2)
    V0=put('V0',P*K);Tp=put('Tpair',k*(8*D*D-4*D-1));V1=put('V1',Tp*GH)
    O=put('Omega',J*m);E0=put('E0',J*(n+W*W)+Q);theta=put('Theta',E0-O*(V0+V1))
    inner=put('inner',theta*theta-O*O*(a0+64*a1));out=put('F9',inner*inner-256*pow(O,4,p)*a0*a1)
    put('dferror',(8*D+1)*k*k-64*D)
    put('Delta1',z['dferror']*GH*GH+64*D*F*(H*H-1))
    put('b',b)
    return out,z

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--binding',type=Path,default=ROOT/'COEFFICIENT_BINDING.json');args=parser.parse_args()
    ports,binding_receipt=load_ports(args.binding)
    layout=json.loads((ROOT/'data/split_code.json').read_text());kernels=json.loads((ROOT/'data/split_kernels.json').read_text())
    require(digest(ROOT/'data/parent_source.json')==layout['source_sha256']==kernels['source_sha256'],'Literal source hash')
    bodies={};audits={}
    for domain in ('positive','natural'):
        for cert in (False,True):
            stem='gap_100_'+domain+('_certificate' if cert else '');path=ROOT/'generated'/f'{stem}.json';body=json.loads(path.read_text())
            bodies[domain,cert]=body;counts=graph_check(body);metadata_check(body,ports)
            require(body['source_sha256']==layout['source_sha256'],'Circuit source identity')
            require(body['layout_sha256']==digest(ROOT/'data/split_code.json'),'Circuit layout identity')
            audits[stem]={'sha256':digest(path),'operations':sum(counts.values()),'operation_counts':counts,'nodes':len(body['nodes'])}
            audits[stem]['exact_tail_fragments']=exact_tail_graph_checks(body)
            if cert:
                certificate=json.loads((ROOT/'generated'/f'{stem}_degree.json').read_text());audits[stem]['degree']=degree_check(body,certificate,ports)
    require(bodies['positive',False]['total_operations']==465 and bodies['natural',False]['total_operations']==472,'Primary frozen operation counts')
    symbolic=symbolic_tail_checks()
    common_counts={domain:common_ancestor_check(bodies[domain,False],bodies[domain,True]) for domain in ('positive','natural')}
    rng=random.Random(51420261023);fixtures=[{x:1 for x in VARIABLES},{x:2 for x in VARIABLES}]+[{x:rng.randrange(1,10000) for x in VARIABLES} for _ in range(20)]
    moduli=[1000000007,1000000009,2147483647];checks=0;named_checks=0
    for p in moduli:
        for v in fixtures:
            expected,names=direct_formula(v,ports,p,layout,kernels)
            for domain in ('positive','natural'):
                inputs=v if domain=='positive' else {x:v[x]-1 for x in VARIABLES}
                for cert in (False,True):
                    value,got=evaluate(bodies[domain,cert],inputs,ports,p)
                    require(value==expected,'Modular full-formula diagnostic')
                    for name,number in got.items():
                        if name in names:require(number==names[name],'Modular register diagnostic '+name);named_checks+=1
                    checks+=1
    receipt={'status':'PASS','whole_tuple':binding_receipt,'circuits':audits,'exact_symbolic_tail_identities':symbolic,
             'primary_certificate_common_ancestor_checks':common_counts,'exact_primary_certificate_identity':True,
             'recipe_bound_exponent':MEXP,'exact_binary_threshold_identity':True,
             'modular_diagnostics':{'moduli':moduli,'positive_fixtures_per_modulus':len(fixtures),'circuit_evaluations':checks,'named_register_comparisons':named_checks,'scope':'Finite implementation diagnostics, not polynomial-identity or unbounded semantic proofs.'},
             'scope':'Exact graph, degree, coefficient binding, coefficient bound, threshold, and small symbolic identity audits. Source extraction is checked separately. Native compiler/Jones semantics are inherited.'}
    path=ROOT/'generated/INDEPENDENT_CIRCUIT_AUDIT.json';path.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
