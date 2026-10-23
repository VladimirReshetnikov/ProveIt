#!/usr/bin/env python3
"""Replay literal round-eight nine-variable DAGs without importing builders."""
from pathlib import Path
from collections import Counter, defaultdict
import ast, gzip, hashlib, json, random
import sympy as sy
ROOT=Path(__file__).resolve().parents[1]

def expr(text,env):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value)is int:return n.value
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
        if isinstance(n,ast.BinOp):
            a,b=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Pow) and 0<=b<=4:return a**b
        raise ValueError(ast.dump(n))
    return go(ast.parse(text,mode='eval').body)

def fixed_values(obj,ports,p=None):
    out={}
    for rec in obj['coefficient_recipes']:
        value=0
        for term in rec['terms']:
            z=term['coefficient']
            for a,e in zip(ports,term['powers']):z*=pow(a,e,p) if p else a**e
            value+=z
        out[rec['name']]=value%p if p else value
    for name,e in obj['fixed_power_leaves'].items():out[name]=pow(2,e,p) if p else 1<<e
    return out

def run(obj,values,fixed,p):
    out=[]
    for ix,node in enumerate(obj['nodes']):
        k=node['kind']
        if k=='literal':v=node['value'];assert type(v)is int
        elif k=='variable':v=values[node['name']]
        elif k=='fixed':v=fixed[node['name']]
        else:
            assert k in ['add','sub','mul'] and 0<=node['left']<ix and 0<=node['right']<ix
            a,b=out[node['left']],out[node['right']]
            v=a+b if k=='add' else a-b if k=='sub' else a*b
        out.append(v%p)
    return out[obj['output']],{k:out[ix] for k,ix in obj['named_nodes'].items()}

def direct(obj,cert,raw,port_values,p):
    vv=dict(raw)
    if obj['domain']=='positive integers':
        for k in ['phi','j','n']:vv[k]-=1
    else:
        for k in ['b','g','h','s','w','i']:vv[k]+=1
    b,g,h,s,w,phi,i,j,n=(vv[k]%p for k in obj['variables'])
    md=lambda x:x%p
    W=cert['maximum_weight'];Kc=cert['Kcode'];Ep=Kc+W+2;pad=cert['padding_exponent']
    B=md(pow(2,obj['source_parameters']['kappa'],p)*b*b)
    env=dict(zip(cert['ports'],port_values))
    DC=md(sum(expr(t['weighted_coefficient'],env)*pow(B,t['encoding_exponent'],p) for row in cert['rows'] for t in row['terms']))
    ell=md(sum(pow(B,x,p) for x in cert['weights']));targets=md(sum(pow(B,row['target_exponent'],p) for row in cert['rows']))
    N0=pow(B,W+1,p);mask=md(N0-1-(b-1)*ell)
    JC=md(2*(pow(B,pad,p)+g)**2*DC+targets);SC=md(g+N0*JC);TC=md(mask+N0*(B-2)*targets)
    block=md(2*b*pow(B,Ep,p));R=md(block*block+(SC+TC)*block+block-1-SC)
    ndeg=Kc+2*W+10;rem=ndeg%2;power=ndeg//2
    scalar_exp=(15+rem)*obj['source_parameters']['kappa']//2-10
    N=md(pow(2,scalar_exp,p)*pow(B,power,p)*pow(b,rem,p));cap=md(32*b*pow(B,W,p))
    U=md(N*N*w);Y=md(N*N*s);M=md(R*Y);P=md(2*M*M*U);K=md(R+1+h*(P-1));A=md(M*(U+1))
    B1=md(2*R+1);W1=md(b*w);C=md(B1+W1+phi);J=md(4*A-5);Q=md(3*W1*C-2*(W1*W1-1))
    D=md((A*A-1)*C*C+1);kk=md(i*J*C);E=md(kk*D*C);F=md((A*A-1)*E*E+1)
    Lstar=md(C*D+1-A);G=md(A+F*Lstar);H=md(C+F*(B1+j*C));I=md((G*G-1)*H*H+1)
    a0=md((P*P-1)*K*K+1);a1=md(D*F*I);V0=md(P*K)
    margin=md((K*K-4*(C-K*Y)**2)*cap-8*g*K*K)
    if obj['majorant']=='simple64':q=64;V1=md(kk*(8*D*D-4*D-1)*G*H)
    else:
        q=2048**2;ns=md(2*G+Lstar)
        n1=md(2*kk*kk*D*(D-1)*Lstar+3*C);n2=md(2*kk*kk*(D-1)*Lstar)
        n3=md(2*kk*kk*(Lstar-C));n4=md(2*kk*kk*C)
        T6=md(kk*((1024*D*D-512*D-128)*ns-64*n1-40*n2-28*n3-21*n4))
        correction=256*i*(kk*kk+2)+2048 if obj['majorant']=='support2048' else i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048
        V1=md((T6+correction)*H)
    O=md(J*margin);theta=md(J*n+Q-O*(V0+V1));inner=md(theta*theta-O*O*(a0+q*a1))
    out=md(inner*inner-4*q*O**4*a0*a1)
    return out,dict(b=b,B=B,Dcode=DC,ell=ell,targets=targets,N0=N0,mask=mask,Jcode=JC,Scode=SC,Tcode=TC,block_L=block,R=R,N=N,Gcap=cap,
      U=U,Y=Y,M=M,P=P,K=K,A=A,B1=B1,C=C,J=J,Q=Q,D=D,k=kk,E=E,F=F,Lstar=Lstar,G=G,H=H,I=I,a0=a0,a1=a1,V0=V0,V1=V1,m=margin,Omega=O,Theta=theta,inner=inner,F9=out)

def add(a,b,sgn=1):
    out=dict(a)
    for e,v in b.items():out[e]=out.get(e,0)+sgn*v
    return {e:v for e,v in out.items() if v}
def mul(a,b):
    out=defaultdict(int)
    for (x,y),v in a.items():
        for (xx,yy),vv in b.items():out[x+xx,y+yy]+=v*vv
    return {e:v for e,v in out.items() if v}

def heads(obj,small_ports):
    fixed=fixed_values(obj,small_ports);out=[]
    sp=obj['source_parameters'];r=4*sp['E']+2;n=sp['Kcode']+2*sp['W']+10;c=2*sp['W']+1
    # Source identities are checked exactly below. Their degree proof is
    # independent of accidental cancellation inside a homogeneous evaluator:
    # deg S,T<=2E, deg L=2E+1, hence L^2 uniquely leads R. N and cap are
    # explicit monomials. These proven cut-point heads seed the ratio tail.
    known={obj['named_nodes']['R']:(r,{(2*sp['E'],0):4}),
           obj['named_nodes']['N']:(n,{(sp['q'],1):1}),
           obj['named_nodes']['Gcap']:(c,{(sp['W'],0):32})}
    tail_start=max(obj['named_nodes'][key] for key in ['R','N','Gcap'])+1
    for ix,node in enumerate(obj['nodes']):
        kind=node['kind']
        if ix in known:z=known[ix]
        elif kind=='variable':z=(1,{(0,0):1})
        elif kind=='fixed' and node['name']=='radix_scale':z=(0,{(1,0):1})
        elif kind=='fixed' and node['name']=='threshold_scale':z=(0,{(0,1):1})
        elif kind in ['fixed','literal']:
            v=fixed[node['name']] if kind=='fixed' else node['value'];z=(0,{(0,0):v}) if v else (-1,{})
        else:
            da,ca=out[node['left']];db,cb=out[node['right']]
            if ix<tail_start:
                # Upper bounds only here. Never assert these dummy heads are
                # exact; every path into the tail crosses a proven cut point
                # or an unchanged raw input. Source degree bounds are also
                # checked independently from the finite positional data.
                z=(da+db if kind=='mul' else max(da,db),{(0,0):1})
            elif kind=='mul':z=(da+db,mul(ca,cb)) if ca and cb else (-1,{})
            elif da>db:z=(da,ca)
            elif db>da:z=(db,cb if kind=='add' else {e:-v for e,v in cb.items()})
            else:
                cc=add(ca,cb,1 if kind=='add' else -1)
                assert cc or da<=0,('unresolved positive-degree cancellation',ix,kind,da)
                z=(da,cc) if cc else (-1,{})
        out.append(z)
    return out[obj['output']],{k:out[ix] for k,ix in obj['named_nodes'].items()}

def exact_registers(obj,cert):
    """Prove each register identity at named polynomial cut points.

    This is exact algebra, not modular sampling. The cut points are verified
    separately in dependency order, so this covers the entire source tail
    except Dcode, whose finite coefficient-extraction source is audited by
    the independent source checker and exact shared-source verifier.
    """
    symbols={name:sy.Symbol('reg_'+name) for name in obj['named_nodes']}
    variables={name:sy.Symbol('var_'+name) for name in obj['variables']}
    internal=dict(variables)
    if obj['domain']=='positive integers':
        for k in ['phi','j','n']:internal[k]-=1
    else:
        for k in ['b','g','h','s','w','i']:internal[k]+=1
    def check(name,cuts,want):
        if name not in obj['named_nodes']:return 0
        stop={obj['named_nodes'][c]:symbols[c] for c in cuts}
        cache={}
        def walk(ix):
            if ix in stop:return stop[ix]
            if ix in cache:return cache[ix]
            z=obj['nodes'][ix];k=z['kind']
            if k=='variable':v=variables[z['name']]
            elif k=='literal':v=sy.Integer(z['value'])
            elif k=='fixed':v=sy.Symbol('fixed_'+z['name'])
            else:
                a,b=walk(z['left']),walk(z['right']);v=a+b if k=='add' else a-b if k=='sub' else a*b
            cache[ix]=v;return v
        assert sy.expand(walk(obj['named_nodes'][name])-want)==0,('exact register identity',name)
        return 1
    z=lambda k:symbols[k]
    b,g=z('b'),internal['g'];W=cert['maximum_weight'];Kc=cert['Kcode'];E=Kc+W+2;B=z('B');cases=0
    def ck(name,cuts,want):
        nonlocal cases
        cases+=check(name,cuts.split(),want)
    ck('b','',internal['b'])
    ck('B','b',sy.Symbol('fixed_radix_scale')*b*b)
    ck('ell','B',sum(B**w for w in cert['weights']))
    ck('targets','B',sum(B**r['target_exponent'] for r in cert['rows']))
    ck('N0','B',B**(W+1))
    ck('mask','N0 b ell',z('N0')-1-(b-1)*z('ell'))
    ck('Jcode','B Dcode targets',2*(B**cert['padding_exponent']+g)**2*z('Dcode')+z('targets'))
    ck('Scode','N0 Jcode',g+z('N0')*z('Jcode'))
    ck('Tcode','mask N0 B targets',z('mask')+z('N0')*(B-2)*z('targets'))
    ck('block_L','b B',2*b*B**E)
    L,S,T=z('block_L'),z('Scode'),z('Tcode')
    ck('R','block_L Scode Tcode',L*L+(S+T)*L+L-1-S)
    nd=Kc+2*W+10
    ck('N','B b',sy.Symbol('fixed_threshold_scale')*B**(nd//2)*b**(nd%2))
    ck('Gcap','b B',32*b*B**W)
    ck('U','N',z('N')**2*internal['w']);ck('Y','N',z('N')**2*internal['s'])
    ck('M','R Y',z('R')*z('Y'));ck('P','M U',2*z('M')**2*z('U'))
    ck('K','R P',z('R')+1+internal['h']*(z('P')-1));ck('A','M U',z('M')*(z('U')+1))
    ck('B1','R',2*z('R')+1);ww=b*internal['w']
    ck('C','B1 b',z('B1')+ww+internal['phi']);ck('J','A',4*z('A')-5)
    ck('Q','b C',3*ww*z('C')-2*(ww*ww-1))
    ck('D','A C',(z('A')**2-1)*z('C')**2+1);ck('k','J C',internal['i']*z('J')*z('C'))
    ck('L','k D',z('k')*z('D'));ck('E','L C',z('L')*z('C'))
    ck('F','A E',(z('A')**2-1)*z('E')**2+1);ck('Lstar','C D A',z('C')*z('D')+1-z('A'))
    ck('G','A F Lstar',z('A')+z('F')*z('Lstar'));ck('H','C F B1',z('C')+z('F')*(z('B1')+internal['j']*z('C')))
    ck('GH','G H',z('G')*z('H'));ck('I','GH H',z('GH')**2-z('H')**2+1)
    ck('V0','P K',z('P')*z('K'));ck('a0','V0 K',z('V0')**2-z('K')**2+1);ck('a1','D F I',z('D')*z('F')*z('I'))
    ck('m','K C Y Gcap',(z('K')**2-4*(z('C')-z('K')*z('Y'))**2)*z('Gcap')-8*g*z('K')**2)
    ck('B8','D',8*z('D')**2-4*z('D')-1)
    majorant=obj['majorant'];q=64 if majorant=='simple64' else 2048**2
    if majorant=='simple64':
        ck('Tpair','k B8',z('k')*z('B8'));ck('V1','Tpair GH',z('Tpair')*z('GH'))
    else:
        ck('Nstar','G Lstar',2*z('G')+z('Lstar'))
        ck('T6','k B8 Nstar D Lstar C',z('k')*(128*z('B8')*z('Nstar')-8*z('k')**2*(2*z('B8')+2*z('D')-1)*z('Lstar')+z('C')*(14*z('k')**2-192)))
        if majorant=='quotient2048':
            a,c=z('A'),z('C')
            ck('quotient_correction','A C',c*(9*c*(64*a-239)-14*(64*a*a-304*a+603))+1024)
            ck('Tmajor','T6 quotient_correction',z('T6')+internal['i']**3*z('quotient_correction')+288*internal['i']+2048)
        else:ck('Tmajor','T6 k',z('T6')+256*internal['i']*(z('k')**2+2)+2048)
        ck('V1','Tmajor H',z('Tmajor')*z('H'))
    if obj['certificate_form']:
        if majorant=='simple64':
            ck('Delta1','D k GH F H',((8*z('D')+1)*z('k')**2-64*z('D'))*z('GH')**2+64*z('D')*z('F')*(z('H')**2-1))
        else:
            data=json.loads((ROOT/'nine/REFINED_DEFECT_POLYNOMIAL.json').read_text())
            want=sum(t['coefficient']*z('A')**t['powers'][0]*z('C')**t['powers'][1]*internal['i']**t['powers'][2] for t in data['terms'])
            ck('DeltaT','A C',want)
            ck('Delta1','H DeltaT D F',z('H')**2*z('DeltaT')+q*z('D')*z('F')*(z('H')**2-1))
    ck('Omega','J m',z('J')*z('m'));ck('E0','J Q',z('J')*internal['n']+z('Q'))
    ck('Theta','E0 Omega V0 V1',z('E0')-z('Omega')*(z('V0')+z('V1')))
    if obj['certificate_form']:
        ck('inner','E0 Omega V0 V1 K Delta1',z('E0')**2-2*z('E0')*z('Omega')*(z('V0')+z('V1'))+z('Omega')**2*(z('K')**2-1+z('Delta1')+2*z('V0')*z('V1')))
    else:ck('inner','Theta Omega a0 a1',z('Theta')**2-z('Omega')**2*(z('a0')+q*z('a1')))
    ck('F9','inner Omega a0 a1',z('inner')**2-4*q*z('Omega')**4*z('a0')*z('a1'))
    return cases

def main():
    if not __debug__:raise RuntimeError('Assertions required')
    binding=json.loads((ROOT/'native/COEFFICIENT_BINDING.json').read_text());actual=[]
    for name in ['beta','K0','MC','MF']:
        fname=binding['binding'][name];raw=gzip.decompress((ROOT/'native'/fname).read_bytes())
        rec=next(r for r in binding['ports'] if r['name']=={'K0':'K','MF':'MF_source'}.get(name,name))
        assert hashlib.sha256(raw).hexdigest()==rec['sha256']
        z=int.from_bytes(raw,'little');assert z.bit_length()==rec['bits'];actual.append(z)
    materialized=json.loads((ROOT/'nine/FIXED_BINDING.json').read_text())
    assert materialized['native_binding_sha256']==hashlib.sha256((ROOT/'native/COEFFICIENT_BINDING.json').read_bytes()).hexdigest()
    leaf_values={}
    for key,leaf in materialized['leaves'].items():
        compressed=(ROOT/'nine'/leaf['file']).read_bytes();raw=gzip.decompress(compressed)
        assert hashlib.sha256(compressed).hexdigest()==leaf['gzip_sha256']
        assert hashlib.sha256(raw).hexdigest()==leaf['magnitude_sha256']
        magnitude=int.from_bytes(raw,'little')
        assert len(raw)==leaf['bytes'] and magnitude.bit_length()==leaf['bits'] and leaf['sign'] in [-1,1]
        leaf_values[key]=leaf['sign']*magnitude
    rng=random.Random(80080091);results=[];max_bits=0
    for path in sorted((ROOT/'nine/generated').glob('nine_*.json')):
        obj=json.loads(path.read_text());certpath=ROOT/obj['positional_certificate'];cert=json.loads(certpath.read_text())
        sp=obj['source_parameters'];ndeg=cert['Kcode']+2*cert['maximum_weight']+10
        assert sp['W']==cert['maximum_weight'] and sp['padding']==cert['padding_exponent']
        assert sp['Dmax']==cert['Dmax'] and sp['Hmax']==cert['target_maximum'] and sp['Kcode']==cert['Kcode']
        assert sp['E']==cert['Kcode']+cert['maximum_weight']+2 and sp['q']==ndeg//2
        assert sp['kappa']==864026 and sp['threshold_scale_exponent']==(15+ndeg%2)*sp['kappa']//2-10
        assert obj['fixed_power_leaves']['threshold_scale']==sp['threshold_scale_exponent']
        exact_register_count=exact_registers(obj,cert)
        assert hashlib.sha256(certpath.read_bytes()).hexdigest()==obj['positional_certificate_sha256']
        assert len(obj['variables'])==len(set(obj['variables']))==9
        assert set(n['name'] for n in obj['nodes'] if n['kind']=='variable')==set(obj['variables'])
        counts=dict(Counter(n['kind'] for n in obj['nodes'] if 'left'in n))
        assert counts==obj['operation_counts'] and sum(counts.values())==obj['total_operations']
        live=set();todo=[obj['output']]
        while todo:
            ix=todo.pop()
            if ix in live:continue
            live.add(ix);node=obj['nodes'][ix]
            if 'left'in node:todo.extend([node['left'],node['right']])
        assert len(live)==len(obj['nodes'])
        mat=materialized['circuits'][path.name]
        assert mat['sha256']==hashlib.sha256(path.read_bytes()).hexdigest()
        assert set(mat['fixed_leaves'])==set(n['name'] for n in obj['nodes'] if n['kind']=='fixed')
        fv=fixed_values(obj,actual)
        assert all(fv[name]==leaf_values[key] for name,key in mat['fixed_leaves'].items())
        actual_env=dict(zip(cert['ports'],actual))
        for row in cert['rows']:
            for term in row['terms']:
                z=abs(expr(term['weighted_coefficient'],actual_env));max_bits=max(max_bits,z.bit_length());assert z<(1<<864013)
        assert obj['fixed_power_leaves']['radix_scale']==864026 and 864026%2==0
        cases=0
        for prime in [2,3,5,97,1000000007,1000000009]:
            for ports in [actual,[7,11,13,17]]:
                reduced=[x%prime for x in ports];fixed=fixed_values(obj,reduced,prime)
                vv=[{n:k for n in obj['variables']} for k in [0,1,2]]
                vv += [{n:rng.randrange(prime) for n in obj['variables']} for _ in range(12)]
                for vals in vv:
                    want,wn=direct(obj,cert,vals,reduced,prime);got,gn=run(obj,vals,fixed,prime)
                    assert want==got,(path.name,prime,vals,want,got)
                    assert all(gn[k]==v for k,v in wn.items() if k in gn),(path.name,'register mismatch')
                    cases+=1
        if obj['certificate_form']:
            (degree,head),named=heads(obj,[7,11,13,17]);sp=obj['source_parameters'];r=4*sp['E']+2;n=sp['Kcode']+2*sp['W']+10;c=2*sp['W']+1
            assert obj['source_degrees']==dict(R=r,N=n,Gcap=c)
            assert named['R']==(r,{(2*sp['E'],0):4})
            assert named['N']==(n,{(sp['q'],1):1})
            assert named['Gcap']==(c,{(sp['W'],0):32})
            expected_degree=(154*r+328*n+4*c+196 if obj['majorant']=='quotient2048' else 188*r+400*n+4*c+232)
            if obj['majorant']=='quotient2048':expected_head={(4*sp['W']+308*sp['E']+328*sp['q'],328):81*2**476}
            else:expected_head={(4*sp['W']+376*sp['E']+400*sp['q'],400):2**554}
            assert degree==obj['degree']==expected_degree
            assert head==expected_head,(path.name,head,expected_head)
            degree_report={'exact_degree':degree,'lambda_exponent':next(iter(head))[0],'threshold_scale_exponent':next(iter(head))[1],'small_integer_head_bits':next(iter(head.values())).bit_length()}
        else:degree_report=None
        results.append(dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),operations=obj['total_operations'],exact_register_identities=exact_register_count,modular_cases=cases,exact_certificate=degree_report))
    assert max_bits==864013
    result=dict(status='PASS',actual_maximum_weighted_coefficient_bits=max_bits,native_binding_verified=True,materialized_signed_leaves=len(leaf_values),
      literal_circuits=results,scope='Literal graph, direct-formula, coefficient-bound, source-binding and exact resolved-degree checks; not end-to-end formal certification.')
    (ROOT/'audit/INDEPENDENT_NINE_CIRCUIT_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
