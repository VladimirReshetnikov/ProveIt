#!/usr/bin/env python3
"""Independent finite checks. Not an end-to-end formal consistency proof."""
import collections,gzip,hashlib,itertools,json,math,pathlib,random
R=pathlib.Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def load(p):return json.loads((R/p).read_text())
def plus(a,b,k=1):
    z=a.copy()
    for m,c in b.items():z[m]=z.get(m,0)+k*c
    return {m:c for m,c in z.items() if c}
def mul(a,b):
    z=collections.defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():z[tuple(x+y for x,y in zip(m,n))]+=c*d
    return {m:c for m,c in z.items() if c}
def ring_identities():
    # Exact coefficient dictionaries, not evaluations at sample points.
    n=4;zero=(0,)*n;one={zero:1}
    def var(i):
        m=list(zero);m[i]=1;return {tuple(m):1}
    def scale(a,k):return {m:k*c for m,c in a.items() if k*c}
    D,k,G,H=[var(i) for i in range(n)];D2=mul(D,D);k2=mul(k,k)
    F=plus(mul(mul(k2,D2),plus(D,one,-1)),one)
    Tp=mul(k,plus(plus(scale(D2,8),scale(D,4),-1),one,-1))
    defect=plus(mul(plus(scale(D,8),one),k2),scale(D,64),-1)
    need(plus(mul(Tp,Tp),scale(mul(D,F),64),-1)==defect,'Pell majorant exact identity')
    G2=mul(G,G);H2=mul(H,H);I=plus(mul(plus(G2,one,-1),H2),one)
    V1=mul(mul(Tp,G),H);a1=mul(mul(D,F),I)
    delta=plus(mul(defect,mul(G2,H2)),scale(mul(mul(D,F),plus(H2,one,-1)),64))
    need(plus(mul(V1,V1),scale(a1,64),-1)==delta,'radical majorant exact identity')
    n=7;zero=(0,)*n;one={zero:1}
    V0,V1,K,a1,Om,E0,unused=[var(i) for i in range(n)]
    a0=plus(plus(mul(V0,V0),mul(K,K),-1),one)
    delta=plus(mul(V1,V1),scale(a1,64),-1);shift=plus(V0,V1)
    theta=plus(E0,mul(Om,shift),-1)
    lhs=plus(mul(theta,theta),mul(mul(Om,Om),plus(a0,scale(a1,64))),-1)
    rhs=plus(plus(mul(E0,E0),scale(mul(mul(E0,Om),shift),2),-1),mul(mul(Om,Om),plus(plus(plus(mul(K,K),one,-1),delta),scale(mul(V0,V1),2))))
    need(lhs==rhs,'cancellation-resolved norm identity')
    return 3
def source_check():
    raw=(R/'data/parent_source.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest()=='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287','source bytes')
    src=json.loads(raw);rows=[{tuple(t['powers']):t['coefficient'] for t in row['terms']} for row in src['equations']]
    base=rows[:];rows[13]=plus(rows[13],rows[1]);rows[14]=plus(rows[14],rows[2]);rows[21]={m:-c for m,c in rows[21].items()}
    need(plus(rows[13],rows[1],-1)==base[13] and plus(rows[14],rows[2],-1)==base[14] and {m:-c for m,c in rows[21].items()}==base[21],'invertible row transformations')
    code=load('data/split_code.json');w=code['weights'];order=code['order'];qs=code['targets'];n=31
    need(len(w)==n and len(set(w))==n and min(w)>0 and sorted(order)==list(range(1,23)) and len(set(qs))==22,'code domains')
    need(code['source_row_operations']==[[14,2,1],[15,3,1]] and code['source_row_signs']=={'22':-1},'row metadata')
    allmons={d:list(itertools.combinations_with_replacement(range(n),d)) for d in range(3)}
    targ=dict(zip(qs,order));kernels=[{} for _ in range(3)];got=[{} for _ in range(22)];count=hits=0
    for ri,q in zip(order,qs):
        grouped=collections.defaultdict(dict)
        for powers,c in rows[ri-1].items():
            m=tuple(i for i,e in enumerate(powers[:n]) for _ in range(e));need(len(m)<=2,'quadratic source')
            factor=2 if len(m)<2 or m[0]==m[1] else 1;grouped[m][powers[n:]]=c*factor
        for m,co in grouped.items():
            d=len(m);e=q-sum(w[i] for i in m);need(e>=0 and e not in kernels[d],'kernel exponent')
            kernels[d][e]=co
            for a in allmons[d]:
                count+=1;j=targ.get(e+sum(w[i] for i in a))
                if j is not None:
                    need(j==ri and a==m,'source contamination');hits+=1
                    powers=[0]*n
                    for i in a:powers[i]+=1
                    multiplicity=2 if d==2 and a[0]!=a[1] else 1
                    for port,c in co.items():got[j-1][tuple(powers)+port]=c*multiplicity
    need(got==[{m:2*c for m,c in row.items()} for row in rows],'22 exact extracted polynomials')
    expected=[{'degree':d,'terms':[{'exponent':e,'coefficient':[{'powers':list(pp),'coefficient':c} for pp,c in sorted(co.items())]} for e,co in sorted(k.items())]} for d,k in enumerate(kernels)]
    need(expected==load('data/split_kernels.json')['kernels'],'kernel export')
    deg=[max(k) for k in kernels];W=max(w);H=max(deg[d]+d*W for d in range(3));Q=max(qs)
    need((W,H,Q,deg)==(111,2010,1954,[1954,1617,1788]),'layout measurements')
    need(kernels[2][1788]=={(0,0,0,0):1},'positive head')
    need(deg[2]+W-deg[1]==282 and deg[2]+2*W-deg[0]==56,'pre-decoding dominance')
    bits=[1064921,1070004,1064921,1064922]
    bound=max(sum(abs(c)*(1<<sum(e*b for e,b in zip(pp,bits))) for pp,c in co.items()) for k in kernels for co in k.values())
    need(bound.bit_length()==2134927,'coefficient bound')
    need(993*4<4096 and 86*32<4095 and H-Q>=2,'coefficient and arbitrary-g bounds')
    return {'interactions':count,'intended_contributions':hits,'exact_target_identities':22,'W':W,'H':H,'pre_decoding_gaps':[282,56],'coefficient_bound_exponent':bound.bit_length()}
def coefficients_check(body):
    ports={};nativebytes=0
    for row in load('coefficients/BINDING.json')['files']:
        z=(R/'coefficients'/(row['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(z)
        need(hashlib.sha256(z).hexdigest()==row['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'native payload digest')
        v=int.from_bytes(raw,'little');need(v.bit_length()==row['bit_length'] and len(raw)==row['bytes'],'native size');ports[row['name']]=v;nativebytes+=len(raw)
    p=[ports[x] for x in ['beta','K','MC','MF_source']]
    f={row['name']:sum(t['coefficient']*math.prod(pow(v,e) for v,e in zip(p,t['powers'])) for t in row['terms']) for row in body['coefficient_recipes']}
    f['base_scale']=1<<2134939;f['threshold_scale']=1<<16012032
    seen=set()
    for row in load('fixed/BINDING.json')['files']:
        z=(R/'fixed'/row['file']).read_bytes();raw=gzip.decompress(z);v=row['sign']*int.from_bytes(raw,'little')
        need(hashlib.sha256(z).hexdigest()==row['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==row['raw_sha256'],'derived digest')
        need(v==f[row['name']],'derived fixed value');seen.add(row['name'])
    need(seen=={n['name'] for n in body['nodes'] if n['kind']=='fixed'},'all fixed leaves materialized')
    return f,p,{'native_payload_bytes':nativebytes,'derived_leaves':len(seen)}
def evaldag(body,f,x,p):
    values=[]
    for node in body['nodes']:
        k=node['kind']
        if k=='variable':v=x[node['name']]
        elif k=='literal':v=node['value']
        elif k=='fixed':v=f[node['name']]
        else:
            a,b=values[node['left']],values[node['right']];v=a+b if k=='add' else a-b if k=='sub' else a*b
        values.append(v%p)
    return values[body['output']]
def direct(x,ports,p):
    b,g,h,s,w,C,i,j,n=[x[k] for k in ['b','g','h','s','w','C','i','j','n']];j-=1
    red=lambda x:x%p
    B=red(pow(2,2134939,p)*b*b);code=load('data/split_code.json')
    ell=red(sum(pow(B,k,p) for k in code['weights']));target=red(sum(pow(B,k,p) for k in code['targets']))
    ds=[]
    for row in load('data/split_kernels.json')['kernels']:
        ds.append(red(sum(sum(t['coefficient']*math.prod(pow(v%p,e,p) for v,e in zip(ports,t['powers'])) for t in term['coefficient'])*pow(B,term['exponent'],p) for term in row['terms'])))
    us=red(ell+g);Gs=red(ds[2]*us*us+ds[1]*us+ds[0]);N0=pow(B,112,p)
    mask=red(N0-1-(b-1)*ell);Sc=red(g+N0*(2*Gs+target));Tc=red(mask+N0*(B-2)*target)
    L=red(2*b*pow(B,2123,p));R0=red(L*(Sc+Tc+1)-Sc-1);N=red(pow(2,16012032,p)*pow(B,1121,p));t=red(b*pow(B,111,p))
    U=red(N*N*w);Y=red(N*N*s);M0=red(R0*Y);P=red(2*M0*M0*U);K=red(R0+1+h*(P-1));A=red(M0*(U+1));B1=red(2*R0+1);W1=red(b*w)
    J=red(4*A-5);Q=red(3*W1*C-2*(W1*W1-1));D=red((A*A-1)*C*C+1);k0=red(i*J*C);E=red(k0*D*C);F=red((A*A-1)*E*E+1)
    G=red(A+F*(C*D+1-A));H0=red(C+F*(B1+j*C));I=red((G*G-1)*H0*H0+1);a0=red((P*P-1)*K*K+1);a1=red(D*F*I)
    m=red(K*K*(4*t-g)-16*t*(C-K*Y)**2);V0=red(P*K);tp=red(k0*(8*D*D-4*D-1));V1=red(tp*G*H0);Om=red(J*m);E0=red(J*(n+W1*W1)+Q);theta=red(E0-Om*(V0+V1))
    return red((theta*theta-Om*Om*(a0+64*a1))**2-256*Om**4*a0*a1)
def exact_degree(body):
    # A separate leading-homogeneous-form engine; fixed leaves are formal
    # coefficient symbols of degree zero. Only actual input powers set degree.
    vars=body['variables'];fixed=sorted({n['name'] for n in body['nodes'] if n['kind']=='fixed'});names=vars+fixed;zero=(0,)*len(names);forms=[]
    for node in body['nodes']:
        k=node['kind']
        if k in ('variable','fixed'):
            m=list(zero);m[names.index(node['name'])]=1;z={tuple(m):1}
        elif k=='literal':z={zero:node['value']} if node['value'] else {}
        else:
            a,b=forms[node['left']],forms[node['right']]
            z=mul(a,b) if k=='mul' else plus(a,b,1 if k=='add' else -1)
        if not z and k in ('add','sub') and a and b:
            need(max(sum(m[:len(vars)]) for m in a)==0,'unresolved positive-degree cancellation')
        if z:
            degree=max(sum(m[:len(vars)]) for m in z);z={m:c for m,c in z.items() if sum(m[:len(vars)])==degree}
        else:degree=0
        forms.append(z)
    output=forms[body['output']];degree=max(sum(m[:len(vars)]) for m in output)
    diagonal=collections.defaultdict(int)
    for m,c in output.items():diagonal[tuple(m[len(vars):])]+=c
    diagonal={m:c for m,c in diagonal.items() if c}
    need(len(diagonal)==1,'unique positive diagonal leading term')
    m,scalar=next(iter(diagonal.items()));need(scalar==1<<290,'leading scalar')
    need({k:e for k,e in zip(fixed,m) if e}=={'base_scale':890324,'threshold_scale':400},'leading coefficient exponents')
    need(degree==816*2010+1224*111+5044==1781068,'degree formula')
    return degree
def main():
    identities=ring_identities();source=source_check();body=load('generated/split_111_positive.json');cert=load('generated/split_111_positive_certificate.json');f,ports,coef=coefficients_check(body)
    for label,bod,expected in [('positive',body,470),('natural',load('generated/split_111_natural.json'),477)]:
        live=set();todo=[bod['output']]
        while todo:
            u=todo.pop()
            if u in live:continue
            live.add(u);node=bod['nodes'][u]
            if node['kind'] in ('add','sub','mul'):todo.extend([node['left'],node['right']])
        counts=collections.Counter(bod['nodes'][u]['kind'] for u in live if bod['nodes'][u]['kind'] in ('add','sub','mul'))
        need(sum(counts.values())==expected and dict(counts)==bod['operation_counts'],'live gate ledger '+label)
    need(15*2134939-21==2*16012032,'threshold constant calibration')
    for k in range(128):
        v=2134939+2*k;need(1+k+2123*v+134*v-31*k-22==2*(16012032+1121*v),'valuation affine identity')
    rng=random.Random(20261023);checks=0
    for p in [1000003,1000033,(1<<61)-1]:
        reduced={name:value%p for name,value in f.items()}
        for _ in range(40):
            x={name:rng.randrange(1,1000) for name in body['variables']};a=evaldag(body,reduced,x,p);b=evaldag(cert,reduced,x,p);c=direct(x,ports,p)
            need(a==b==c,'independent actual-coefficient evaluation');checks+=1
    degree=exact_degree(cert)
    result={'status':'PASS','exact_tail_ring_identities':identities,'source':source,'coefficients':coef,'positive_operations':470,'natural_operations':477,'exact_degree':degree,'actual_tuple_modular_checks':checks,'threshold_identity':'2257v-30k-21=2(1121v+16012032), v=2134939+2k','scope':'Finite identities, source certificate, payloads, exact degree and implementation checks; imported unbounded compiler/finalizer semantics remain ordinary mathematical proof dependencies.'}
    (R/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
