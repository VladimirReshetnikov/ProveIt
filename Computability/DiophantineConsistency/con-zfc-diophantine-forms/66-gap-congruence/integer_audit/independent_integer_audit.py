"""Independent audit: inert DAGs only; no builder or upstream module imported."""
import json,gzip,hashlib,random,itertools,math
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'integer'
def check(x,msg):
    if not x:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
portnames=('beta','K','MC','MF_source')
ports=[]
port_entries=read(BASE/'data/coefficients_binding.json')['files']
check(tuple(x['name'] for x in port_entries)==portnames,'fixed port order')
for item in port_entries:
    blob=(BASE/'data'/(item['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(blob)
    check(hashlib.sha256(blob).hexdigest()==item['gzip_sha256'],'port compressed identity')
    check(hashlib.sha256(raw).hexdigest()==item['sha256'],'port identity')
    check(len(raw)==item['bytes'],'port length')
    ports.append(int.from_bytes(raw,'little'))
check(len(ports)==4,'whole tuple')
check(ports[0]==(1<<1064921)-1,'native radix')

def polyrecipe(terms):
    return sum(t['coefficient']*math.prod(v**e for v,e in zip(ports,t['powers'])) for t in terms)

def inspect(filename,layoutname):
    path=BASE/'generated'/filename;body=read(path);layout=read(BASE/'data'/layoutname)
    source_path=BASE/'data'/layout.get('source_file','parent_quartic31.json')
    src=read(source_path)
    check(hashlib.sha256(source_path.read_bytes()).hexdigest()==layout['source_sha256'],'source byte binding')
    if 'coordinate_map' in src:
        parent=read(BASE/'data/parent_quartic31.json')
        check(hashlib.sha256((BASE/'data/parent_quartic31.json').read_bytes()).hexdigest()==src['source_sha256'],'parent byte binding')
        names=src['variables']+src['constants'];n=len(names);zero=(0,)*n
        def atom(name):return tuple(int(i==names.index(name)) for i in range(n))
        def times(p,q):
            out={}
            for a,x in p.items():
                for b,y in q.items():
                    e=tuple(i+j for i,j in zip(a,b));out[e]=out.get(e,0)+x*y
            return {e:c for e,c in out.items() if c}
        transforms={atom('P'):{atom('P'):1,atom('eta'):1,atom('zeta'):1},atom('N'):{atom('N'):1,zero:1}}
        if 'J*beta' in src['coordinate_map']['N']:
            transforms[atom('N')][tuple(x+y for x,y in zip(atom('J'),atom('beta')))]=1
        expected=[]
        for row in parent['equations']:
            poly={}
            for term in row['terms']:
                cur={zero:term['coefficient']}
                for i,power in enumerate(term['powers']):
                    e=tuple(int(j==i) for j in range(n));factor=transforms.get(e,{e:1})
                    for _ in range(power):cur=times(cur,factor)
                for e,c in cur.items():poly[e]=poly.get(e,0)+c
            expected.append(poly)
        for i,j,a in src['source_row_operations']:
            for e,c in expected[j-1].items():expected[i-1][e]=expected[i-1].get(e,0)+a*c
        for i,row in enumerate(src['equations']):
            check({e:c for e,c in expected[i].items() if c}=={tuple(t['powers']):t['coefficient'] for t in row['terms']},'independent affine row identity')
    rows=[{tuple(t['powers']):t['coefficient'] for t in row['terms']} for row in src['equations']]
    for i,j,a in layout.get('source_row_operations',[]):
        for mon,c in rows[j-1].items():rows[i-1][mon]=rows[i-1].get(mon,0)+a*c
    for i,sign in enumerate(layout.get('row_orientations',[1]*len(rows))):
        check(sign in (-1,1),'invertible row orientation')
        rows[i]={e:sign*c for e,c in rows[i].items()}
    targets=dict(zip(layout['order'],layout['targets']));W=max(layout['weights']);weights=layout['weights']
    check(min(weights)>0 and len(set(weights))==31,'positive distinct positions')
    check(len(set(targets.values()))==22,'distinct targets')
    kernels=[{} for _ in range(3)];labels=[[(0,)*31],[],[]]
    for i in range(31):
        m=[0]*31;m[i]=1;labels[1].append(tuple(m))
    for i,j in itertools.combinations_with_replacement(range(31),2):
        m=[0]*31;m[i]+=1;m[j]+=1;labels[2].append(tuple(m))
    interactions=records=0
    for rowno,row in enumerate(rows,1):
        groups={}
        for mon,c in row.items():
            if c:
                alpha=mon[:31];rec=groups.setdefault(alpha,{})
                rec[mon[31:]]=rec.get(mon[31:],0)+c
        for alpha,rec in groups.items():
            degree=sum(alpha);factor=2 if degree<2 or 2 in alpha else 1
            value=factor*sum(c*math.prod(v**e for v,e in zip(ports,mon)) for mon,c in rec.items())
            exponent=targets[rowno]-sum(a*w for a,w in zip(alpha,weights))
            check(exponent>=0,'nonnegative reversed exponent')
            check(exponent not in kernels[degree],'kernel record collision')
            kernels[degree][exponent]=value;records+=1
            for beta in labels[degree]:
                result=exponent+sum(a*w for a,w in zip(beta,weights))
                check((result in targets.values())==(alpha==beta),'source isolation')
                interactions+=1
    height=max(max(k)+d*W for d,k in enumerate(kernels))
    check(height==layout['convolution_height'],'height')
    allpositive=all(k[max(k)]>0 for k in kernels)
    quadratic_dominates=(kernels[2][max(kernels[2])]>0 and max(kernels[2])+W>max(kernels[1]) and max(kernels[2])+2*W>max(kernels[0]))
    check(allpositive or quadratic_dominates,'unconditional positive convolution certificate')
    check(height-max(targets.values())>=2,'target headroom')
    M=1<<2134927
    check(all(abs(x)<M for k in kernels for x in k.values()),'record coefficient bound')
    fixed={name:polyrecipe(rec) for name,rec in body['fixed_recipes'].items()}
    fixed['radix']=1<<body['base_exponent'];fixed['threshold']=1<<(16*body['base_exponent']-23)
    check(fixed['radix']==8192*M,'radix reserve')
    manifest=read(BASE/'fixed/MANIFEST.json')
    check(set(fixed)=={m['name'] for m in manifest},'fixed manifest completeness')
    for item in manifest:
        blob=(BASE/'fixed'/(item['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(blob)
        check(hashlib.sha256(raw).hexdigest()==item['sha256'],'derived coefficient raw hash')
        check(hashlib.sha256(blob).hexdigest()==item['gzip_sha256'],'derived coefficient compressed hash')
        check(item['sign']*int.from_bytes(raw,'little')==fixed[item['name']],'materialized coefficient recipe')
    nodes=body['nodes'];live=set();pending=[body['output']]
    while pending:
        i=pending.pop()
        if i in live:continue
        live.add(i);n=nodes[i]
        if 'left'in n:pending.extend([n['left'],n['right']])
    check(len(live)==len(nodes),'no unused DAG nodes')
    count=sum('left'in n for n in nodes);check(count==body['total_operations'],'gate count')
    def evaluate(v,mod):
        arr=[];degrees=[];heads=[]
        for i,n in enumerate(nodes):
            k=n['kind']
            if k=='variable':value=v[n['name']];deg=1;head=value
            elif k=='literal':value=n['value'];deg=0;head=value
            elif k=='fixed':value=fixed[n['name']];deg=0;head=value
            else:
                l,r=n['left'],n['right'];check(l<i and r<i,'topological DAG')
                if k=='mul':value=arr[l]*arr[r];deg=degrees[l]+degrees[r];head=heads[l]*heads[r]
                else:
                    sign=1 if k=='add'else -1;value=arr[l]+sign*arr[r];deg=max(degrees[l],degrees[r])
                    head=(heads[l] if degrees[l]==deg else 0)+sign*(heads[r] if degrees[r]==deg else 0)
            arr.append(value%mod);degrees.append(deg);heads.append(head%mod)
        return arr[body['output']],{s:arr[i] for s,i in body['named_nodes'].items()},degrees[body['output']],heads[body['output']]
    def direct(v,p):
        def r(a):return a%p
        b=6*v['t']+4;g=b*v['g0'];h=b*v['h0'];k=b*(3*v['k0']+2);B=r(fixed['radix']*b*b)
        ell=r(sum(pow(B,w,p) for w in weights));Uword=r(ell+g)
        ds=[r(sum((a%p)*pow(B,e,p) for e,a in d.items())) for d in kernels]
        conv=r(ds[0]+ds[1]*Uword+ds[2]*Uword*Uword)
        N0=pow(B,W+1,p);N=pow(B,height+W+2,p);tar=r(sum(pow(B,e,p) for e in targets.values()))
        Tcode=r(N0-3-(b-1)*ell+N0*(B-2)*tar);Scode=r(g+N0*(2*conv+tar))
        X=r(N*(Scode+Tcode+1)-Scode-1);Y=r(fixed['threshold']*pow(B,height+2*W+9,p)*b);cap=r(b*pow(B,W,p))
        L=r(v['l']*Y);U=r(2*L*X);V=r(4*g*v['w']*Y);Wb=r(b*v['w']);A=r(U*(V+1));B1=r(2*X+1)
        C=r(B1+(A-2)*h);Phalf=r((L*X)*U*V);P=r(2*Phalf);K=r(X+1+k*(P-2));S=r(2*A-5);T=r(3*Wb*C-2*(Wb*Wb-1))
        Q=r((Phalf*Phalf-1)*K*K+1)
        Delta=r(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
        xi=r(v['z']*v['x']);D=r((A*A-4)*C*C+4);E=r(C*C*D*xi);F=r(4*(A*A-4)*E*E+1)
        G=r(2*(A+2)*(A-2)**2*E*E-1);H=r(C+(B1-C)*F+16*E*F*v['y']);I=r((G*G-1)*H*H+1)
        sig=r(xi*pow(S,5,p));rho=r(T+S*v['y']);theta=r((rho**3-rho*S*S-S**3)*(rho*rho+23*S*S))
        rb=r(b*Q);aa=r(rb+(3*Delta-1)*(rb*v['z'])**2);dd=r(D*F*I);Z=r(sig*v['m']-theta)
        out=r((Z*Z-sig*sig*(aa+dd))**2-4*sig**4*aa*dd)
        return out,dict(b=r(b),g=r(g),h=r(h),k=r(k),X=X,Y=Y,cap=cap,A=A,C=C,Q=Q,D=D,S=S,T=T,K=K,P=P,Delta=Delta,guard=aa,lucas=dd,Theta=theta,Sigma=sig)
    rnd=random.Random(976421);replays=0;heads=[]
    for p in (1000000007,998244353,1000003):
        for _ in range(40):
            vals={n:rnd.randrange(-13,14) for n in body['variables']}
            a,named,deg,h=evaluate(vals,p);z,expected=direct(vals,p)
            check(a==z,'independent direct formula')
            for k,x in expected.items():check(named[k]==x,'named register '+k)
            replays+=1
        _,_,deg,h=evaluate(dict.fromkeys(body['variables'],1),p)
        check(deg==body['degree_upper_bound'] and h!=0,'attained degree bound')
        heads.append(dict(prime=p,degree=deg,residue=h))
    cg=0
    for t in range(-6,7):
        b=6*t+4;mod=abs(24*b*b)
        for _ in range(15):
            vals={n:rnd.randrange(-9,10) for n in body['variables']};vals['t']=t
            _,a,_,_=evaluate(vals,mod)
            check(a['X']%2==1 and a['X']%3==0,'X parity/residue')
            check((a['X']+1+a['g'])%(b*b)==0,'canonical X+1 congruence')
            check(a['Y']%abs(b)==0,'Y divisibility')
            check(a['K']%abs(3*b)==0,'K congruence')
            check((a['Q']-1)%(b*b)==0 and a['Q']%3==1,'Q units')
            check(a['D']%abs(4*b)==0,'D divisibility')
            check((a['guard']-b)%abs(2*b)==0 and a['lucas']%abs(2*b)==0,'unconditional radicand separation')
            cg+=1
    return dict(file=str(path.relative_to(ROOT.parent)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),operations=count,degree=deg,record_count=records,isolation_interactions=interactions,modular_replays=replays,congruence_cases=cg,heads=heads)

# The explicit candidate table is independent of the builder's default selection.
results=[inspect('integer10.json','layout.json')]
BASE=BASE/'alternative_low_cost'
results.append(inspect('integer10.json','layout.json'))
# Exhaustive tiny block identity, including g's guaranteed second-lowest zero bit.
carry=0
for u in range(3,8):
    N=1<<u
    for S in range(0,N,4):
        for T in range(2,N-S):
            if not T&2:continue
            T1=T-2;X=N*(S+T1+1)-S-1
            defect=S.bit_count()+T1.bit_count()-(S+T1).bit_count()
            check(X.bit_count()==u+T1.bit_count()-defect,'leadless population identity')
            check((S&T1)==(S&T),'cleared bit does not change AND')
            check((defect==0)==(S&T==0),'carry iff disjoint')
            carry+=1
out=dict(status='PASS',candidates=results,carry_cases=carry,scope='Independent literal arithmetic, coefficient extraction, exact degrees and finite congruence/bit checks; universal proof and inherited compiler/Sun endpoint are separate.')
(ROOT/'INDEPENDENT_INTEGER_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
