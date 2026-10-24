#!/usr/bin/env python3
"""Independent exact audit. Standard library only; no producer imports/execution.
Sparse polynomials use sorted (indeterminate, exponent) tuples and integer coefficients.
The input JSONs are inert data, parsed with a restricted Python-expression AST.
"""
import argparse, ast, collections, gzip, hashlib, json, math, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=Path(__file__).resolve().parent
REPORT={}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def keymul(a,b):
    d=dict(a)
    for n,e in b:d[n]=d.get(n,0)+e
    return tuple(sorted(d.items()))
class P:
    def __init__(self,x=0): self.d=({():x} if x else {}) if isinstance(x,int) else x
    @staticmethod
    def var(n):return P({((n,1),):1})
    def __add__(self,o):
        o=poly(o);d=self.d.copy()
        for m,c in o.d.items():
            d[m]=d.get(m,0)+c
            if not d[m]:del d[m]
        return P(d)
    __radd__=__add__
    def __neg__(self):return P({m:-c for m,c in self.d.items()})
    def __sub__(self,o):return self+-poly(o)
    def __rsub__(self,o):return poly(o)+-self
    def __mul__(self,o):
        o=poly(o);d=collections.defaultdict(int)
        for a,c in self.d.items():
            for b,v in o.d.items():d[keymul(a,b)]+=c*v
        return P({m:c for m,c in d.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        need(isinstance(n,int) and n>=0,'power');r=P(1);x=self
        while n:
            if n&1:r=r*x
            n//=2
            if n:x=x*x
        return r
    def __eq__(self,o):return self.d==poly(o).d
    def __bool__(self):return bool(self.d)
    def degree(self,weights):return max((sum(weights.get(n,0)*e for n,e in m) for m in self.d),default=-1)
    def lead(self,weights):
        d=self.degree(weights);return P({m:c for m,c in self.d.items() if sum(weights.get(n,0)*e for n,e in m)==d})
    def sub(self,e):
        ans=P()
        for m,c in self.d.items():
            term=P(c)
            for n,k in m:term=term*e.get(n,P.var(n))**k
            ans=ans+term
        return ans
    def terms(self):return [{'monomial':dict(m),'coefficient':str(c)} for m,c in sorted(self.d.items())]
def poly(x):return x if isinstance(x,P) else P(x)
def parse(s,e=None):
    e=e or {}
    def rec(t):
        if isinstance(t,ast.Constant) and type(t.value)==int:return P(t.value)
        if isinstance(t,ast.Name):return e.get(t.id,P.var(t.id))
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return -rec(t.operand)
        if isinstance(t,ast.BinOp):
            if isinstance(t.op,ast.Pow):
                need(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=32,'literal exponent')
                return rec(t.left)**t.right.value
            a,b=rec(t.left),rec(t.right)
            if isinstance(t.op,ast.Add):return a+b
            if isinstance(t.op,ast.Sub):return a-b
            if isinstance(t.op,ast.Mult):return a*b
        raise ValueError(ast.dump(t))
    return rec(ast.parse(s,mode='eval').body)
def jsonin(p):return json.loads(p.read_text())
def coef_sos(rs,target,variables):
    vs=set(variables);out=P()
    for r in rs:
        eligible=[]
        for mon,co in r.d.items():
            v={n:e for n,e in mon if n in vs}
            if any(e>target.get(n,0) for n,e in v.items()):continue
            eligible.append((v,tuple((n,e) for n,e in mon if n not in vs),co))
        for a,pa,ca in eligible:
            for b,pb,cb in eligible:
                v=dict(a)
                for n,e in b.items():v[n]=v.get(n,0)+e
                if v==target:out=out+P({keymul(pa,pb):ca*cb})
    return out

def integer_literals():
    base=ROOT/'positivity';src=jsonin(base/'inherited/quartic38.json')
    old=jsonin(base/'inherited/quartic41.json')
    rs=[parse(s) for s in src['residuals']]
    ors=[parse(s) for s in old['residuals']]
    need(rs[:23]==ors[:23],'Q38 arithmetic differs from Q41')
    q=parse('beta*J+1');cone=parse('cone_A*F*cone_B*(beta*J+1-F-alpha)-(beta*J+1-cone_A*F-cone_B*(beta*J+1-F-alpha))**2')
    pos=lambda a,b,c:1+a*a+b*b+c*(c+1)
    var=P.var
    need(rs[23]==cone-pos(var('cone_pos1'),var('cone_pos2'),var('cone_pos3')),'cone equation')
    need(rs[24]==parse('eta*zeta')-pos(var('eta_zeta_pos1'),var('eta_zeta_pos2'),var('eta_zeta_pos3')),'eta guard')
    sourcevars=src['variables'];aff={'J':parse('3*J3+1'),'w_scale':parse('3*w3+1')}
    expected={}
    expected['quartic37_direct']=[r.sub({'X':parse('3*X3-1')}) for i,r in enumerate(rs) if i!=22]
    ra=[r.sub(aff) for i,r in enumerate(rs) if i!=22]
    expected['quartic37']=ra
    restorations={'P':'eta+zeta+E*(c-eta)','X':'4*(3*w3+1)*(beta*(3*J3+1)+1)','N':'(beta*(3*J3+1)+1)*(L+1)','C2':'c*c','Delta':'a*a+4*a+3','V':'f*o-c','Baux':'I*I','tau':'tau+E*(c-eta)','D':'D+a*c'}
    e={n:parse(s) for n,s in restorations.items()};r6=[r.sub(e) for r in ra]
    need([i for i,r in enumerate(r6) if not r]==[1,2,6,9,10,15,19],'seven exact defining rows')
    before=r6[17];r6[17]=r6[17]+parse('o*o*(F2-f*f)')
    need(r6[17]-before==parse('o*o')*ra[14],'ideal-preserving correction')
    expected['sextic30']=[r for r in r6 if r]
    k0='1-V+j*c+h*E';rest8={'L':'(beta*(3*J3+1)+1)**2-1','N':'(beta*(3*J3+1)+1)**3','X':restorations['X'],'C2':'c*c','F2':'f*f','g':'y*y-V*V','Baux':'I*I','D':restorations['X']+'+a*c+gamma*(4*a+3)','Delta':restorations['Delta'],'zeta':k0+'-eta','P':k0+'+E*(c-eta)'}
    e8={n:parse(s) for n,s in rest8.items()};r8=[r.sub(e8) for r in ra]
    need(sum(not r for r in r8)==11,'eleven exact defining rows')
    r8=[r for r in r8 if r];expected['octic26']=r8
    x=cone.sub(aff);y=parse('eta*(1-V+j*c+h*E-eta)')
    joint=x*y-(parse('t*t')-x-y+1)**2-pos(var('p'),var('qpos'),var('rpos'))
    r12=r8[:-2]+[joint];expected['degree12_24']=r12
    pivot={'F':parse('(K0+4*(3*w3+1))*C-z*beta*(3*J3+1)')}
    pivot['alpha']=parse('beta*(3*J3+1)+1-C')-pivot['F']
    for name,r0 in [('degree10_25',r8),('degree16_23',r12)]:
        rnew=[r.sub(pivot) for r in r0]
        need(sum(not r for r in rnew)==1,'one monic transport row '+name)
        expected[name]=[r for r in rnew if r]
    result=[]
    specs={'quartic37':(37,24,4,{'tau':4},'1'),'quartic37_direct':(37,24,4,{'tau':4},'1'),'sextic30':(30,17,6,{'I':4,'g':2},'1'),'octic26':(26,13,8,{'a':4,'f':4},'1'),'degree10_25':(25,12,10,{'w3':2,'C':2,'J3':6},'104976*beta**6'),'degree12_24':(24,12,12,{'eta':4,'j':4,'c':4},'1'),'degree16_23':(23,11,16,{'w3':8,'C':8},'429981696*cone_A**8')}
    for name,ers in expected.items():
        x=jsonin(base/(name+'.json'));actual=[parse(s) for s in x['residuals']]
        need(actual==ers,'literal residual mismatch '+name)
        nv,nr,deg,target,cstr=specs[name]
        need(len(x['variables'])==nv and len(actual)==nr,'count '+name)
        weights={n:1 for n in x['variables']};ports=set(x['fixed_numerals'])
        leaves={n for r in actual for m in r.d for n,k in m}
        need(leaves-ports==set(x['variables']),'all and only declared witnesses '+name)
        degrees=[r.degree(weights) for r in actual]
        need(2*max(degrees)==deg==x['exact_degree'],'degree bound '+name)
        cert=coef_sos(actual,target,x['variables'])
        need(cert==parse(cstr),'actual degree coefficient '+name)
        need(cert==parse(x['degree_certificate']['coefficient']) and target==x['degree_certificate']['monomial'],'published certificate '+name)
        need(all(v>0 for v in cert.d.values()),'certificate positivity '+name)
        result.append(dict(packet=name,variables=nv,residuals=nr,exact_degree=deg,coefficient_monomial=target,coefficient=cstr,residual_terms=sum(len(r.d) for r in actual)))
    REPORT['integer_packets']=result
    REPORT['integer_maps']='All seven complete literal arrays equal independent exact transformations, including monic restorations and the ideal-preserving sextic row operation.'

def hashes_and_coefficients():
    base=ROOT/'positivity';pins=jsonin(base/'INHERITED_HASHES.json')
    for f,h in pins.items():need(hashlib.sha256((base/f).read_bytes()).hexdigest()==h,'inherited hash '+f)
    sets=[]
    for root,filename,style in [(base,'BINDING.json',0),(ROOT/'positive/native','ACTIVE_BINDING.json',1)]:
        binding=jsonin(root/filename);ports={}
        for name,rec in binding['ports'].items():
            z=(root/rec['file' if style else 'path']).read_bytes();raw=gzip.decompress(z);v=int.from_bytes(raw,'little')
            need(raw and raw[-1]!=0,'minimal payload '+name)
            need(hashlib.sha256(raw).hexdigest()==rec['sha256_raw' if style else 'raw_sha256'],'raw hash '+name)
            need(hashlib.sha256(z).hexdigest()==rec['sha256_gzip' if style else 'gzip_sha256'],'gzip hash '+name)
            need(v.bit_length()==rec['bits'] and len(raw)==rec['raw_bytes'],'payload sizes '+name)
            ports[name]=v
        d=590069 if style else 1064921
        need(ports['beta']==(1<<d)-1,'whole tuple radix')
        need(0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'mask interval')
        need((ports['MF']-ports['beta'])%8==4 and ports['MC']%4==2,'shift convention')
        sets.append((style,ports))
    tilepath=base/'coefficients/wang943_tiles.json';tiles=jsonin(tilepath)
    transitions=[line.split() for line in (base/'coefficients/k215.tm').read_text().splitlines() if line and not line.startswith('#')]
    transitions=[(int(q),int(b),int(w),m,int(t)) for q,b,w,m,t in transitions]
    rr={q:i+6 for i,q in enumerate(sorted({a[4] for a in transitions if a[3]=='R'}))}
    ll={q:i+205 for i,q in enumerate(sorted({a[4] for a in transitions if a[3]=='L'}))}
    hd=lambda q,b:2*q+2+b
    ts={(0,hd(q,b),rr[t],w) if m=='R' else (ll[t],hd(q,b),0,w) for q,b,w,m,t in transitions}
    for b in (0,1):
        ts|={(0,hd(215,b),0,hd(215,b)),(0,b,0,b)}
        ts|={(rr[q],b,0,hd(q,b)) for q in rr}
        ts|={(0,b,ll[q],hd(q,b)) for q in ll}
    ts|={(0,n,0,438) for n in (0,1,432,433)}|{(2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)}
    ts|={(1,438,1,n) for n in (434,435,436)}|{(a,437,b,437) for a in (0,1,4) for b in (0,1,2)}|{(5,0,0,0)}
    need([list(t) for t in [(2,435,3,1),(5,0,0,0)]+sorted(ts-{(2,435,3,1),(5,0,0,0)})]==tiles,'literal ordered Wang943 language')
    finite=[]
    for style,ports in sets:
        if not style:
            b,L=121,8801;weight=lambda j:1<<(10+2*j)
            ce={i:1+sum(weight(10*s+j) for s,x in enumerate(tile) for j in range(10) if ((x+512)>>j)&1)+sum(weight(j) for j in range(40,44)) for i,tile in enumerate(tiles)}
            ce.update({off+2*j:weight(10*s+j) for s,off in enumerate((1020,1000,980,960)) for j in range(10)})
            ce.update({e:weight(40+j) for j,e in enumerate((1095,1096,2195,3296))});bare=(40,41,1100,2200);dr=1
            targets=[1000+2*j for j in range(10)]+[1021+2*j for j in range(10)]+[2195,3296]
            mu=1022+sum(weight(j) for j in range(44));padding={e:(1<<119)-1 for e in range(8792,8799)};padding[8799]=(1<<27)-1
        else:
            b,L=67,8807;width=(9,10,9,10);occ=(256,512,256,512);starts=(0,9,19,28);offsets=(1023,1013,1003,983)
            perm=tuple(list(range(8))+[34]+list(range(8,17))+[35]+list(range(17,25))+[36]+list(range(25,34))+[37]+[38,39,40]);weight=lambda j:1<<(10+perm[j])
            ce={i:1+(1<<51)-sum(weight(starts[s]+j) for s,x in enumerate(tile) for j in range(width[s]) if ((x+occ[s])>>j)&1)-sum(weight(j) for j in range(38,41)) for i,tile in enumerate(tiles)}
            ce.update({offsets[s]+j:weight(starts[s]+j) for s in range(4) for j in range(width[s])})
            ce.update({e:weight(38+j) for j,e in enumerate((1095,2195,3296))});bare=(30,62,1100,2201);dr=42
            targets=[1013+j for j in range(10)]+[1065+j for j in range(9)]+[2195,3296]
            mu=(1<<51)-2;padding={e:(1<<65)-1 for e in range(8792,8805)};padding[8805]=(1<<19)-1
        ce.update({1063:0,1064:0});dc=collections.Counter({e:1 for e in bare})
        for e,c in ce.items():
            for t in (4393,5495):dc[t-e]+=c
        B=1<<(b*L);DC=sum(c<<(b*e) for e,c in dc.items());DR=1<<(b*dr)
        nativeMF=4+sum(mu<<(b*t) for t in (4393,5495))+sum(1<<(b*t) for t in targets)+sum(c<<(b*e) for e,c in padding.items())
        MC=B-1-sum(1<<(b*e) for e in ce if e!=1)-(2<<(b*1063))
        rebuilt={'beta':B-1,'K0':DC+B*DR,'MC':MC,'MF':nativeMF+B-1}
        for n,v in rebuilt.items():need(ports[n]==v,'independent coefficient reconstruction '+str(style)+' '+n)
        if not style:
            need(ports['cone_A']==1<<1113 and ports['cone_B']==1<<666104,'new cone scales')
            c0=ce[0];mass=991*(2*sum(ce.values())+6);rho=1<<121
            need(dc[5495]==c0 and c0==105534389824824194647382298625,'unique top convolution coefficient')
            need((1<<96)<=c0<c0+1<=3*(1<<95),'leading digit interval')
            need(4*mass+8<rho and 6*sum(ce.values())+18<mass,'canonical no carry')
            need(121*8791+1113==1064921-97 and 121*3296+666104==1064921-1,'balancing exponent identities')
            need(ports['beta']%3==1,'residue orientation binding')
        finite.append(dict(tuple='compact44' if style else 'mixed-parity-unrounded-1064921',all_four_ports_rebuilt=True,radix_exponent=b*L,raw_bytes=sum((v.bit_length()+7)//8 for v in ports.values())))
    REPORT['fixed_coefficients']=finite
    REPORT['inherited_files_sha256_verified']=len(pins)

def positive_literals():
    p=ROOT/'positive';results=[]
    for name,srcname,expected_count in [('p11_degree277','70-residue-orientation/eleven/p11_positive_degree325',111),('p12_degree78','69-cones-pell/positive/equation',101)]:
        cur=jsonin(p/(name+'.json'));old=jsonin(ROOT/'review/packages'/(srcname+'.json'))
        source=[]
        for row in old['source']:
            if name.startswith('p11'):
                if row[0] in ('g14','g15'):continue
                row=['I','*','c2','i'] if row[0]=='I' else row
            else:
                if row[0]=='q4':continue
                if row[0]=='q5':row=['U','*','q2','Y']
                elif row[0]=='g56':row=['g56','*','q','E']
                else:row=[('U' if v=='q5' else v) for v in row]
            source.append(row)
        need(source==cur['source'],'entire positive graph transformation '+name)
        names=set(cur['witnesses']+cur['fixed_numerals']);deps={}
        for dst,op,a,b in cur['source']:
            need(op in ('+','-','*') and dst not in names,'fresh allowed graph operation')
            need(all(type(v)==int or v in names for v in (a,b)),'topological graph')
            names.add(dst);deps[dst]=[v for v in (a,b) if isinstance(v,str)]
        todo=[cur['output']];live=set()
        while todo:
            n=todo.pop()
            if n not in live:live.add(n);todo+=deps.get(n,[])
        need(set(names)==live,'complete witness and gate liveness')
        need(len(cur['source'])==expected_count,'literal binary count')
        degrees={n:1 for n in cur['witnesses']};degrees.update({n:0 for n in cur['fixed_numerals']})
        corrections={'A1':13} if name.startswith('p11') else {'A0':15,'A1':13,'g82':7}
        for dst,op,aa0,bb0 in cur['source']:
            da=degrees[aa0] if isinstance(aa0,str) else 0;db=degrees[bb0] if isinstance(bb0,str) else 0
            degrees[dst]=corrections.get(dst,da+db if op=='*' else max(da,db))
        need(degrees[cur['output']]==cur['exact_degree'],'cancellation-resolved output degree bound')
        relevant=['I','Df','Q','V','L','W','Zbar','A','Bf','Cnum','Ncenter','N8','A1','P11'] if name.startswith('p11') else ['A0','A1','rho','den','Q','V','g82','aux_a','aux_b','normA','N','P12']
        results.append(dict(packet=name,variables=len(cur['witnesses']),operations=expected_count,breakdown=dict(collections.Counter(row[1] for row in cur['source'])),degree_bounds={n:degrees[n] for n in relevant}))
    # Exact sparse abstract expansions, not floating evaluation or finite testing.
    e={n:P.var(n) for n in ['q','X','Y','k','eta','gamma','R','F','alpha','K0','r','n','Q','V','d','rho']}
    q,X,Y,k,eta,gamma,R=[e[n] for n in ['q','X','Y','k','eta','gamma','R']]
    c=k*Y+eta;a=X*Y+Y;H=4*a+3;Delta=a*a+H
    main_leaders={}
    for b in (1,4):
        U=b*q*q*Y;D=U*(X+a*c)+H*(U*gamma+b*q*X*Y-(k-R-1))
        A1=D*D-U*U*(1+Delta*c*c)
        weights={n:1 for n in e};weights['R']=4;weights['K0']=0
        leader=8*b*q*q*k*X*X*Y**4*(b*q*q*Y*gamma+R)
        need(A1.degree(weights)==13 and A1.lead(weights)==leader,'adaptive carrier exact cancellation '+str(b))
        main_leaders[b]=leader
    ell=X*k*Y*Y;M=q**3*(q-1);Bt=(q*e['K0']+X)*(q-e['F']-e['alpha'])-q*e['F'];W=1+(q-1)*k
    Z=M*(ell+k+e['r'])+(q-1)*Y-q**3*W*Bt
    A0=Z*Z-M*M*(ell*(ell+k)+1)
    weights={n:1 for n in e};weights['K0']=0
    need(A0.degree(weights)==15 and A0.lead(weights)==-2*q**8*k*k*X*Y*Y*Bt,'first carrier cancellation')
    Q,V,d,rho,n=[e[z] for z in ['Q','V','d','rho','n']]
    h=lambda z:(1-Q)*z*z+2*(1-Q)*V*z+V*V-1
    aa=h(n);bb=2*(1-Q)*(n+V);AN=d*aa+(1-Q)*rho;N=AN*AN-d*bb*bb*rho
    i=P.var('i')
    need(N.sub({'rho':d*i*i})==d*d*h(n-i)*h(n+i),'two-root resultant exact factorization')
    wn={'d':12,'Q':6,'V':6,'rho':2,'n':1}
    need(N.degree(wn)==50 and N.lead(wn)==4*d*d*Q*Q*V*V*n*n,'norm exact weighted degree')
    # Three-root elimination identity in the independent extension ring with squares.
    x,aa,bb,cc,delta=[P.var(z) for z in ['z','A','B','C','delta']]
    center=delta**2*((x*x-aa-bb)**2-4*aa*bb)-2*delta*cc*(x*x+aa+bb)+cc*cc
    schedule=(delta*(x*x-aa-bb)-cc)**2-4*(delta*delta*aa*bb+delta*cc*(aa+bb))
    need(center==schedule,'factored three-root norm center')
    # Certificates after substituting actual witness leading forms.
    j,beta,zeta,t,T,F,alpha,i=[P.var(z) for z in ['j','beta','zeta','t','T','F','alpha','i']]
    k0=P.var('eta')+zeta;X=P.var('X');Y=P.var('Y');gamma=P.var('gamma');n=P.var('n');K0=P.var('K0')
    q0=6*beta*j;R0=q0**3*(q0-F);Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    # Avoid expanding large products: only compute a requested target coefficient.
    def coef_product(factors,target,ports):
        z=P(1)
        for f in factors:
            z=z*f
            z=P({m:c for m,c in z.d.items() if all(n in ports or e<=target.get(n,0) for n,e in m)})
        out=P({tuple((n,e) for n,e in m if n in ports):c for m,c in z.d.items() if {n:e for n,e in m if n not in ports}==target})
        # Multiple leftover port monomials can coincide; normalize by sum instead.
        out=P()
        for m,c in z.d.items():
            if {n:e for n,e in m if n not in ports}==target:out=out+P({tuple((n,e) for n,e in m if n in ports):c})
        return out
    tar12={'j':18,'eta':11,'X':12,'Y':23,'t':8,'n':2,'gamma':1,'alpha':1,'F':2}
    lead12f=[-64*q0**10,k0**11,X**11,Y**22,t**8,n*n,Bt0,q0*q0*Y*gamma+R0,R0*R0]
    c12=coef_product(lead12f,tar12,{'beta','K0'})
    need(c12==64*(6*beta)**18,'positive12 actual-slice degree coefficient')
    q0=3*beta*j;Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    tar11={'j':60,'i':24,'eta':49,'X':42,'Y':85,'alpha':16,'gamma':1}
    # Q0^4 Zbar0^8 A1_13, collected before selecting the coefficient.
    lead11f=[32*3**8,i**24,q0**58,k0**49,X**34,Y**84,(q0+F+alpha)**8,Bt0**8,4*q0*q0*Y*gamma+q0**3*(q0-F)]
    c11=coef_product(lead11f,tar11,{'beta','K0'})
    need(c11==128*3**8*(3*beta)**60,'positive11 actual-slice degree coefficient')
    need(sum(tar11.values())==277 and sum(tar12.values())==78,'certificate total degree')
    REPORT['positive_packets']=results
    REPORT['positive_exact_degree_certificates']=[dict(packet='p11_degree277',monomial=tar11,coefficient='128*3^8*(3*beta)^60',exact_degree=277),dict(packet='p12_degree78',monomial=tar12,coefficient='64*(6*beta)^18',exact_degree=78)]
    REPORT['positive_symbolic_identities']='Exact independent sparse expansion of both adaptive A1 carriers, the A0 cancellation, two-root resultant, and the factored octic norm center.'

def archives():
    root=ROOT/'review/archives';index={}
    pins=jsonin(ROOT/'review/ARCHIVE_PINS.json')
    for rec in pins:
        p=root/rec['file'];b=p.read_bytes()
        need(hashlib.sha256(b).hexdigest()==rec['sha256'],'archive raw pin '+p.name)
        need(hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()==rec['git_blob_sha'],'archive Git blob '+p.name)
        with zipfile.ZipFile(p) as z:
            for n in z.namelist():
                if n.endswith('/'):continue
                h=hashlib.sha256(z.read(n)).hexdigest()
                index.setdefault(h,[]).append({'archive':p.name,'entry':n})
    files=list((ROOT/'positivity/inherited').iterdir())
    files += [p for p in (ROOT/'review/packages').rglob('*') if p.is_file() and any(s in str(p) for s in ['69-cones-pell/positive','70-residue-orientation/eleven','70-residue-orientation/positive','73-guard-reanchoring/positive'])]
    files += list((OUT/'inherited_interfaces').iterdir())
    matches=[]
    for p in files:
        if not p.is_file():continue
        h=hashlib.sha256(p.read_bytes()).hexdigest();need(h in index,'source not byte-exact to archive '+str(p))
        matches.append({'path':str(p.relative_to(ROOT)),'sha256':h,'archive_matches':index[h]})
    (OUT/'ARCHIVE_MATCHES.json').write_text(json.dumps(matches,indent=2)+'\n')
    REPORT['authenticated_archives']=len(pins);REPORT['byte_exact_source_files']=len(matches)
    REPORT['archive_verification_mode']='Full archive SHA256 and Git-blob authentication, followed by exact member/source-byte comparison.'

def release_provenance():
    pins=jsonin(OUT/'SOURCE_ARCHIVE_PINS.json');by_name={r['file']:r for r in pins}
    rows=jsonin(OUT/'ARCHIVE_MATCHES.json')
    for row in rows:
        p=ROOT/row['path'];need(hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],'retained source digest '+row['path'])
        need(bool(row['archive_matches']),'missing prior archive member evidence')
        for m in row['archive_matches']:need(m['archive'] in by_name,'unknown prior archive pin')
    REPORT['byte_exact_source_files']=len(rows)
    REPORT['previously_authenticated_archive_pins']=len(pins)
    REPORT['archive_verification_mode']='Release mode: retained file digests rechecked against the prior full-audit receipt. Original archive bytes are not distributed and their SHA256/Git hashes are NOT recomputed in this run. See SOURCE_ARCHIVE_PINS.json, ARCHIVE_MATCHES.json and the preserved full RESULTS.json.'

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--release',action='store_true',help='Verify retained source hashes against the prior archive-audit receipt; do not require original ZIPs.');args=ap.parse_args()
    integer_literals();print('PASS: seven literal integer packets and exact degrees',flush=True)
    hashes_and_coefficients();print('PASS: both native tuples independently rebuilt; every payload/hash verified',flush=True)
    positive_literals();print('PASS: positive11/12 exact graph transformations, identities and coefficients',flush=True)
    if args.release:
        release_provenance();print('PASS: retained source hashes against prior full archive audit (archives not rerun)',flush=True)
    else:
        archives();print('PASS: authenticated archive pins and byte-exact inherited interfaces',flush=True)
    REPORT['status']='PASS';REPORT['scope']='Finite exact algebra and data only. Unbounded existence equivalences are proved in AUDIT.md subject to named inherited compiler/Pell/calibration theorems; no new kernel certificate.'
    (OUT/('RESULTS_RELEASE.json' if args.release else 'RESULTS.json')).write_text(json.dumps(REPORT,indent=2)+'\n')
