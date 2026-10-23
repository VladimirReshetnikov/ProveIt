#!/usr/bin/env python3
"""Independent data, identity, modular replay, and finite-regression audit.
Finite tests supplement but do not replace the universal mathematical proof.
"""
from pathlib import Path
from itertools import product,combinations_with_replacement
import hashlib,gzip,json,math,random,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'upstream'))
from circuit import evaluate
from build_nine import build,degree_certificate,KAPPA
from verify_selective import audit

def require(ok,msg):
    if not ok:raise AssertionError(msg)
def digest(data):return hashlib.sha256(data).hexdigest()

def literal(v,ports,p,bridge='calibrated'):
    """Independent direct formula, using original positive source equations."""
    src=json.loads((ROOT/'upstream/upstream_parent_quartic31.json').read_text())
    code=json.loads((ROOT/'upstream/code_v1.json').read_text());ws=code['weights'][1:]
    # Evaluate shifted coefficients directly by binomial expansion, not builder recipes.
    b=2*(v['epsilon']+1)**2 if bridge=='two' else v['epsilon']+2
    B=pow(2,KAPPA,p)*b*b%p
    Ds=0
    for row,target in zip(code['order'],code['targets']):
        equation=next(e for e in src['equations'] if e['number']==row)
        for term in equation['terms']:
            es=term['powers'];n=len(ws);supp=[i for i,e in enumerate(es[:n]) if e]
            for ks in product(*(range(es[i]+1) for i in supp)):
                alpha=[0]*n;co=term['coefficient']
                for i,k in zip(supp,ks):alpha[i]=k;co*=math.comb(es[i],k)
                co*=math.factorial(2-sum(alpha))*math.prod(math.factorial(k) for k in alpha)
                for name,e in zip(src['constants'],es[n:]):co=co*pow(ports[name],e,p)%p
                Ds=(Ds+co*pow(B,target-sum(a*w for a,w in zip(alpha,ws)),p))%p
    b=v['epsilon']+2
    if bridge=='two':b=2*(v['epsilon']+1)**2
    B=pow(2,KAPPA,p)*b*b%p
    bp=lambda e:pow(B,e,p)
    g,h,s,w,i,j=(v[n]+1 for n in ('g0','h0','s0','w0','i0','j0'))
    ell=sum(bp(e) for e in ws)%p;targets=sum(bp(e) for e in code['targets'])%p
    N0=bp(184);L=2*b*bp(5741)%p if bridge=='calibrated' else bp(5741)
    mask=(N0-1-(b-1)*ell)%p;Tc=(mask+(B-2)*targets*N0)%p
    Jc=(2*(1+g)**2*Ds+targets)%p;Sc=(g+Jc*N0)%p
    if bridge=='three':R=((L-1)*((Sc+Tc+1)*L+Tc+1))%p;N=L
    else:
        R=(L*L+(Sc+Tc)*L+L-1-Sc)%p
        if bridge=='calibrated':N=pow(2,15*KAPPA//2-10,p)*bp(2966)%p
        else:N=pow(2,17*KAPPA//2-9,p)*bp(2965)*(v['epsilon']+1)**3%p
    Gcap=32*b*bp(183)%p;U=N*N*w%p;Y=N*N*s%p;MM=R*Y%p;P=2*MM*MM*U%p;K=(R+1+h*(P-1))%p
    A=MM*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p;C=(B1+W1+v['phi'])%p;J=(4*A-5)%p
    Q=(3*W1*C-2*(W1*W1-1))%p;D=((A*A-1)*C*C+1)%p;E=i*J*D*C*C%p
    F=((A*A-1)*E*E+1)%p;G=(A+F*(C*D+1-A))%p;H=(B1+j*C)%p;I=((G*G-1)*H*H+1)%p
    a0=((P*P-1)*K*K+1)%p;a1=64*D*F*I%p;u=J*F%p;vc=(Q*F+J*(H-C))%p
    margin=(K*K*Gcap-4*(C-K*Y)**2*Gcap-8*g*K*K)%p
    V0=P*K%p;t0=i*J*C%p;S0=t0*(8*D*D-4*D-1)%p;V1=S0*G*H%p;Md=(Q+H-C)%p
    Om=u*(2*margin-1)%p;Th=(u*v['n']+vc-Om*(Md+V0*V1))%p
    out=((Th*Th-Om*Om*(a0+V0*V0*a1))**2-4*Om**4*V0*V0*a0*a1)%p
    return out,{'b':b%p,'B':B,'Dcode':Ds,'N0':N0,'L':L,'mask':mask,'Jcode':Jc,'Scode':Sc,'Tcode':Tc,'R':R,'N':N,'Gcap':Gcap,'P':P,'K':K,'A':A,'C':C,'D':D,'E':E,'F':F,'G':G,'H':H,'I':I,'a0':a0,'a1':a1,'margin':margin,'u':u,'v':vc,'V0':V0,'V1':V1,'Omega':Om,'Theta':Th,'F9':out}

def main():
    selective=audit(ROOT/'upstream/code_v1.json')
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    pinchecks=0
    for rec in pins['current_pin_authenticated_files']+pins['inherited_proof_files']:
        raw=(ROOT/rec['local_path']).read_bytes();require(digest(raw)==rec['sha256'],'source SHA256')
        if 'git_blob_sha' in rec:require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==rec['git_blob_sha'],'source Git blob')
        pinchecks+=1
    binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text());ports={};auth=[]
    require(digest((ROOT/binding['complete_interface_proof_path']).read_bytes())==binding['complete_interface_proof_sha256'],'complete tuple proof')
    for rec in binding['payloads']:
        packed=(ROOT/rec['path']).read_bytes();raw=gzip.decompress(packed)
        require(digest(packed)==rec['gzip_sha256'],'gzip hash');require(digest(raw)==rec['sha256'],'payload hash')
        value=int.from_bytes(raw,'little');require(value.bit_length()==rec['bit_length'],'bitlength');ports[rec['name']]=value;auth.append(rec['name'])
    ports={name:ports[alias] for name,alias in binding['port_aliases'].items()}
    fresh={};rebuild=0
    for bridge in ('three','two','calibrated'):
        for pos in (False,True):
            for cert in (False,True):
                body=build(pos,cert,bridge);label=bridge+'_'+('positive' if pos else 'natural')+('_certificate' if cert else '')
                saved=json.loads((ROOT/f'generated/{label}.json').read_text());saved.pop('exact_degree')
                require(saved==body,'rebuild '+label);fresh[label]=body;rebuild+=1
                require(len([n for n in body['nodes'] if n['kind']=='variable'])==9,'nine unknowns')
                require(body['coefficient_bound_exponent']==2134927,'coefficient bound')
    boundchecks=0
    for rec in fresh['calibrated_natural']['coefficient_recipes']:
        value=sum(t['coefficient']*math.prod(ports[n]**e for n,e in zip(('beta','K0','MC','MF'),t['powers'])) for t in rec['terms'])
        require(abs(value)<1<<2134927,'actual coefficient bound');boundchecks+=1
    rng=random.Random(20261023);replays=0;registers=0
    for bridge in ('three','two','calibrated'):
        bn=fresh[bridge+'_natural'];bc=fresh[bridge+'_natural_certificate'];bp=fresh[bridge+'_positive'];bpc=fresh[bridge+'_positive_certificate']
        for p in (1000003,1000033,1000037):
            pm={n:x%p for n,x in ports.items()};fixed={}
            for rec in bn['coefficient_recipes']:
                fixed[rec['name']]=sum(t['coefficient']*math.prod(pow(pm[n],e,p) for n,e in zip(('beta','K0','MC','MF'),t['powers'])) for t in rec['terms'])%p
            fixed['base_scale']=pow(2,KAPPA,p)
            if bn['threshold_scale_exponent'] is not None:fixed['threshold_scale']=pow(2,bn['threshold_scale_exponent'],p)
            for case in range(40):
                v={n:rng.randrange(0,100) for n in bn['variables']};b=2*(v['epsilon']+1)**2 if bridge=='two' else v['epsilon']+2
                wanted,regs=literal(v,pm,p,bridge);got,named=evaluate(bn,fixed,v,p)
                require(got==wanted,'independent formula');require(all(named[n]==x for n,x in regs.items()),'independent named register');registers+=len(regs)
                require(evaluate(bc,fixed,v,p)[0]==wanted,'certificate identity')
                vp={n:m+1 for n,m in zip(bp['variables'],v.values())}
                require(evaluate(bp,fixed,vp,p)[0]==wanted,'positive translation');require(evaluate(bpc,fixed,vp,p)[0]==wanted,'positive certificate')
                replays+=1
    local=0
    for B in (8,16,32,64):
        for h in range(-B//4+1,B//4):
            for incoming in (-1,0):
                a=2*h+1+incoming;require(((a%B)&(B-2)==0)==(h==0),'signed target padding')
                require(a//B in (-1,0),'target outgoing borrow');require((2*h+incoming)//B in (-1,0),'ordinary outgoing borrow');local+=1
    carries=0
    for u in range(1,9):
        L=1<<u
        for S in range(L):
            for T in range(L-S):
                R=L*L+(S+T)*L+L-1-S
                threshold=u+T.bit_count()+1
                require((R.bit_count()>=threshold)==(S&T==0),'two-block carry identity')
                carries+=1
    calibration=0
    for kap in (20,22,24):
        for k in range(1,15):
            v=kap+2*k;ulog=1+k+5741*v;tpop=206*v-31*k-22
            nexponent=(15*kap//2-10)+2966*v
            require(2*nexponent==ulog+tpop+1,'square threshold exact exponent');calibration+=1
    # Exact polynomial identity in two indeterminates: coefficient dictionaries.
    def add(a,b,sg=1):
        c=a.copy()
        for k,x in b.items():c[k]=c.get(k,0)+sg*x
        return {k:x for k,x in c.items() if x}
    def mul(a,b):
        c={}
        for x,v in a.items():
            for y,w in b.items():k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+v*w
        return {k:x for k,x in c.items() if x}
    def pw(a,n):
        z={(0,0):1}
        for _ in range(n):z=mul(z,a)
        return z
    tt={(1,0):1};dd={(0,1):1};one={(0,0):1}
    approx=mul(tt,{(0,2):8,(0,1):-4,(0,0):-1})
    df=add(mul(mul(pw(tt,2),pw(dd,3)),add(dd,one,-1)),dd)
    err=add(mul(pw(tt,2),{(0,1):8,(0,0):1}),{(0,1):64},-1)
    require(add(add(pw(approx,2),{k:64*v for k,v in df.items()},-1),err,-1)=={},'near-square exact polynomial identity')
    majorants=0
    for A,C,i,G,H in product(range(2,5),range(2,5),range(1,4),range(2,5),range(1,4)):
        J=4*A-5;D=(A*A-1)*C*C+1;t=i*J*C;E=t*D*C;F=(A*A-1)*E*E+1;I=(G*G-1)*H*H+1;S0=t*(8*D*D-4*D-1)
        require(S0*S0-64*D*F==t*t*(8*D+1)-64*D>0,'near-square majorant')
        require((S0*G*H)**2>64*D*F*I,'root majorant');majorants+=1
    finalizers=0
    for r0,r1,u,q,mu in product(range(1,5),range(1,5),range(1,4),range(1,4),range(1,4)):
        a0=r0*r0;a1=r1*r1;V0=r0+1;V1=r1+1;M=q;v=u*q
        for sg0,sg1 in product((-1,1),repeat=2):
            Z=M+V0*V1+sg0*r0+sg1*V0*r1;n=(2*mu-1)*Z-q;O=u*(2*mu-1);Th=u*n+v-O*(M+V0*V1)
            require(n>=0 and (Th*Th-O*O*(a0+V0*V0*a1))**2-4*O**4*V0*V0*a0*a1==0,'finalizer completeness');finalizers+=1
    degrees={}
    for bridge in ('three','two','calibrated'):
        cert=degree_certificate(fresh[bridge+'_natural_certificate']);saved=json.loads((ROOT/f'generated/{bridge}_natural_degree.json').read_text());require(cert==saved,'degree exact');degrees[bridge]=cert['exact_degree']
    result=dict(status='PASS',source_provenance_checks=pinchecks,authenticated_ports=auth,selective_code=selective,reproduced_circuits=rebuild,actual_recipe_bounds=boundchecks,modular_literal_replays=replays,independent_named_register_checks=registers,local_sparse_borrow_cases=local,two_block_carry_cases=carries,calibrated_square_threshold_cases=calibration,near_square_polynomial_identity='exact zero',majorant_cases=majorants,finalizer_completeness_cases=finalizers,exact_degrees=degrees,scope='Finite implementation/data audits; universal equivalence is the mathematical proof with explicitly imported compiler and Jones ratio theorems.')
    (ROOT/'generated/VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
