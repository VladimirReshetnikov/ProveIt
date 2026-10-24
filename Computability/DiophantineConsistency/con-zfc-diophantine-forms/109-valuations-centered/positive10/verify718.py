"""Independent exact-arithmetic finite audits for circuit718; not a proof assistant."""
from pathlib import Path
import sys, gzip, hashlib, json, random, math, itertools
sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).parent))
import circuit718 as c
COEFF=Path(__file__).resolve().parent/'coefficients'
PORTFILES={'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'}
BIND={
'beta':('466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c','0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'),
'K0':('b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a','c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e'),
'MC':('271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e','6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4'),
'MF':('935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b','48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737')}
def require(a,msg):
    if not a: raise RuntimeError(msg)
def ports():
    result={}
    for k,f in PORTFILES.items():
        z=(COEFF/f).read_bytes(); r=gzip.decompress(z)
        require(hashlib.sha256(z).hexdigest()==BIND[k][0], 'gzip hash '+k)
        require(hashlib.sha256(r).hexdigest()==BIND[k][1], 'raw hash '+k)
        result[k]=int.from_bytes(r,'little')
    return result

def direct(env,p):
    beta,K0,MC,MF=[env[k] for k in c.FIXED]
    j,F,alpha,i,T,w,Y,n,eta,zeta=[env[k] for k in c.WITNESSES]
    J=2*j+1; q=beta*J+1; X=w*q; a=(X+1)*Y; k=eta+zeta; cc=k*Y+eta
    mu=q*q+1; Ap=mu*(a+2)+1; Dp=Ap*Ap-1; Hp=4*Ap-5; ap=Ap-2
    V0=X*mu*mu*Y*Y; Dtau=V0*(V0+1)*k*k+1
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    e=k-R-1; Bt=(K0+w)*(q-F-alpha)-F
    I=i*cc*cc; Df=1+Dp*I*I; Q=Dp*Dp*I*I; delta=Q-1
    Tp=T+alpha; bp=cc*Tp-R; V=Df*bp-cc
    Dnum=Q*V*V-1; Dmain=Dp*cc*cc+1
    Cf=mu*Ap*I; Ct=(V0+1)*k; L=bp+cc*Tp; W=1+(q-1)*L
    P1=q**3*(q-1); Mtot=P1*mu*mu*Hp
    Znum=P1*mu*mu*(Hp*(n+V+Cf+Ct)+X+ap*cc)+Hp*(mu*mu*((q-1)*Y-q**3*W*Bt)-P1*e)
    s=delta*Znum*Znum % p
    A=delta*Mtot*Mtot*Dtau % p; B=delta*Mtot*Mtot*mu*mu*Df % p
    C=Mtot*Mtot*Dnum % p; D=delta*(P1*mu*mu)**2*Dmain % p
    s1=A+B+C; s2=A*B+(A+B)*C; s3=A*B*C
    U=s+D; Po=U-s1; Pe=Po*Po+4*(s*D-s2)
    Ge=Pe*Pe+16*(s*D*Po*Po-4*s3*U); Go=Pe*Po-16*s3
    N=(Ge*Ge-64*s*D*Go*Go) % p
    return {k:v%p for k,v in locals().copy().items() if isinstance(v,int)}

def leader(direction, beta, p):
    j,F,alpha,i,T,w,Y,n,eta,zeta=[direction[k] for k in c.WITNESSES]
    q=2*beta*j; k=eta+zeta; cc=k*Y; mu=q*q; A=mu*w*q*Y
    D=A*A; I=i*cc*cc; Df=D*I*I; Q=D*Df
    R=q**3*(q-F); Bt=w*(q-F-alpha)
    V=-Df*R; Cf=mu*A*I; Ct=w*q*mu*mu*Y*Y*k
    M=q**8*4*A; rem=R*Bt
    return 2**14*pow(Q,8,p)*pow(M,16,p)*pow(V,8,p)*pow(Cf,4,p)*pow(Ct,2,p)*rem*rem % p

def audit():
    src=c.rows(); avail=set(c.WITNESSES+c.FIXED)
    for name,op,a,b in src:
        require(name not in avail,'unique '+name)
        require(op in ['+','-','*'],'op')
        require(all(isinstance(x,int) or x in avail for x in [a,b]),'forward ref')
        avail.add(name)
    live={'N'}
    for name,op,a,b in reversed(src):
        if name in live: live.update(x for x in [a,b] if isinstance(x,str))
    require(all(r[0] in live for r in src),'dead row')
    require(set(c.WITNESSES+c.FIXED)<=live,'dead input')
    from collections import Counter
    counts=dict(Counter(r[1] for r in src)); require(len(src)==126,'count')
    packet=json.loads(Path(__file__).with_name('equation718.json').read_text())
    require(packet['source']==[list(r) for r in src], 'literal JSON source')
    ports_=ports()
    require(ports_['beta']+1 == 1 << 590069, 'fixed base')
    require(0 < ports_['MC'] < ports_['beta'] < ports_['MF'] < 2*ports_['beta'], 'mask bounds')
    require(ports_['K0']>0,'K0 positive')
    results={'operations':len(src),'breakdown':counts,'ports_bound':True,'syntactic_degree':c.syntactic_degrees(src)['N'],'degree_lines':[]}
    p=2**127-1; rng=random.Random(20261023)
    for it in range(20):
        env={k:v%p for k,v in ports_.items()}; env.update({v:rng.randrange(1,p) for v in c.WITNESSES})
        got=c.evaluate(src,env,mod=p); expected=direct(env,p)
        for key in ['I','Df','Q','V','Cf','L','W','Mtot','Znum','N']:
            require(got[key]==expected[key], 'direct register '+key)
    results['independent_formula_points']=20
    for p in [2**127-1,2**89-1]:
        pp={k:v%p for k,v in ports_.items()}
        for line in range(2):
            offset={x:rng.randrange(1,100) for x in c.WITNESSES}
            direction={x:rng.randrange(1,100) for x in c.WITNESSES}
            vals=[]
            for t in range(833):
                env=dict(pp);env.update({x:(offset[x]+direction[x]*t)%p for x in c.WITNESSES})
                vals.append(c.evaluate(src,env,mod=p)['N'])
            diffs=[]
            while vals:
                diffs.append(vals[0]);vals=[(b-a)%p for a,b in zip(vals,vals[1:])]
            deg=max(i for i,v in enumerate(diffs) if v)
            require(deg==718,'degree718')
            lc=diffs[718]*pow(math.factorial(718)%p,-1,p)%p
            target=leader(direction,pp['beta'],p)
            require(lc==target and target!=0,'exact leading coefficient')
            results['degree_lines'].append({'prime':str(p),'degree':deg,'leading_coefficient':str(lc),'predicted_leader_matches':True})
    Path(__file__).with_name('CHECKS718.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':audit()
