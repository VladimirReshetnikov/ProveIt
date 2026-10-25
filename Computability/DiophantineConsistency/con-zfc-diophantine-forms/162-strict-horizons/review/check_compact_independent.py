#!/usr/bin/env python3
"""Independent direct-formula and topology checks of the free-Y scale charts."""
from pathlib import Path
from collections import Counter
import argparse, json, random, hashlib

HERE=Path(__file__).resolve().parent
DEFAULT_SOURCE=HERE.parent/"compact"
P=2**127-1
def req(ok,msg):
    if not ok:raise ValueError(msg)

def formula(vals,ports,corrected,mod):
    J,F,alpha,i,T,w,s,n,eta,zeta=[vals[k] for k in
        ("J","F","alpha","i","T","w","s","n","eta","zeta")]
    beta,K0,MC,MF=[ports[k] for k in ("beta","K0","MC","MF")]
    h=beta*J;q=h+1;C=q-F-alpha;Y=s;k=eta+zeta;c=k*Y+eta
    wb=w if corrected else q*w;X=q*wb;d=6*q**7 if corrected else q**7
    A=q*Y*(X+1)+1;delta=A*A-1;H=4*A-5
    v=X*q*q*Y*Y;E=1+v*(v+1)*k*k
    R=(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    B=(K0+wb)*C-F;U=i*c*c;a=delta*U*U*E;F0=1+a;G=E*F0
    Fs=1+4*a*F0;Q=delta*(Fs-1);b=c*(T+alpha)-R;V=Fs*b-c
    K=X*(3*c-2*X)+2;L=b*V
    ec=(6*(k-R-1)-v*(R+1)*(R-1)*(R+3)-6*q**4*s
        if corrected else k-R-1-q**4*s)
    M=h*d*H;Z=h*d*(H*(n-L*B)+K)-H*(d*B+h*ec)
    return (Q*(Z*Z-M*M*G*V*V)+(M*M*G-Z*Z))%mod

def evaluate(e,vals,ports,mod):
    env={**vals,**ports};degree={k:1 for k in vals};degree.update({k:0 for k in ports})
    uses=Counter()
    def get(x):
        return x%mod if isinstance(x,int) else env[x]
    def deg(x):
        return 0 if isinstance(x,int) else degree[x]
    for name,op,x,y in e["source"]:
        req(name not in env,"duplicate")
        a,b=get(x),get(y)
        env[name]=({"+":lambda:a+b,"-":lambda:a-b,"*":lambda:a*b}[op]())%mod
        degree[name]=deg(x)+deg(y) if op=="*" else max(deg(x),deg(y))
        if isinstance(x,str):uses[x]+=1
        if isinstance(y,str):uses[y]+=1
    out=e.get("output","N")
    req(out in env,"output")
    live={out}
    for name,op,x,y in reversed(e["source"]):
        if name in live:
            if isinstance(x,str):live.add(x)
            if isinstance(y,str):live.add(y)
    req(all(row[0] in live for row in e["source"]),"dead operation")
    req(all(k in live for k in e["witnesses"]+e["fixed_numerals"]),"unused input")
    return env[out],degree[out]
def audit(source=DEFAULT_SOURCE):
    rng=random.Random(20261025);results={}
    for filename,corrected,expected_ops,expected_degree in [
        ("equation_83_degree312.json",False,83,312),
        ("equation_89_degree278.json",True,89,278)]:
        e=json.loads((source/filename).read_text())
        req(len(e["source"])==expected_ops,"count")
        for k in range(80):
            vals={name:rng.randrange(1,20) for name in e["witnesses"]}
            beta=rng.randrange(16,50)*2+1
            ports={"beta":beta,"K0":rng.randrange(1,70),
                   "MC":rng.randrange(1,beta),"MF":rng.randrange(beta+1,2*beta)}
            actual,degree=evaluate(e,vals,ports,P)
            req(actual==formula(vals,ports,corrected,P),"formula mismatch")
            req(degree==expected_degree,"degree upper bound")
        results[filename]={"operations":len(e["source"]),"degree_upper_bound":degree,
                          "formula_checks":80,"topology_and_liveness":"pass",
                          "sha256":hashlib.sha256((source/filename).read_bytes()).hexdigest()}
    return {"status":"pass","scope":"topology, degree upper bounds, direct-formula modular regression; exact degree established in review",
            "results":results}

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",nargs="?",type=Path,default=DEFAULT_SOURCE)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    rendered=json.dumps(audit(args.source),indent=2)+"\n"
    if args.output:args.output.write_text(rendered)
    print(rendered,end="")

