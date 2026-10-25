#!/usr/bin/env python3
"""Independent exact algebra and literal-artifact checks; standard library only.

These finite checks do not prove the unbounded Pell or native-calibration
theorems. Those arguments and their precise inherited boundaries are in
PROOF.md and inherited/.
"""
from pathlib import Path
import argparse
import copy
import gzip
import hashlib
import json
import random
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FILES = ["equation_83_436.json", "equation_80_750.json", "equation_81_560.json"]
CHECKS = []


def require(condition, message):
    if not condition:
        raise ValueError(message)
    CHECKS.append(message)


class Ring:
    """An exact sparse polynomial over Z, used for free algebra identities."""
    def __init__(self, data):
        self.d = {k: v for k, v in data.items() if v}
    @staticmethod
    def lift(a):
        return a if isinstance(a, Ring) else Ring({(): a})
    def __add__(self, b):
        d = dict(self.d)
        for m, c in self.lift(b).d.items(): d[m] = d.get(m, 0) + c
        return Ring(d)
    __radd__ = __add__
    def __neg__(self): return Ring({m: -c for m, c in self.d.items()})
    def __sub__(self, b): return self + -self.lift(b)
    def __rsub__(self, b): return self.lift(b) + -self
    def __mul__(self, b):
        d = {}
        for m, c in self.d.items():
            for n, a in self.lift(b).d.items():
                k = tuple(sorted(m+n)); d[k] = d.get(k, 0) + c*a
        return Ring(d)
    __rmul__ = __mul__
    def __pow__(self, n):
        r = Ring.lift(1)
        for _ in range(n): r = r*self
        return r


def symbolic_identities():
    names = ["h", "m", "H", "t", "s", "n", "L", "B", "K", "e", "Q", "G", "V"]
    h,m,H,t,s,n,L,B,K,e,Q,G,V = [Ring({(x,): 1}) for x in names]
    oldM = t*h*m*H
    oldZ = t*h*m*(H*(n-s-L*B)+K)+H*(m*(h*t*s-t*B)-t*h*e)
    M = h*m*H
    Z = h*m*(H*(n-L*B)+K)-H*(m*B+h*e)
    require(not (oldZ-t*Z).d, "free polynomial numerator normalization")
    require(not (oldM-t*M).d, "free polynomial denominator normalization")
    N = lambda z, d: Q*(z*z-d*d*G*V*V)+(d*d*G-z*z)
    require(not (N(oldZ,oldM)-t*t*N(Z,M)).d, "entire finalizer normalization by q^6")
    require(not (N(Z,M)-((Q-1)*Z*Z-M*M*G*(Q*V*V-1))).d, "entire product-square finalizer identity")
    D,U,E = [Ring({(x,): 1}) for x in ["Delta", "U", "E"]]
    a=D*U*U*E; F0=a+1; G0=E*F0; Fsq=1+4*a*F0
    require(not (Fsq-(1+2*a)**2).d, "Pell doubling trace identity")
    require(not (D*(Fsq-1)-4*D*D*U*U*G0).d, "whole-radicand divisibility identity")
    require(not (F0-D*U*U*E-1).d, "coprime radicand factors identity")
    X,Y,mu = [Ring({(x,): 1}) for x in ["X", "Y", "mu"]]
    A=mu*Y*(X+1)+1; v=X*mu*mu*Y*Y; d=(X+1)**2-2*X*Y
    eta3=4*A*A-1-(8*v+4)*Y
    require(not (eta3-(4*mu*mu*Y*Y*d+8*mu*Y*(X+1)+3-4*Y)).d,"exact p=3 first-index-two defect identity")
    D,Fs,b,c=[Ring({(x,): 1}) for x in ["Delta", "Fsq", "b", "c"]]
    V=Fs*b-c; Q=D*(Fs-1)
    require(not ((V-(4*Q-3))-(Fs*(b-4*D)-(c-4*D-3))).d,"positive auxiliary third-index residue identity")
    require(not ((V+(4*Q-3))-(Fs*(b+4*D)-(c+4*D+3))).d,"negative auxiliary third-index residue identity")
    return 10


def topology(equation):
    inputs = equation["witnesses"]; ports=equation["fixed_numerals"]
    known=set(inputs+ports); dependencies={}; deg={x:1 for x in inputs}|{x:0 for x in ports}
    for row in equation["source"]:
        if len(row)!=4: raise ValueError("invalid row")
        name,op,a,b=row
        if name in known or op not in ["+","-","*"]: raise ValueError("invalid register")
        for arg in (a,b):
            if not isinstance(arg,int) and arg not in known: raise ValueError("forward/unknown reference")
        da=0 if isinstance(a,int) else deg[a]; db=0 if isinstance(b,int) else deg[b]
        deg[name]=da+db if op=="*" else max(da,db)
        known.add(name); dependencies[name]=[x for x in (a,b) if isinstance(x,str)]
    live=set(); stack=[equation["output"]]
    while stack:
        x=stack.pop()
        if x not in live:
            live.add(x); stack.extend(dependencies.get(x,[]))
    require(live==known,"all gates, ports and unknowns live: "+equation["name"])
    require(equation["operations"]==len(equation["source"]),"literal operation count: "+equation["name"])
    require(equation["operation_breakdown"]=={o:sum(r[1]==o for r in equation["source"]) for o in ("*","+","-")},"operation breakdown: "+equation["name"])
    require(deg[equation["output"]]==equation["exact_degree"],"global degree upper bound: "+equation["name"])
    return deg


def evaluate(equation, inputs, ports, modulus):
    values=dict(ports)|dict(zip(equation["witnesses"], inputs))
    for name,op,a,b in equation["source"]:
        x=a if isinstance(a,int) else values[a]; y=b if isinstance(b,int) else values[b]
        values[name]=({"+":lambda:x+y,"-":lambda:x-y,"*":lambda:x*y}[op]())%modulus
    return values


def formula(inputs, ports, normalized, free_t, weight):
    J,F,alpha,i,T,w,Y,n,eta,zeta=inputs
    beta,K0,MC,MF=[ports[x] for x in ["beta","K0","MC","MF"]]
    q=beta*J+1; h=q-1
    if normalized: Y=q**3*Y
    X=w*q; mu=q*q+1; k=eta+zeta; c=k*Y+eta
    A=mu*Y*(X+1)+1; D=A*A-1; H=4*A-5
    v=X*mu*mu*Y*Y; E=1+v*(v+1)*k*k
    R=(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    B=(K0+w)*(q-F-alpha)-F; e=k-R-1; U=i*c*c
    a=D*U*U*E; F0=1+a; G=E*F0; Fsq=(1+2*a)**2
    Q=4*D*D*U*U*G
    b=c*(T if free_t else T+alpha)-R; V=Fsq*b-c
    L=V*V if weight=="V^2" else b*V
    K=X*(3*c-2*X)+2
    if normalized:
        M=h*mu*mu*H
        Z=h*mu*mu*(H*(n-L*B)+K)-H*(mu*mu*B+h*e)
    else:
        P=q**3*h; M=P*mu*mu*H
        Z=P*mu*mu*(H*(n-L*B)+K)+H*(mu*mu*(h*Y-q**3*B)-P*e)
    N=(Q-1)*Z*Z-M*M*G*(Q*V*V-1)
    return N


def poly_add(a,b,p,sign=1):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]=x
    for i,x in enumerate(b): c[i]=(c[i]+sign*x)%p
    while len(c)>1 and not c[-1]: c.pop()
    return c


def poly_mul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    while len(c)>1 and not c[-1]: c.pop()
    return c


def exact_ray(equation, slopes, ports, p):
    values={k:[v%p] for k,v in ports.items()}|{k:[0,v%p] for k,v in zip(equation["witnesses"],slopes)}
    for name,op,a,b in equation["source"]:
        x=[a%p] if isinstance(a,int) else values[a]; y=[b%p] if isinstance(b,int) else values[b]
        values[name]=poly_mul(x,y,p) if op=="*" else poly_add(x,y,p,1 if op=="+" else -1)
    return values[equation["output"]]


def expected_leading(equation, slopes, ports, p):
    J,F,alpha,i,T,w,Y,n,eta,zeta=slopes
    q=ports["beta"]*J%p; k=eta+zeta
    if not equation["normalization"]["qcube"]:
        factors=[(2,14),(q,200),(w,46),(Y,104),(i,20),(k,60),(q-F,4),(q-F-alpha,2)]; sign=1
    elif equation["transport_weight"]=="V^2":
        factors=[(2,14),(q,506),(w,46),(Y,108),(i,20),(k,64),(T,4),(q-F-alpha,2)]; sign=1
    else:
        tp=T if equation["normalization"]["free_T"] else T+alpha
        factors=[(2,10),(q,384),(w,34),(Y,80),(i,14),(k,46),(tp,2)]; sign=-1
    out=sign
    for a,b in factors: out=out*pow(a,b,p)%p
    return out


def load_ports(equation):
    ports={}
    for name,entry in equation["coefficient_binding"]["ports"].items():
        data=(HERE/"coefficients"/entry["file"]).read_bytes(); raw=gzip.decompress(data)
        require(hashlib.sha256(data).hexdigest()==entry["gzip_sha256"],"coefficient compressed hash: "+name)
        require(hashlib.sha256(raw).hexdigest()==entry["raw_sha256"],"coefficient integer hash: "+name)
        value=int.from_bytes(raw,"little")
        require(value.bit_length()==entry["bits"],"coefficient bit length: "+name)
        ports[name]=value
    require(ports["beta"]>=31 and ports["beta"]%2==1 and ports["K0"]>0 and 0<ports["MC"]<ports["beta"]<ports["MF"]<2*ports["beta"],"whole fixed tuple coefficient box")
    return ports


def main():
    parser=argparse.ArgumentParser(); parser.add_argument("--output",type=Path); args=parser.parse_args()
    ledger=json.loads((HERE/"SOURCE_LEDGER.json").read_text())
    for path,entry in ledger["files"].items():
        data=(HERE/path).read_bytes()
        require(len(data)==entry["bytes"] and hashlib.sha256(data).hexdigest()==entry["sha256"],"source pin: "+path)
    symbolic_identities()
    first=json.loads((HERE/FILES[0]).read_text()); ports=load_ports(first)
    rng=random.Random(18472026); summaries=[]; mutations=0
    for name in FILES:
        equation=json.loads((HERE/name).read_text()); degrees=topology(equation)
        require(equation["coefficient_binding"]==first["coefficient_binding"],"whole tuple binding unchanged: "+name)
        parent=json.loads((HERE/equation["parent_path"]).read_text())
        require(hashlib.sha256((HERE/equation["parent_path"]).read_bytes()).hexdigest()==equation["parent_sha256"],"parent circuit pin: "+name)
        samples=[]
        for p in [1000000007,1000000009]:
            cp={k:v%p for k,v in ports.items()}
            for index in range(16):
                inputs=[rng.randrange(1,15) if index<8 else rng.randrange(-8,9) for _ in equation["witnesses"]]
                out=evaluate(equation,inputs,cp,p)[equation["output"]]
                direct=formula(inputs,cp,equation["normalization"]["qcube"],equation["normalization"]["free_T"],equation["transport_weight"])%p
                require(out==direct,"independent literal formula: "+name+f":{p}:{index}")
                q=(cp["beta"]*inputs[0]+1)%p; old=list(inputs)
                if equation["normalization"]["qcube"]: old[6]=pow(q,3,p)*inputs[6]%p;old[7]=inputs[7]-inputs[6]
                if equation["normalization"]["free_T"]: old[4]=inputs[4]-inputs[2]
                expected=out*(pow(q,6,p) if equation["normalization"]["qcube"] else 1)%p
                require(evaluate(parent,old,cp,p)[parent["output"]]==expected,"parent substitution control: "+name+f":{p}:{index}")
                samples.append((inputs,cp,p,direct))
        ray_receipts=[]
        for ray in [[1]*10,[1,2,3,2,4,3,2,1,3,2]]:
            p=1000000007; cp={k:v%p for k,v in ports.items()}; coeff=exact_ray(equation,ray,cp,p)
            lead=expected_leading(equation,ray,cp,p)
            require(lead!=0 and len(coeff)-1==equation["exact_degree"] and coeff[-1]==lead,"exact complete-ray leading coefficient: "+name+":"+str(ray))
            ray_receipts.append({"slopes":ray,"prime":p,"degree":len(coeff)-1,"leading_coefficient":lead})
        for target,operand in [("Fsqr",1),("Znum",1),("Q",1),("N",1)]:
            mutated=copy.deepcopy(equation)
            for row in mutated["source"]:
                if row[0]==target: row[1]="-" if row[1]=="+" else "+";break
            rejected=any(evaluate(mutated,inputs,cp,p)[equation["output"]]!=want for inputs,cp,p,want in samples)
            require(rejected,"rejected actual gate mutation: "+name+":"+target);mutations+=1
        summaries.append({"file":name,"variables":len(equation["witnesses"]),"operations":equation["operations"],"breakdown":equation["operation_breakdown"],"exact_degree":equation["exact_degree"],"ray_receipts":ray_receipts,"front_degrees":{k:degrees[k] for k in ["Am1","Delta","Dtau","U","DpI2","Dg","Fsqr","Q","cTR","V","Mtot","Znum"]}})
    rebuilt=subprocess.run([sys.executable,str(HERE/"build.py"),"--check"],cwd=HERE,text=True,capture_output=True)
    require(rebuilt.returncode==0,"deterministic exact builder replay")
    receipt={"status":"PASS","checks":len(CHECKS),"free_polynomial_identities":10,"rejected_gate_mutations":mutations,"equations":summaries,"scope":"Exact finite artifact and algebra checks; unbounded arithmetic and inherited calibration are ordinary proofs, not established by finite tests."}
    if args.output: args.output.write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__=="__main__": main()
