"""New exact supplements for the optional smooth-radix construction."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
def need(x,msg):
    if not x:raise RuntimeError(msg)
def v2(n):return (n&-n).bit_length()-1
def geom(B,N,mod):return (pow(B,N,(B-1)*mod)-1)//(B-1)%mod
def run():
    periods=crt=heights=margins=0
    for r in range(1,26):
        d=5**r;m=275*d
        for j in range(25):
            t=4400*d*(1<<j)
            need(t%(4*5**(r+1))==0 and t%10==0,'Euler periods')
            need(v2(t)==j+4 and(t>>v2(t))==m,'odd part')
            need(pow(2,t,m)==1,'actual power residue')
            need((t//d)%1100==0 and 4*m<=t//4,'block and exponent bounds')
            periods+=1
    for d in [5,25,125]:
        B=1<<d
        for x in [1,10,10**6]:
            I=2*d*x+1;Wmod=None
            for K in [991,10**12,(1<<500)-1]:
                hK=K.bit_length();H0=max(I,hK);t=4400*d;j=0
                while t<4*H0:t*=2;j+=1
                need(t<=max(4400*d,8*H0),'minimal height bound')
                need(I<=t//4 and hK<=t//4,'logarithmic margins')
                need(j==0 or 4*H0<=t<8*H0,'dyadic rounding')
                heights+=1;m=275*d;a=j+4;N=t//d
                q=pow(2,t,t);J=geom(B,N,t);MC=6;MF=12+B-1
                M=(MC+q*MF)*J%t;e0=M%m;e=next(e0+i*m for i in range(4) if(e0+i*m)%4==3)
                Z=(e-M)%(1<<a) or(1<<a)
                need(3<=e<1100*d<=t//4 and Z%4==1,'CRT representative')
                C=(pow(2,I,t)+Z)%t;F=(K+pow(2,e,t))*C%t
                R=((q*q-Z-q*F)*(q*q-1)+M)%t
                need(R==e,'literal packing residue')
                need(geom(B,N,55)==0 and pow(B,N,55)==1,'55-block divisibility')
                crt+=1
    for t in range(64,4097,4):
        need(3*t<=1<<(t//4),'linear margin')
        need((1<<(t//2+2))+(1<<(t//4+1))<(1<<t),'new total bound')
        margins+=1
    return dict(status='PASS',scope='Optional radix lemma supplements only; full theorem is symbolic',
        smooth_period_cases=periods,height_selection_cases=heights,literal_CRT_cases=crt,margin_cases=margins,
        mock_ports_are_not_claimed_genuine_compilers=True,saved_schedule_executions=0,upstream_code_executions=0,
        original_full_proof_sha256='dc886e8991e32c331b9135b4ea6b3f73733656be3df6c2aa01576e1732fb83e1',
        addendum_sha256=hashlib.sha256((ROOT/'SMOOTH_RADIX.md').read_bytes()).hexdigest())
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--expect',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
    if args.output:
        p=args.output.resolve();need(not p.is_relative_to(ROOT),'Packet output forbidden');need(not p.exists(),'Fresh output required')
        if args.expect:need(p!=args.expect.resolve(),'Expected file overwrite forbidden')
    output=(json.dumps(run(),indent=2)+'\n').encode()
    if args.expect:need(args.expect.read_bytes()==output,'Receipt byte mismatch')
    if args.output:
        with args.output.open('xb') as f:f.write(output)
    print(output.decode(),end='')
