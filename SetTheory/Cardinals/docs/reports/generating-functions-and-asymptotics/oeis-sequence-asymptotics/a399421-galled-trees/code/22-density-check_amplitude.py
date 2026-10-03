"""Portable replay adapter; the original arithmetic is unchanged.
All inputs and output destinations are explicit command-line options.
"""
import argparse
from pathlib import Path
import mpmath as m,json
parser=argparse.ArgumentParser(description="Independent scalar amplitude diagnostic.")
parser.add_argument('--reference', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--dps', type=int, default=85)
args=parser.parse_args()
m.mp.dps=args.dps
reference=json.loads(args.reference.read_text())['A397952']
assert reference['offset']==0
seq=reference['values']
known=seq[:]
seq=[0,1];S=[0,1]
for n in range(2,161):
 num=sum(seq[i]*seq[n-i] for i in range(1,n))+(seq[n//2] if n%2==0 else 0)+sum(S[i]*S[n-1-i] for i in range(1,n-1))+(S[(n-1)//2] if n%2 else 0)
 assert num%2==0
 seq.append(num//2)
 S.append(seq[n]+sum(seq[i]*S[n-i] for i in range(1,n)))
assert seq[:len(known)]==known
A=lambda z:m.fsum(m.mpf(a)*z**i for i,a in enumerate(seq))
D=lambda z:m.fsum(m.mpf(a)*i*z**(i-1) for i,a in enumerate(seq) if i)
f=lambda r,s:(r+s*s/2+A(r*r)/2+r/2*((s/(1-s))**2+A(r*r)/(1-A(r*r)))-s,s+r*s/(1-s)**3-1)
r,s=m.findroot(f,(m.mpf('.2344'),m.mpf('.4349')))
b=A(r*r);d=D(r*r)
ww=1+r*(1+2*s)/(1-s)**4
t=lambda d:1+r*d+s*s/(2*(1-s)**2)+b/(2*(1-b))+r*r*d/(1-b)**2
out=dict(r=r,s=s,b=b,derivative=d,phit=t(d),phiww=ww,delta=m.sqrt(2*r*t(d)/ww),finite_diff=(A(r*r)-A(r*r-m.mpf('.001')))/m.mpf('.001'),delta_finite_diff=m.sqrt(2*r*t((A(r*r)-A(r*r-m.mpf('.001')))/m.mpf('.001'))/ww),paper_inputs_delta=m.sqrt(2*m.mpf('.2344')*m.mpf('1.6716')/m.mpf('5.2993')))
out={k:str(v) for k,v in out.items()}
print(json.dumps(out,indent=2))
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(out,indent=2)+'\n')
