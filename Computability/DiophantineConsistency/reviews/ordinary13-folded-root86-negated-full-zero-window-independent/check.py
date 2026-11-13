#!/usr/bin/env python3
"""Independent symbolic toy-zero and scalar-window checks; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-full-zero-window'
toy=D/'reviews/ordinary13-folded-root86-toy-full-zero-independent';floor=D/'reviews/current14-carrier64-pell-floor-independent';shift=D/'reviews/ordinary13-folded-root86-negated-shift-repair-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','f55501ef059c0cdeed010e402784f49105d909d80e07e3b53287cc77153468c1'),(P/'check.py','f4e0d255ff3f3c51dc7fdb1e15cd7bb62be487e821b9e09cf5c1f35659dd2089'),(P/'result.json','b91a4c94d136677cc0266d0c5e40dc322892450783ba5a59989611012d368028'),(toy/'check.py','19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b'),(toy/'result.json','900aebfa8b65363d44e889525fc0eeb6c0b6b6c356fdec94f99db8f43260bf3a'),(floor/'check.py','65ff9800b15d3313eaecb3f595851f355f9e7b0c8f811afd46187cc95c9f6839'),(floor/'result.json','042e585bfc7e47b8212eabeb5271cdb8b2e5e9b64f28e53e995f2690fbe9b0b3'),(shift/'check.py','b1b3d764930b0358844d8e5d7c115b13cfed7d1763d0ca41db05e2587cc45f37'),(shift/'result.json','59340826c196fa654f38085f5c60ce49d187f428b9729e4945fcf6821c4b77b8')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-full-zero-window-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='1d02ec13b2b7f745dc6b9bff33a78bc73b1dd9363c1d116fa1de09bbbf80e7e8'
for p in (P,toy,floor,shift):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
g=json.loads((D/'research/ordinary13-folded-root86-negated/candidate.json').read_text()); deps={n:{n} for n in g['witnesses']+g['fixed_numerals']}
for n,op,a,b in g['source']:
 deps[n]={n} if n=='R' else set().union(*(deps[x] for x in (a,b) if isinstance(x,str)))
assert all(not ({'F','alpha','MC','r'} & deps[n]) for n in ('A1','Fa','g72'))
# Instance 1: exact rank retention from the previously reviewed full toy zero.
b,q=31,32;R=998911;oldG=b*(q-1)+14;newG=b*(q-1)+45
assert newG-oldG==31 and 14-(-31699)==31*(q*q-1)
assert oldG*(q*q-1)+14+q*46==R==newG*(q*q-1)-31699+q*46
assert (q-1-45)==-14 and (-14*(pow(2,R,b)+9*q)-q)%b==0
# Instance 2: all four ports positive, distinct from compact44. No enormous
# binomial or Pell witness is expanded: check the exact scalar and exponents.
R2=2**20-1;N=(R2-1)//2;G=b*(q-1)+34
assert G==995 and G*(q*q-1)+30658+q==R2 and min(31,9,30658,1)>0
assert R2%4==3 and R2%5==0 and N==2**19-1 and N.bit_count()-1==18 and pow(2,R2,b)==1
assert (q-1-34)==-3 and (-3*(pow(2,R2,b)+9*q)-q)%b==0 and R2>=26 and R2>10
# The q³ divisibility follows from the proved central-binomial valuation;
# 18 >= v2(q³)=15. F=1 forces the stated repair cap to zero in both cases.
assert 18>=15 and min(1-1,(34-1)//b)==0 and min(1-1,(45-1)//b)==0
# Independent finite analogue of the c-th strong unit and auxiliary R=3
# congruences, not a computation of the enormous symbolic witnesses.
def pell_power(a,n):
 delta=a*a-1;x,y=1,0
 for _ in range(n):x,y=a*x+delta*y,x+a*y
 return x,y
a=4;D0,c=pell_power(a,3);f,L=pell_power(D0,c);delta=a*a-1
# pell_power(D0,c) uses D0²−1=delta*c², so its coefficient is L*c.
L*=c;assert f*f-delta*L*L==1 and L%(c*c)==0
S=delta*L;xx,y=pell_power(S,3);assert xx%S==0;V=xx//S
assert f*f%c==1 and (V+c)%(f*f)==0 and (V+3)%c==0 and (V+c+f*f*3)%(c*f*f)==0 and y>V>0
print(json.dumps({'status':'PASS_SCOPED_SYMBOLIC_TOY_CONSTRUCTIONS','negative_MC_rank':R,'positive_ports':[31,9,30658,1],'positive_rank':R2,'binomial_v2':18,'two_scalar_windows_empty':True,'scope':'symbolic toy zeros relying on cited unbounded Pell arguments; no compact44 or unrestricted nonequivalence claim; no Lean'},indent=2))
