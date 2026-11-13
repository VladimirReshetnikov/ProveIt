from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-parent-even-index-coprime-discriminant-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expressions(g):
 e={v:('var',v) for v in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:e[name]=(op,e[a] if isinstance(a,str) else ('lit',a),e[b] if isinstance(b,str) else ('lit',b))
 return e
p,q=expressions(parent),expressions(child)
for name in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[name]==q[name]
rows={row[0]:row[1:] for row in parent['source']}
for x,r in {'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],'Fs':['+',1,'g72'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'out':['-','P0123',1]}.items():assert rows[x]==r
for a in range(4):
 for f in range(4):
  for I in range(4):assert (1+I*I-(a*a+4*a+3)*(f*f-1))%4!=3
# Discover least positive integer-coordinate units by an independent finite search.
ds=[2,3,5,6,7,10,11,13,15];units={}
for d in ds:
 for x in range(2,2000):
  if (x*x-1)%d:continue
  z=(x*x-1)//d;y=math.isqrt(z)
  if y*y==z and y>0:units[d]=(x,y);break
 assert d in units and all(d%(j*j) for j in range(2,math.isqrt(d)+1))

def seq(d,a,b,n):
 X,U=1,0;out=[(X,U)]
 for _ in range(n):X,U=a*X+d*b*U,b*X+a*U;out.append((X,U))
 return out
hits=tests=gcdtests=0
for d,(a,b) in units.items():
 S=seq(d,a,b,48)
 for j in range(1,20):
  for k in range(1,20):
   assert math.gcd(S[j][1],S[k][1])==S[math.gcd(j,k)][1];gcdtests+=1
 for r in (1,2,3):
  A,t=S[r];delta=A*A-1;assert delta==d*t*t
  for m in (2,4,6):
   if math.gcd(m,delta)!=1:continue
   rm=r*m;assert S[rm][1]%t==0;c=S[rm][1]//t
   assert math.gcd(c,delta)==1 and 2*S[rm//2][0]>t and c>S[rm//2][1]
   for h in range(1,2*rm+1):
    u=S[h][1];g=math.gcd(h,rm)
    if u%c==0:
     assert S[g][1]%c==0 and rm%g==0 and g==rm and h%rm==0
     hits+=1
    if u%(c*c)==0:
     assert h%rm==0
    tests+=1
assert hits>0 and tests>0
# Valuation cancellation and conversion to the original A-Pell sequence.
for d in ds:
 for t in range(1,13):
  Delta=d*t*t
  for I in range(201):
   if I*I%Delta==0:assert I%(d*t)==0
# Nonfundamental example independently identified by discovered least unit.
d=7;a,b=units[d];S=seq(d,a,b,6);A,t=S[3];assert (a,b,A,t)==(8,3,2024,765)
m=2;rm=6;c=S[rm][1]//t
assert c==2*A and S[rm][1]==t*c and c>S[rm//2][1] and math.gcd(m,A*A-1)==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'parent_unit_rows_and_mod4_checked':True,
 'independently_discovered_integer_units':len(units),'strong_divisibility_controls':gcdtests,
 'index_and_growth_controls':tests,'divisibility_hits':hits,
 'nonfundamental_example_checked':True,'integer_pell_classification_assumed':True,
 'conditional_same_data_only':True,'lean_executed':False},indent=2,sort_keys=True))
