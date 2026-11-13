from pathlib import Path
from hashlib import sha256
import json,math,sys,resource
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(15,15))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
D=Path('reviews/ordinary13-shifted-two-norm-parent-odd-index-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
# Actual graph fields used by the inherited parent construction.
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expr(g):
 e={v:('var',v) for v in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:
  e[name]=(op,e[a] if isinstance(a,str) else ('num',a),e[b] if isinstance(b,str) else ('num',b))
 return e
p,q=expr(parent),expr(child)
for x in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[x]==q[x]
rows={r[0]:r[1:] for r in parent['source']}
for x,r in {'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],
 'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],
 'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'F0':['+',1,'A0'],
 'F1':['+',1,'A1'],'Fs':['+',1,'g72'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[x]==r
# Independent matrix power, also applicable to the odd quotient recurrence.
def mm(a,b,n):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%n for i in range(2) for j in range(2))
def mp(a,e,n):
 z=(1,0,0,1)
 while e:
  if e&1:z=mm(z,a,n)
  a=mm(a,a,n);e//=2
 return z
def pell(A,n):
 d=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+d*y,x+A*y
 return x,y
# Check the same-index period and the oddness of f for both parities of A.
for A in range(2,8):
 d=A*A-1
 for m in (1,2,3):
  g,c=pell(A,m);h=2*m*c
  assert mp((A,d,1,A),h,c*c)==(1%(c*c),0,0,1%(c*c))
  f,v=pell(A,h)
  assert v%(c*c)==0 and f%2==1 and f*f-d*v*v==1
  half,_=pell(A,h//2);assert f==2*half*half-1
  assert mp((A,d,1,A),2*h*f,f*f)==(f*f-1,0,0,f*f-1)
  if m%4==1:
   L=2*h*f-m
   assert L>=m and L%4==3 and L%c==(-m)%c
   assert mp((A,d,1,A),L,f*f)[2]==c%(f*f)
# Exact full auxiliary fact-level witness for an odd A, not an actual graph zero.
A=3;m=1;g,c=pell(A,m);h=2*m*c;f,v=pell(A,h);delta=A*A-1;I=delta*v
L=2*h*f-m;R=2;z,y=pell(I,L)
assert (c,h,f,v,I,L)==(1,2,17,6,48,67)
assert z%I==0;V=z//I;num=V+c+f*f*R
assert num%(f*f*c)==0;T=num//(f*f*c)
assert T>0 and V==f*f*(T*c-R)-c and I*I==delta*(f*f-1)
assert y*y-I*I*(y*y-V*V)==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'parent_auxiliary_rows_checked':True,'small_period_controls':18,'both_multiplier_parities_checked':True,
 'exact_odd_multiplier_A':3,'exact_odd_multiplier_m':1,
 'exact_odd_multiplier_auxiliary_index':67,'exact_auxiliary_witness_checked':True,
 'scope':'source-level conditional lift; no unrestricted witness or model claim',
 'lean_executed':False},indent=2,sort_keys=True))
