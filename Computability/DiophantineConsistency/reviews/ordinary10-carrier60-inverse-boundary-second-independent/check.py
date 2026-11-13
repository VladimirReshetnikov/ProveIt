from pathlib import Path
from hashlib import sha256
import json,random,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary10-carrier60-inverse-boundary-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary10-carrier60-inverse-boundary')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
old=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text());new=json.loads((p/'candidate.json').read_text())
assert len(old['source'])==61 and len(new['source'])==60
assert new['witnesses']==[('n_C' if x=='n_alpha' else x) for x in old['witnesses']]
expect=[]
for row in old['source']:
 n=row[0]
 if n=='alpha':expect.append(['C','+','n_C',1]);continue
 if n in ('C','g44'):continue
 if n=='G':expect.extend([['qqF','*','q','qF'],['G','-','qqF','C']]);continue
 expect.append(row)
assert expect==new['source']
# Deterministic pointwise forward/back controls with both positivity guards.
def ev(g,v,ports):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],ports))
 for n,op,x,y in g['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
rng=random.Random(0x6061);forward=inverse=0
for _ in range(400):
 v=[rng.randrange(7) for _ in range(10)];ports=[rng.randrange(1,6),rng.randrange(1,6),rng.randrange(6),rng.randrange(6)]
 a=ev(old,v,ports)
 if a['C']>0:
  w=v.copy();w[2]=a['C']-1;b=ev(new,w,ports)
  assert a['out']==b['out'] and a['G']==b['G'] and a['C']==b['C'];forward+=1
 w=[rng.randrange(7) for _ in range(10)];b=ev(new,w,ports)
 if b['qF']-b['C']>=1:
  v=w.copy();v[2]=b['qF']-b['C']-1;a=ev(old,v,ports)
  assert a['out']==b['out'] and a['G']==b['G'] and a['C']==b['C'];inverse+=1
assert forward and inverse
# Reconstruct Pell pairs by binary powering, independently of the author's
# linear recurrence loop, and evaluate the literal 60-row graph.
def pell(A,n):
 D=A*A-1;x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+D*y*v,x*v+y*u
  u,v=u*u+D*v*v,2*u*v;n//=2
 return x,y
q=2;X=34;Y=16;M=X*Y*Y;A=Y*(X+1)+2;H=4*Y*(X+1)+3;U=Y*q*q
xf,yf=pell(2*M+1,45);tau=xf;k=2*yf
main,c=pell(A,67);eta=c-Y*k
assert 0<=eta<k and tau*tau==1+M*(M+1)*k*k and main*main==1+(A*A-1)*c*c
num=main-X-(A-2)*c;assert num>0 and num%H==0
t=num//H;R=k-1+U*t;ports=[1,1,R-3,0]
v=[1,0,0,17,1,34,tau,eta,k-eta-1,0]
assert min(v)>=0 and min(ports)>=0
b=ev(new,v,ports)
assert b['q']==q and b['X']==X and b['Y']==Y and b['R']==R and b['Dstar']==U*main
assert b['Bres']==b['firstres']==b['A1']==b['out']==0 and b['qF']-b['C']==0
# Its inverse is algebraically valid only with n_alpha=-1, outside naturals.
w=v.copy();w[2]=-1;a=ev(old,w,ports);assert a['out']==0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'exact_61_to_60_source_delta':True,
 'guarded_forward_controls':forward,'guarded_inverse_controls':inverse,
 'independent_binary_Pell_full_graph_zero':True,'recovered_alpha':0,
 'signed_old_input_minus_one_is_not_natural':True,'actual_compact_ports':False,
 'global_zero_nonequivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
