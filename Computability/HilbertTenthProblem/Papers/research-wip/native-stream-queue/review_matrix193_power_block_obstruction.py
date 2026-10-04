#!/usr/bin/env python3
import json,hashlib,argparse
from pathlib import Path
from fractions import Fraction
ap=argparse.ArgumentParser(description='Independent bounded matrix193 source and affine loader review.')
ap.add_argument('--root',type=Path,required=True)
ap.add_argument('--author-root',type=Path)
mode=ap.add_mutually_exclusive_group(required=True)
mode.add_argument('--output',type=Path)
mode.add_argument('--expect',type=Path)
args=ap.parse_args()
ROOT=args.root.resolve()
AUTH=(args.author_root.resolve() if args.author_root else ROOT)/'matrix193_power_block_obstruction'
EXPECTED={'py':'a6c77d2625d760d5435723c9124eb187201c17c378e386ad62faf3c0cf351fc9','json':'16985a6eac0ff6df74cfc2a141e24d150f581134e547916d1a5eaace3fd8fc34','md':'60f442caa77c68f11c73a4995fbebc4582a0ef64b3a9e41dfd68c27d8782d978'}
def ok(v,s):
 if not v: raise ValueError(s)
for ext,h in EXPECTED.items(): ok(hashlib.sha256(Path(str(AUTH)+'.'+ext).read_bytes()).hexdigest()==h,ext)
a=json.loads(Path(str(AUTH)+'.json').read_text())
ok(a['source_sha256']==EXPECTED['py'],'author self-source hash')
for name,h in a['parent_pins'].items(): ok(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==h,name)
p=json.loads((ROOT/'group_directed_semigroup193.json').read_text())['packet']
I=(1,0,0,1);P=(1,2,0,1)
def mul(a,b):
 A,B,C,D=a;E,F,G,H=b
 return (A*E+B*G,A*F+B*H,C*E+D*G,C*F+D*H)
def inv(a):
 A,B,C,D=a;ok(A*D-B*C==1,'det');return D,-B,-C,A
def ep(j):return (1+4*j,2,-8*j*j,1-4*j)
def phi(w):
 z=I
 for c in w:z=mul(z,ep(p['top_codes'][c]))
 return z
def block(u,v):return [[u[0],u[1],0,0],[u[2],u[3],0,0],[0,0,v[0],v[1]],[0,0,v[2],v[3]]]
tiles={z['id']:z for z in p['tiles']}
for g in p['generators']:
 if g['name']=='C':u,v=inv(phi(p['terminal']+'#')),P
 else:
  t=tiles[g['tile_id']]
  if g['name'].startswith('A'):u,v=phi(t['h']),ep(t['id'])
  else:u,v=inv(phi(t['g'])),mul(mul(inv(P),inv(ep(t['id']))),P)
 ok(block(u,v)==g['matrix'],g['name'])
ok(len(p['generators'])==193,'193')
N=tuple(e-i for e,i in zip(ep(2),I));ok(mul(N,N)==(0,0,0,0),'nilpotence')
L=inv(phi('A0]#'));R=inv(phi('['));c=mul(L,R);s=tuple(-v for v in mul(mul(L,N),R))
u=a['unary_target'];cf=u['fixed_coefficients']
for k,ij in enumerate(('00','01','10','11')):
 ok(cf['constant_'+ij]==c[k] and cf['slope_'+ij]==s[k],ij)
# Independent linear polynomial evaluation of all eight supplied rows.
env={k:(v,0) for k,v in cf.items()};env['x']=(0,1)
for dst,op,l,r in u['source']:
 ok(dst not in env and l in env and r in env,'closure');A,B=env[l];C,D=env[r]
 if op=='+':env[dst]=(A+C,B+D)
 else:
  ok(op=='*' and B*D==0,'linear');env[dst]=(A*C,A*D+B*C)
ok([env[k] for k in u['upper_outputs']]==list(zip(c,s)),'affine coefficients')
ok(sum(row[1]=='*' for row in u['source'])==4 and len(u['source'])==8,'eight gates')
live=set(u['upper_outputs'])
for d,op,l,r in reversed(u['source']):
 ok(d in live,'dead gate');live.update((l,r))
det=(c[0]*c[3]-c[1]*c[2],c[0]*s[3]+s[0]*c[3]-c[1]*s[2]-s[1]*c[2],s[0]*s[3]-s[1]*s[2])
ok(det==(1,0,0),'det polynomial')
# Distinct binary-power evaluator, including negative exponent values.
def power(a,n):
 if n<0:a,n=inv(a),-n
 z=I
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
xs=[-17,-2,-1,0,1,2,3,7,16,31,64,128,257]
for x in xs:
 v=tuple(C+x*S for C,S in zip(c,s));expected=inv(mul(mul(phi('['),power(ep(2),x)),phi('A0]#')))
 ok(v==expected,'signed power')
 if x>=0:ok(v==inv(phi('['+'1'*x+'A0]#')),'literal word')
out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'status':'PASS','author_pins':EXPECTED,'parent_pins':a['parent_pins'],'matrix_entries':3088,'gates':8,'affine_coefficients':[list(x) for x in zip(c,s)],'determinant_coefficients':list(det),'signed_exponent_values':xs,'scope':'Independent closed-form conjugates and flat matrix arithmetic; no predecessor code executed; no semilinear algorithm or universal unary loader certified.'}
def same(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b
if args.expect:
 ok(same(out,json.loads(args.expect.read_text())), 'exact typed receipt')
else:
 args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('PASS: 193 matrices / 3088 entries, 8 live gates, affine determinant, 13 signed exponents.')
