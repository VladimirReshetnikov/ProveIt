"""Independent literal audit of the relocated-anchor quadratic system.

Imports no producer module. Unbounded arithmetic remains a mathematical proof.
"""
import json,hashlib,sys,argparse
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parents[1]/'root'

def P(ts):
 out={}
 for c,m in ts:
  if type(c) is not int or not c or m!=sorted(m) or len(m)>2:raise ValueError('bad monomial')
  mon=tuple(m)
  if mon in out:raise ValueError('duplicate monomial')
  out[mon]=c
 return out

def v(i):return {(i,):1}
def c(n):return {():n} if n else {}
def plus(*pp):
 d=defaultdict(int)
 for p in pp:
  for m,a in p.items():d[m]+=a
 return {m:a for m,a in d.items() if a}
def times(*pp):
 p={():1}
 for q in pp:
  d=defaultdict(int)
  for m,a in p.items():
   for n,b in q.items():d[tuple(sorted(m+n))]+=a*b
  p={m:a for m,a in d.items() if a}
 return p
def neg(p):return {m:-a for m,a in p.items()}
def coeff(k,p):return {m:k*a for m,a in p.items() if k*a}
def minus(p,q):return plus(p,neg(q))
def sq(p):return times(p,p)
def substitute(p,i,e):
 ans={}
 for m,a in p.items():ans=plus(ans,times(c(a),*(e if j==i else v(j) for j in m)))
 return ans

def need(ok,msg):
 if not ok:raise ValueError(msg)

def main(profile=221,parent_path=None,target_dir=None,receipt_path=None):
 parent=parent_path or ROOT/'158-pooled-powers/equation/equation.json'
 target_dir=target_dir or ROOT/f'anchor{profile}'
 output=target_dir/'equation.json'
 raw=parent.read_bytes();orig=json.loads(raw);target=json.loads(output.read_bytes())
 old=[P(r['terms']) for r in orig['residuals']]
 t,x,F,B,yp,C=[v(i) for i in (0,1,2,4,5,17)]
 A=plus(v(142),c(1));q=minus(v(102),c(1));K=v(100) if profile!=219 else coeff(1<<20,t)
 # name table: (D,Y,Z,index), with genuine affine offsets.
 seeds=[(v(146),v(147),v(148),t),
        (v(155),v(156),v(157),plus(F,t)),
        (v(158),minus(v(159),c(1)),v(160),minus(v(9),c(1))),
        (v(161),v(162),v(163),v(10)),
        (v(164),v(165),v(166),v(11)),
        (v(167),v(168),v(169),v(12)),
        (v(170),v(171),v(172),v(13)),
        (v(173),v(174),v(175),yp),
        (v(176),v(177),v(178),v(14)),
        (v(179),v(180),v(181),v(15)),
        (v(182),v(183),plus(v(184),c(1)),x),
        (v(185),v(186),v(187),v(16)),
        (v(188),v(189),v(190),C),
        (v(191),v(192),v(193),K)]
 edits={}
 edits[105]=plus(v(149),sq(t),coeff(-2,times(A,t)),c(1))
 edits[106]=plus(F,neg(v(191)),neg(times(t,v(192))),times(v(149),v(150)))
 reps=[minus(v(9),c(1))]+[v(i) for i in range(10,18)]
 H=plus(c(2),coeff(4,plus(*reps)))
 edits[138]=minus(v(194),times(B,H))
 edits[139]=plus(t,c(-128 if profile==221 else -16),coeff(-4,sq(v(195))))
 edits[144]=minus(v(208),sq(v(189)))
 edits[148]=plus(v(198),neg(v(188)),neg(v(190)),neg(times(v(196),v(204))))
 edits[149]=plus(v(199),neg(C),coeff(-4,times(v(189),v(205))))
 edits[153]=plus(sq(v(189)),neg(sq(C)),c(-1),
     *(neg(sq(Y)) for d,Y,z,k in seeds if Y!=v(189)),
     neg(sq(v(212))),neg(sq(v(213))),neg(sq(v(214))),neg(v(214)))
 orientation={}
 for d,Y,Z,k in seeds:
  X=plus(d,Z)
  norm=plus(sq(X),sq(Y),neg(sq(Z)),c(-1))
  orientation=plus(orientation,sq(minus(X,c(1))),sq(minus(Y,k)),neg(norm))
 edits[150]=plus(orientation,neg(times(v(142),v(209))))
 rs=[106,110,113,116,119,123,126,130,134,137]
 edits[154]=plus(sq(v(128)),c(-1),*(coeff(-4,sq(v(i))) for i in rs),neg(sq(v(215))),neg(sq(v(216))),neg(sq(v(217))),neg(v(217)))
 atoms=[t,plus(t,c(1)),plus(F,t),x,t,B,F,yp]+reps+[v(18),K,q,v(102),v(194)]
 outputs=[103,104,108,111,114,117,120,121,124,127,128,132,135]
 atoms += [v(i) for i in outputs]
 edits[137]=plus(v(141),c(-2),*(neg(sq(p)) for p in atoms))
 # Explicit power-request matching verifies frame membership.
 requests=[(t,K,F),(B,x,v(18)),(v(194),x,q)]
 plus_positions=[1,2,3,4,5,6,8,9,11,12]
 plus_outputs=[103,108,111,114,117,120,124,127,132,135]
 Hpool={};Spool={}
 for seed_i,oi in zip(plus_positions,plus_outputs):
  d,Y,Z,k=seeds[seed_i];X=plus(d,Z);m=v(oi)
  Hpool=plus(Hpool,times(Y,minus(m,X)))
  Spool=plus(Spool,sq(minus(m,d)),neg(sq(Y)))
  requests.append((v(102),k,m))
 edits[158]=plus(v(221),coeff(-2,Hpool),neg(times(minus(coeff(2,A),v(102)),v(222))))
 edits[159]=plus(Spool,neg(times(v(102),v(221))),v(222))
 for seed_i,oi in [(0,104),(7,121),(10,128)]:requests.append((q,seeds[seed_i][3],v(oi)))
 need(len(requests)==16,'request count')
 for no,(n,k,m) in enumerate(requests):
  for atom in (n,k,m):need(atom in atoms,f'unbounded power atom {no}')
 # Check the principal multiplication/norm rows survive with those offsets.
 for si,(d,Y,Z,k) in enumerate(seeds):
  need(plus(Z,neg(times(A,Y))) in old or neg(plus(Z,neg(times(A,Y)))) in old,f'AY row {si}')
  X=plus(d,Z);norm=plus(sq(X),sq(Y),neg(sq(Z)),c(-1))
  need(norm in old or neg(norm) in old,f'norm row {si}')
 deleted={0,86,99,155,156};expected=[]
 for i,r in enumerate(old):
  if i in deleted:continue
  p=edits.get(i,r)
  p=substitute(p,3,F);p=substitute(p,17,coeff(2,v(17)))
  need(max(map(len,p),default=0)<=2,f'degree row {i}')
  expected.append(p)
 beta_rhs = times(F,plus(coeff(2,v(225)),c(1)))
 expected.append(plus(yp,c(-1),neg(beta_rhs)))
 if profile==221:expected += [minus(v(226),sq(t)),minus(K,sq(v(226)))]
 elif profile==220:expected.append(minus(K,coeff(1<<20,t)))
 live=sorted({i for p in expected for m in p for i in m});ren={a:b for b,a in enumerate(live)}
 expected=[{tuple(ren[i] for i in m):a for m,a in p.items()} for p in expected]
 actual=[P(r['terms']) for r in target['residuals']]
 need(expected==actual,'literal final residual mismatch')
 need(len(live)==profile and len(expected)==profile-61,'final counts')
 need(target['parent_equation_sha256']==hashlib.sha256(raw).hexdigest(),'parent hash')
 certificate=json.loads((target_dir/'certificate.json').read_bytes())
 need(certificate['original_to_final']==[[i,ren[i]] for i in live],'renumbering mismatch')
 # Collect quartic directly, independent of emitter arithmetic.
 quartic=plus(*(sq(p) for p in actual))
 receipt={'ok':True,'parent_sha256':hashlib.sha256(raw).hexdigest(),'equation_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'quadratic_rows_checked':len(actual),'variables':len(live),'power_requests':len(requests),'frame_atoms':len(atoms),'degree':max(map(len,quartic)),'monomials':len(quartic),'height':max(map(abs,quartic.values())),'evidence_scope':'exact finite source delta, offsets, anchor rows, norms, 16 power requests, and coefficient collection; not an unbounded formal proof'}
 print(json.dumps(receipt,indent=2))
 receipt_path=receipt_path or Path(__file__).parent/f'anchor{profile}_audit.json'
 receipt_path.parent.mkdir(parents=True,exist_ok=True)
 receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--profile',type=int,choices=[219,220,221],default=221);parser.add_argument('--parent-equation',type=Path);parser.add_argument('--target-dir',type=Path);parser.add_argument('--receipt',type=Path);args=parser.parse_args();main(args.profile,args.parent_equation,args.target_dir,args.receipt)
