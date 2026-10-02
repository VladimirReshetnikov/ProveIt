#!/usr/bin/env python3
"""Independent exact Hall reconstruction and packed-exponent certificate audit."""
if not __debug__:raise SystemExit('Run without -O: assertions are required.')
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from math import comb
import argparse,hashlib,json,time
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--data-dir',type=Path,default=Path('/workspace/shared/incomplete-two-by-three-complete-exteriors'))
p.add_argument('--output-dir',type=Path,default=Path(__file__).parent)
args=p.parse_args();started=time.monotonic()
def pack(e):
 assert len(e)==8 and all(type(x)is int and 0<=x<256 for x in e)
 return sum(x<<(8*i) for i,x in enumerate(e))
def unpack(e):return tuple((e>>(8*i))&255 for i in range(8))
def multiply(a,b):
 out={}
 for k,x in a.items():
  for l,y in b.items():out[k+l]=out.get(k+l,0)+x*y
 return {k:v for k,v in out.items() if v}
def gap(a,b,c):
 out=multiply(b,b)
 for k,x in multiply(a,c).items():out[k]=out.get(k,0)-2*x
 return {k:v for k,v in out.items() if v}
def selected_feasible(mask,I,J,nx,ny):
 # Direct Hall test on the selected full physical subgraph, not the core-rank shortcut.
 rows=[]
 for i in I:
  rows.append(sum(1<<jj for jj,j in enumerate(J) if mask>>(3*i+j)&1)|sum(1<<(len(J)+h) for h in range(ny)))
 rows += [(1<<len(J))-1]*nx
 for used in range(1,1<<len(rows)):
  n=0
  for i,row in enumerate(rows):
   if used>>i&1:n|=row
  if n.bit_count()<used.bit_count():return False
 return True
hall_cases=0
def coefficients(mask):
 global hall_cases
 out=[{}for k in range(6)]
 for im in range(4):
  I=[i for i in range(2) if im>>i&1]
  for jm in range(8):
   J=[j for j in range(3) if jm>>j&1]
   for k in range(6):
    nx,ny=k-len(I),k-len(J)
    if not(0<=nx<=3 and 0<=ny<=2):continue
    hall_cases+=1
    if not selected_feasible(mask,I,J,nx,ny):continue
    exp=tuple(int(i in I) for i in range(2))+tuple(int(j in J) for j in range(3))+(int(nx==2),int(nx==3),int(ny==2))
    key=pack(exp);out[k][key]=out[k].get(key,0)+1
 return out
def relabel(mask,pl,pr):
 return sum(1<<(3*pl[i]+pr[j]) for i in range(2)for j in range(3) if mask>>(3*i+j)&1)
perms=[(pl,pr)for pl in permutations(range(2))for pr in permutations(range(3))]
polys={m:coefficients(m)for m in range(64)}
classes={}
for m in range(64):classes.setdefault(min(relabel(m,*pp) for pp in perms),[]).append(m)
assert sorted(classes)==[0,1,3,7,9,10,11,14,15,27,29,31,63]
assert sorted(x for xx in classes.values()for x in xx)==list(range(64))
relabel_checks=0
for rep,members in classes.items():
 for m in members:
  pl,pr=next(pp for pp in perms if relabel(rep,*pp)==m)
  perm=list(pl)+[2+j for j in pr]+[5,6,7]
  for a,b in zip(polys[rep],polys[m]):
   moved={}
   for key,val in a.items():
    ee=[0]*8
    for i,n in enumerate(unpack(key)):ee[perm[i]]=n
    moved[pack(ee)]=val
   assert moved==b;relabel_checks+=1
def cone(raw,k):
 dv,dw,dz=(2,2,0) if k==2 else (4,2,2)
 out={}
 for key,c in raw.items():
  e=unpack(key);i,j,l=e[5:]
  assert i+2*j<=dv and l<=dw and (k==2 or j<=dz)
  factor=F(c,2**(i+l)*6**j)
  for h in range(dv-i-2*j+1):
   for hh in range(dw-l+1):
    for hhh in (range(dz-j+1) if k==3 else [0]):
     ee=e[:5]+(i+2*j+h,l+hh,j+hhh if k==3 else 0)
     value=factor*comb(dv-i-2*j,h)*comb(dw-l,hh)*(comb(dz-j,hhh) if k==3 else 1)
     kk=pack(ee);out[kk]=out.get(kk,F(0))+value
 return {key:c for key,c in out.items()if c},(dv,dw,dz)
def evaluate(poly,values):
 total=F(0)
 for key,c in poly.items():
  term=F(c)
  for x,n in zip(values,unpack(key)):term*=x**n
  total+=term
 return total
def phash(poly):
 data=[[list(e),str(c)]for e,c in sorted((unpack(k),v)for k,v in poly.items())]
 return hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest()
records=[];files={};substitution_checks=0
for mask,members in sorted(classes.items()):
 g=polys[mask]
 for k in [2,3]:
  raw=gap(g[k-1],g[k],g[k+1]);target,den=cone(raw,k)
  # Direct rational evaluations verify denominator clearing independently of expansion.
  for vv,ww,zz in [(F(1),F(2),F(3)),(F(3,2),F(2,3),F(1,4))]:
   core=[F(2),F(3),F(5),F(7),F(11)]
   mm=vv/(2*(1+vv));ss=ww/(2*(1+ww));nn=vv**2/(6*(1+vv)**2)
   if k==3:nn*=zz/(1+zz)
   assert evaluate(target,core+[vv,ww,zz])==evaluate(raw,core+[mm,nn,ss])*(1+vv)**den[0]*(1+ww)**den[1]*(1+zz)**den[2]
   substitution_checks+=1
  file=args.data_dir/f'core_{mask}_gap_{k}.json';data=json.loads(file.read_text());files[file.name]=hashlib.sha256(file.read_bytes()).hexdigest()
  meta=data['record'];assert meta['mask']==mask and meta['k']==k and tuple(meta['denominator_exponents'])==den
  assert meta['terms']==len(target) and meta['negatives']==sum(c<0 for c in target.values()) and meta['squares']==len(data['squares'])
  remainder=dict(target)
  for coefficient,(outer,left,right,rho) in data['squares']:
   c=F(coefficient);rho=F(rho);assert c>0 and rho>0
   # Validate vectors before forming all three monomials, including previously absent ones.
   pack(outer);pack(left);pack(right)
   for ee,cc in [(tuple(m+2*a for m,a in zip(outer,left)),c*rho*rho),(tuple(m+a+b for m,a,b in zip(outer,left,right)),-2*c*rho),(tuple(m+2*b for m,b in zip(outer,right)),c)]:
    kk=pack(ee);remainder[kk]=remainder.get(kk,F(0))-cc
  assert all(c>=0 for c in remainder.values())
  remainder={key:c for key,c in remainder.items()if c};assert remainder
  records.append({'mask':mask,'orbit_size':len(members),'gap':k,'squares':len(data['squares']),'positive_remainder_terms':len(remainder),'target_sha256':phash(target),'remainder_sha256':phash(remainder)})
assert sum(x['squares']for x in records)==915
assert sum(x['positive_remainder_terms']for x in records)==33318
receipt={'verdict':'PASS','method':'Independent direct selected-subgraph Hall reconstruction; packed-exponent rational expansion; no producer imports or optimizer','labeled_masks':64,'core_classes':13,'middle_certificates':26,'selected_subgraph_Hall_tests':hall_cases,'coefficient_relabel_checks':relabel_checks,'rational_substitution_checks':substitution_checks,'positive_rational_squares':915,'positive_remainder_terms':33318,'all_remainders_nonempty':True,'source_note_sha256':hashlib.sha256((args.data_dir/'ALL_CORE_MASKS_ULC.md').read_bytes()).hexdigest(),'certificate_sha256':files,'records':records,'elapsed_seconds':round(time.monotonic()-started,3)}
args.output_dir.mkdir(parents=True,exist_ok=True)
(args.output_dir/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k not in ['records','certificate_sha256']},indent=2))
