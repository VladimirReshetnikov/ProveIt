from pathlib import Path
from hashlib import sha256
import itertools,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-shifted85-free-aux-square-criterion')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
a=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());b=json.loads((D/'candidate.json').read_text())
assert len(a['source'])==85 and len(b['source'])==84 and a['fixed_numerals']==b['fixed_numerals']
assert a['witnesses'][11]=='n_y' and b['witnesses'][11]=='n_y2'
expected=[]
for n,op,x,y in a['source']:
 if n=='y2':assert (op,x,y)==('*','n_y','n_y');continue
 expected.append([n,op,'n_y2' if x=='y2' else x,'n_y2' if y=='y2' else y])
assert expected==b['source']
def tree(g,repl=None):
 d={x:('var',i) for i,x in enumerate(g['witnesses'])};d.update({x:('port',i) for i,x in enumerate(g['fixed_numerals'])})
 if repl:d['n_y2']=('*',('var',11),('var',11))
 for n,op,x,y in g['source']:d[n]=(op,d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
 return d[g['output']]
assert tree(a)==tree(b,True)
# Generic unit sign exclusions for first, main and strong patterns modulo 4.
for b0,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b0)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b0*b0*(1+ell*(ell+k)))%4!=3
for u,a0,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(3+4*a0+a0*a0)*c*c))%4!=3
for I,a0,f in itertools.product(range(4),repeat=3):
 assert (1+I*I-(3+4*a0+a0*a0)*(f*f-1))%4!=3
# Pell quotient iff direct auxiliary algebra for independent small fields.
controls=0
for f in range(1,7):
 for c in range(1,7):
  for i in range(1,4):
   I=c*c*i
   if I<=1:continue
   x,y=1,0
   for m in range(1,7):
    x,y=I*x+(I*I-1)*y,x+I*y
    assert (x%I==0)==(m%2==1)
    if m%2==0:continue
    for eps in (-1,1):
     V=eps*(x//I)
     for R in range(-3,8):
      num=V+c+f*f*R;den=f*f*c
      if num%den:continue
      T=num//den
      if T<1:continue
      assert V==f*f*(T*c-R)-c
      assert y*y-I*I*(y*y-V*V)==1
      controls+=1
assert controls>0
assert 'theorem solution_index' in Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shifted_zeta_parent_rows':85,'candidate_rows':84,'exact_forward_tree_identity':True,
 'three_generic_mod4_unit_exclusions':True,'Pell_quotient_sufficiency_controls':controls,
 'reverse_criterion_universally_discharged':False,'lean_executed':False},sort_keys=True,indent=2))
