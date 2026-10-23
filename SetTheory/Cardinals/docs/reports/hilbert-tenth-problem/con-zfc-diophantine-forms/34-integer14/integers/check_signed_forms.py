"""Independent modular matrix-norm and signed-core replay; not a formal proof."""
from pathlib import Path
import json,random,math,hashlib
from itertools import combinations_with_replacement
from circuit_support import evaluate,audit_body
from build_signed_forms import build,degree_data
HERE=Path(__file__).resolve().parent
def need(v,s):
 if not v:raise RuntimeError(s)
def determinant(a,p):
 a=[r[:] for r in a];out=1;n=len(a)
 for j in range(n):
  k=next((k for k in range(j,n) if a[k][j]%p),None)
  if k is None:return 0
  if k!=j:a[k],a[j]=a[j],a[k];out=-out
  q=a[j][j]%p;out=out*q%p;inv=pow(q,-1,p)
  for k in range(j+1,n):
   f=a[k][j]*inv%p
   for t in range(j,n):a[k][t]=(a[k][t]-f*a[j][t])%p
 return out%p
def norm_matrix(X,S,c,a,b,w1,w2,p):
 rad=[c,a,b];weights=[1,w1,w2];mat=[[0]*8 for _ in range(8)]
 for mask in range(8):
  mat[mask][mask]=X
  for j in range(3):
   row=mask^(1<<j);fac=rad[j] if mask&(1<<j) else 1
   mat[row][mask]=(mat[row][mask]-S*weights[j]*fac)%p
 return determinant(mat,p)
def actual_fixed(co,ports,p):
 L=co['L'];s=co['index_exponent'];z=pow(2,s,p);fx={'z_index':z}
 for row in co['coefficient_records']:
  v=0
  for term in row['coefficient_polynomial_in_fixed_ports']:
   t=term['coefficient']
   for a,e in zip(ports,term['powers']):t=t*pow(a%p,e,p)%p
   v+=t
  fx[row['name']]=v%p
 B=2*z%p;five=[5**j for j in range(co['nu']+1)];tot=0
 for inds in combinations_with_replacement(range(-1,co['nu']+1),4):
  expo=sum(five[j] for j in inds if j>=0);tot=(tot+pow(B,L-expo,p))%p
 y=z*tot
 for row in co['coefficient_records']:y+=fx[row['name']]*pow(B,L-row['expo'],p)
 fx['y_index']=y%p;fx['b_floor']=pow(2,(s+1)*(L+1),p);fx['b_floor_odd']=2*fx['b_floor']%p
 return fx
def main():
 if not __debug__:raise RuntimeError('Run without -O or -OO')
 rng=random.Random(202610230253);base=json.loads((HERE/'source_core31.json').read_text());receipts={}
 for small,tiny,rj in [(True,True,True),(False,True,True)]:
  body=build(base,small,tiny,rj);name=body['variant'];saved=json.loads((HERE/(name+'.json')).read_text())
  need(body['nodes']==saved['nodes'] and body['output']==saved['output'],'regeneration')
  compares=0;norms=0
  for p in [1009,65537,1000003]:
   for _ in range(80):
    fixed={nd['name']:rng.randrange(1,p) for nd in base['nodes'] if nd['kind']=='fixed'}
    fixed['b_floor']=rng.randrange(1,p);fixed['b_floor_odd']=rng.randrange(1,p)
    vv={x:rng.randrange(-20,21) for x in body['variables']}
    expected={x:vv.get(x,0) for x in base['variables']}
    if small:expected['epsilon']=(fixed['b_floor_odd' if tiny else 'b_floor']*vv['epsilon']**2-fixed['y_index']-1)%p
    if tiny:expected['w0']=(vv['wroot']**2-1)%p
    if rj:
     for old,new in [('h0','h'),('i0','i'),('j0','j')]:expected[old]=(vv[new]-1)%p
    old=evaluate(base,fixed,expected,p);new=evaluate(body,fixed,vv,p)
    get=lambda s:new[body['named_nodes'][s]]
    for nm in ['b','B','q','ell','lambda','e','N','Gcap','R','U','Y','M','P','K','A','Wsmall','C','J','Q','D','E','F','Gp','H','I','a0','a1','margin']:
     need(get(nm)==old[base['named_nodes'][nm]],name+': core '+nm);compares+=1
    stackname=max((s for s in body['named_nodes'] if s.startswith('guard_stack')),key=lambda x:int(x[11:]))
    direct=norm_matrix(get('Xnorm'),get('Smerge'),get(stackname),get('a0'),get('a1'),get('weight1'),get('weight2'),p)
    need(direct==new[body['output']],name+': matrix norm');norms+=1
  receipts[name]={**audit_body(body),**degree_data(body),'signed_core_named_comparisons':compares,'independent_matrix_norm_checks':norms,'sha256':hashlib.sha256((HERE/(name+'.json')).read_bytes()).hexdigest()}
 guardchecks=0
 for length in range(1,8):
  for _ in range(200):
   ds=[3*rng.randrange(-4,5)+2 for _ in range(length)];zs=[rng.choice([-3,-2,-1,1,2,3]) for _ in range(length)];cc=1;fs=[]
   for d,z in zip(ds,zs):
    f=1+4*d*cc*z*z;need(f%4==1 and math.gcd(f,cc)==1 and abs(f)>=3,'guard algebra');fs.append(f);cc*=f
   need(abs(cc)>1 and cc*cc>abs(cc),'small signed weight')
   if cc>=0 and math.isqrt(cc)**2==cc:need(all(d>0 for d in ds),'guard implication')
   guardchecks+=1
 intersect=0;valuation=0
 for modulus in range(1,501):
  need(any(((t**3-t-1)*(t*t+23))%modulus==0 for t in range(modulus)),'intersectivity');intersect+=1
 for D in range(-12,13):
  if not D:continue
  for T in range(-12,13):
   for Z in range(-5,6):
    for v in range(-3,4):
     r=T+D*v;q=(r**3-D*D*r-D**3)*(r*r+23*D*D);need(q!=0,'intersective nonzero')
     den=Z*D**5
     if den and q%den==0:need(T%D==0 and Z!=0,'valuation implication')
     valuation+=1
 co=json.loads((HERE/'INDEX_CONSTANTS.json').read_text());binding=json.loads((HERE/'SIGNED_BINDING.json').read_text());payload=HERE/binding['native_tuple_directory'];ports=[]
 need(hashlib.sha256((HERE/'INDEX_CONSTANTS.json').read_bytes()).hexdigest()==binding['index_constants_sha256'],'index hash')
 need(hashlib.sha256((HERE/'source_core31.json').read_bytes()).hexdigest()==binding['source_core_sha256'],'core hash')
 native=json.loads((payload/'COEFFICIENT_BINDING.json').read_text())
 for name in ['beta','K','MC','MF_source']:
  data=(payload/(name+'.bin')).read_bytes();ports.append(int.from_bytes(data,'little'))
  need(hashlib.sha256(data).hexdigest()==binding['native_payload_sha256'][name],'native payload hash')
 actual=[]
 for p in [1009,65537,1000003]:
  fx=actual_fixed(co,ports,p)
  for name,small,tiny,rj,ex12 in [('signed14',True,True,True,120),('signed15_linear',False,True,True,248)]:
   body=build(base,small,tiny,rj);dd=degree_data(body,fx,p)
   expected=pow(2,832,p)*pow(12,ex12,p)%p
   if small:expected=expected*pow(fx['b_floor_odd'],406528*co['L']+8,p)%p
   need(dd['leading_diagonal_residue']==expected and expected!=0,'actual leading coefficient')
   for _ in range(10):
    vv={x:rng.randrange(-9,10) for x in body['variables']};ns=evaluate(body,fx,vv,p);get=lambda s:ns[body['named_nodes'][s]]
    last='guard_stack4' if small else 'guard_stack5'
    need(norm_matrix(get('Xnorm'),get('Smerge'),get(last),get('a0'),get('a1'),get('weight1'),get('weight2'),p)==ns[body['output']],'actual fixed norm')
   actual.append({'name':name,'prime':p,'leading_residue':expected,'matrix_checks':10})
 receipts.update(status='PASS',scope='Finite diagnostics supplement the mathematical proofs; no consistency or actual halting witness is searched for.',guard_stack_checks=guardchecks,intersective_moduli=intersect,divisibility_checks=valuation,actual_fixed_checks=actual)
 (HERE/'SIGNED_CHECKS.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps({k:v for k,v in receipts.items() if not isinstance(v,dict)},indent=2))
if __name__=='__main__':main()
