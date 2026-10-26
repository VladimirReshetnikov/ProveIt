"""Three certified natural-domain projections from the source164 equation.

Two use canonical sign lifts; the third has a pointwise natural inverse whose
nonnegativity follows from a retained square row. See NATURAL_PROOF.md.
"""
from pathlib import Path
import json,hashlib,sys
sys.dont_write_bytecode=True
import reduce_radical as r
ROOT=Path(__file__).resolve().parent
def write(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')

def one(eq,names,pivot_name,row_output,tag):
 names2={v['name']:i for i,v in enumerate(eq['variables'])}
 v=[0]*len(names2)
 for name,c in names.items():v[names2[name]]=c
 p=names2[pivot_name]
 # The source row containing this output linearly and as the highest index is
 # selected only if it is the exact requested monic definition.
 rid=next(j for j,row in enumerate(eq['residuals']) if r.norm(row['terms']).get((names2[row_output],))==1 and all(i<=names2[row_output] for _,mon in row['terms'] for i in mon))
 new,c=r.project(eq,v,p,rid);c['domain_justification']=tag
 return new,c

def emit(eq,cert,out):
 pp=r.add(*(r.mul(r.norm(x['terms']),r.norm(x['terms'])) for x in eq['residuals']))
 equation=dict(eq);equation['variant']='canonical_nonnegative_quadratic_projection';equation['metrics']=r.metric(equation,True)
 # Binding is against the raw output used by the checker, before the metadata
 # addition above; mathematical coefficient arrays are identical.
 write(out/'equation.json',eq);write(out/'metrics.json',r.metric(eq,True));write(out/'projection_certificate.json',cert)
 write(out/'expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','domain':'nonnegative integers','variables':len(eq['variables']),'terms':r.terms(pp)})
 print(out.name,r.metric(eq,True),flush=True)

if __name__=='__main__':
 source=json.loads((ROOT/'natural_source206.json').read_text())
 eq=source;cs=[]
 eq,c=one(eq,{'mul.363':1,'mul.369':1},'mul.363','mul.363','canonical g9 = mul369 - mul363 >= 0');cs.append(c)
 eq,c=one(eq,{'mul.372':1,'mul.373':1},'mul.373','mul.373','canonical g10 = mul372 - mul373 >= 0');cs.append(c)
 emit(eq,{'schema':'common_hessian_radical_projection_v1','steps':list(cs)},ROOT/'natural204')
 eq,c=one(eq,{'mul.299':1,'mul.304':-4},'mul.299','mul.299','pointwise natural: y304=x304+4*x299; restored x304=add302*(add302+1) by retained row');cs.append(c)
 emit(eq,{'schema':'common_hessian_radical_projection_v1','steps':list(cs)},ROOT/'natural203')
