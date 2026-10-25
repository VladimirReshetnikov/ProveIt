#!/usr/bin/env python3
"""Build four complete DAGs; no upstream execution and no network."""
import ast,json
from pathlib import Path
from circuit import DAG,export
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def assignments(path):
 tree=ast.parse(path.read_text());out={}
 for n in tree.body:
  if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ['VARS','REGS']:
   out[n.targets[0].id]=ast.literal_eval(n.value)
 return out

def build_one(tag,variables,regs,degree):
 d=DAG(variables);e={x:d.leaf('variable',x) for x in variables};e.update({x:d.leaf('coefficient',x) for x in PORTS})
 for name,formula in regs:e[name]=eval(formula,{'__builtins__':{}},e)
 p=export(tag,d,e['P'],{n:e[n] for n,_ in regs},{'exact_degree':degree,'fixed_numerals':PORTS,'proof':'PROOF.md'})
 p['coefficient_binding']='baseline/coefficients/BINDING.json'
 (ROOT/(tag+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 (ROOT/(tag+'_spec.json')).write_text(json.dumps({'variables':variables,'registers':regs,'degree':degree},indent=2)+'\n')
 return {k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']}
def main():
 a=assignments(ROOT/'baseline/build.py');b=assignments(ROOT/'baseline/thirteen/build.py');metrics=[]
 for tag,src,degree in [('integer14_degree88_ops115',a,88),('integer13_degree156_ops125',b,156)]:
  regs=[]
  for name,form in src['REGS']:
   if name in ['strong','auxiliary']:form=form[:-2]
   if name=='P':form=form.replace('(strong+1)','strong').replace('(auxiliary+1)','auxiliary')
   regs.append([name,form])
  metrics.append(build_one(tag,src['VARS'],regs,degree))
 regs=[]
 for name,form in b['REGS']:
  if name=='G':regs.extend([['Bg','budget-p1**2-p2**2'],['G','4*Bg-3']]);continue
  if name=='auxiliary':form=form[:-2]
  if name in ['Dt','U2','ga','db','fc','gc','inner','N','P']:continue
  regs.append([name,form])
 regs.extend([['inner','s*(s+1)-Bg-Ds'],['N','inner**2-G*Fs'],['P','(carrier+1)*(N+1)*auxiliary-1']])
 metrics.append(build_one('integer14_degree94_ops110',b['VARS']+['s'],regs,94))
 regs=[]
 for name,form in a['REGS']:
  if name in ['pos2','G','auxiliary','UG','N','P']:continue
  if name=='strong':form=form[:-2]
  regs.append([name,form])
 regs.extend([['Bg','budget-p1**2-p2**2'],['G','4*Bg-3'],['delta','Q-1'],['Cy','Q*V**2-1'],['inner','delta*(s*(s+1)-Bg+1)-Cy'],['N','inner**2-G*delta*Cy'],['P','(carrier+1)*strong*(N+1)-1']])
 variables=[x for x in a['VARS'] if x not in ['y','p3']]+['p1','s']
 metrics.append(build_one('integer14_degree86_ops112',variables,regs,86))
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics))
if __name__=='__main__':main()
