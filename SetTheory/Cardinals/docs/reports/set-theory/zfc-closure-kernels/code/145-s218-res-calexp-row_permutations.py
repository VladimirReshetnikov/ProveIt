from compose_membership219 import *

NAMES=['rho8','G','rho6','left_sub','interchange','right_sub','distribution','exist_eq','bundle']
def make(choices):
 words=[]
 for idx,formula in enumerate(o.FORMULAS):
  p=choices.get(idx,('a','b','c'));m=dict(zip(('a','b','c'),p))
  word=[m.get(k,k) for k in o.postfix(formula,set())]
  words.append(word)
 ats=sum((o.atoms(o.M[k])for w in words for k in w),())
 t=o.compose(ats)
 # Imported source equality optimization is unchanged as an independent closed macro.
 t,paths=compose(t)
 return t,words,paths

if __name__=='__main__':
 out=ROOT/'row_permutation_results';out.mkdir(exist_ok=True);rs=[]
 best=206
 for idx in range(9):
  perms=list(itertools.permutations(('a','b','c'))) if idx!=8 else [('a','b','c'),('b','a','c')]
  for p in perms:
   t,words,paths=make({idx:p});m=z.s.metrics(t)
   r={'row':idx,'row_name':NAMES[idx],'permutation':p,'source_metrics':m,'equality_replacements':paths}
   if m['dag_nodes']<207:
    d=out/(NAMES[idx]+'_'+''.join(p));d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(z.s.sites(t)))
    r['sites_file']=str(d/'sites.json')
   rs.append(r)
   print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(rs,indent=2)+'\n')
