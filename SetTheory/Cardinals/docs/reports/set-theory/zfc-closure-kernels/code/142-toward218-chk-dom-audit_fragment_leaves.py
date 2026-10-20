"""Instantiate checked proof DAGs, assigning unused auxiliary variables truth0."""
import check_dag as c
import json
from pathlib import Path
D=Path(__file__).parent
r=c.r;fs=r['formulas'];terms=c.terms

def vv(t):
 if isinstance(t,tuple):return vv(t[0])|vv(t[1])
 return {t} if isinstance(t,int) else set()

def walkunify(major,minor):
 m=c.rename(major,'m');n=c.rename(minor,'n')
 assert isinstance(m,tuple)
 todo=[(m[0],n)];out=m[1]
 mv={v:'m'+str(v)for v in vv(major)};nv={v:'n'+str(v)for v in vv(minor)}
 while todo:
  a,b=todo.pop(0)
  if a==b:continue
  if c.isvar(a) or c.isvar(b):
   if not c.isvar(a):a,b=b,a
   assert not c.has(b,a)
   todo=[(c.repl(x,a,b),c.repl(y,a,b))for x,y in todo]
   out=c.repl(out,a,b)
   mv={v:c.repl(x,a,b)for v,x in mv.items()};nv={v:c.repl(x,a,b)for v,x in nv.items()}
  else:
   assert isinstance(a,tuple) and isinstance(b,tuple)
   todo.extend(zip(a,b))
 names={}
 def scan(t):
  if isinstance(t,tuple):scan(t[0]);scan(t[1])
  elif c.isvar(t) and t not in names:names[t]=len(names)
 scan(out)
 return mv,nv,names

def subst(t,env,default='T'):
 if isinstance(t,tuple):return c.norm(tuple(subst(x,env,default)for x in t))
 return env.get(t,default) if t!='T' else t

def st(t):return '('+st(t[0])+'>'+st(t[1])+')' if isinstance(t,tuple) else str(t)

report={}
for goal,root in r['found'].items():
 seen=set();leaves=[]
 def walk(i,args):
  key=(i,tuple(sorted(args.items())))
  if key in seen:return
  seen.add(key);p=fs[i]['parent']
  if 'seed'in p:
   if goal=='I':
    assert p['seed'] in ['U=0','A=D→U','truth0']
    if p['seed']=='U=0':
     assert args[1]=='T'
     lr_args={0:args[0],1:'T',2:'T',3:args[2]}
     assert subst(terms[i],args)==subst(terms[2],lr_args)
   leaves.append({'seed':p['seed'],'arguments':{str(v):st(x)for v,x in args.items()},'instance':st(subst(terms[i],args))})
   return
  ma,mi=p['major'],p['minor'];mv,nv,names=walkunify(terms[ma],terms[mi])
  env={k:args[j]for k,j in names.items()}
  margs={v:subst(t,env)for v,t in mv.items()};nargs={v:subst(t,env)for v,t in nv.items()}
  assert subst(terms[ma],margs)==c.norm((subst(terms[mi],nargs),subst(terms[i],args)))
  walk(ma,margs)
  walk(mi,nargs)
 walk(root,{v:'X'+str(v)for v in vv(terms[root])})
 report[goal]={'proof_instances':len(seen),'all_instantiated_mp_edges_checked':True,'lr_only_leaf_conversion_checked':goal=='I','leaves':leaves}
 print(goal,'instances',len(seen),'leaves',len(leaves))
 for leaf in leaves:
  if leaf['seed']in['U=0','U=A']:print(leaf['seed'],leaf['arguments'])
(D/'instantiated_fragment_leaves.json').write_text(json.dumps(report,indent=2))
