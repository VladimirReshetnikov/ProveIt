"""Independent restricted syntax audit: no producer imports or Lean execution."""
from pathlib import Path
import re,json,hashlib
P=Path('/tmp/k215-generic-cd52/candidate/DominatedImplication.lean');O=Path(__file__).resolve().parent
source=P.read_text();pin=hashlib.sha256(P.read_bytes()).hexdigest()
assert pin=='5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f'
source=re.sub(r'/\-.*?\-/','',source,flags=re.S)
counts={'mp':0,'restricted_rows':0,'seed_uses':0,'guards':0}
def ast(s):
 ts=re.findall(r'\(|\)|[^\s()]+',s);i=0
 def one():
  nonlocal i
  t=ts[i];i+=1
  if t!='(':assert t!=')';return t
  out=[]
  while ts[i]!=')':out.append(one())
  i+=1
  return out[0]if len(out)==1 else out
 out=[]
 while i<len(ts):out.append(one())
 return out[0]if len(out)==1 else out

def formula(x):
 if isinstance(x,str):assert re.fullmatch(r'(?:v\d+|[a-z]|τ)',x),x;return x
 assert isinstance(x,list)and len(x)==3 and x[0]=='wim',x
 return(formula(x[1]),formula(x[2]))
def subst(x,env):return tuple(subst(v,env)for v in x)if isinstance(x,tuple)else env.get(x,x)
def guard(p,u,a,hyps):
 counts['guards']+=1
 if isinstance(p,str):assert p in hyps and hyps[p]==(u,a),(p,u,a,hyps);return
 head,*args=p
 if head=='L.refl':assert args==['_']or len(args)==1 and formula(args[0])==u;assert u==a,(p,u,a)
 elif head=='le_l':assert len(args)==2 and isinstance(a,tuple)and formula(args[0])==a[1];guard(args[1],u,a[0],hyps)
 elif head=='le_r':assert len(args)==2 and isinstance(a,tuple)and formula(args[0])==a[0];guard(args[1],u,a[1],hyps)
 else:raise AssertionError(p)
lemmas={};current=''
def proof(p,envproof,hyps):
 if isinstance(p,str):
  if p=='h.truth':counts['seed_uses']+=1;return'τ'
  assert p in envproof,p;return envproof[p]
 head,*args=p
 if head=='h.mp':
  assert len(args)==2;p0=proof(args[0],envproof,hyps);p1=proof(args[1],envproof,hyps)
  assert isinstance(p0,tuple)and p0[0]==p1,(current,'MP mismatch',p0,p1);counts['mp']+=1;return p0[1]
 if head=='h.rho8':
  assert len(args)==5;a,b,c,u=map(formula,args[:4]);guard(args[4],u,a,hyps)
  counts['restricted_rows']+=1;return(((c,u),a),((a,c),(b,c)))
 assert head in lemmas,(current,head)
 assert args[0]=='h';args=args[1:]
 if head=='under_antecedent':
  assert len(args)==2;z=formula(args[0]);xy=proof(args[1],envproof,hyps);assert isinstance(xy,tuple)
  return((z,xy[0]),(z,xy[1]))
 params,need,conclusion=lemmas[head];assert len(args)==len(params)+len(need),(head,args)
 env=dict(zip(params,map(formula,args[:len(params)])))
 for p,(u,a)in zip(args[len(params):],need.values()):guard(p,subst(u,env),subst(a,env),hyps)
 return subst(conclusion,env)

region=source[source.index('private theorem d1 '):source.index('\nend\n',source.index('private theorem d1 '))]
blocks=list(re.finditer(r'^private theorem (\w+)(.*?)(?=^private theorem|\Z)',region,re.M|re.S))
results=[]
for m in blocks:
 current=m[1];s=m[2].strip();sig,body=s.split(' :=',1)
 # Signature last type starts after the final newline colon, before T.
 cut=list(re.finditer(r':\s*\n?\s*T\s+',sig))[-1];h,target=sig[:cut.start()],sig[cut.end():]
 target=formula(ast(target));params=[];hyps={}
 groups=re.findall(r'\(([^():]+) : A\)',h)
 for g in groups:params.extend(g.split())
 if current.startswith('d'):
  found=re.search(r'\(hb0 : (.*)\)\s*$',h)
  if found:
   u,a=found[1].split('≼');hyps['hb0']=(formula(ast(u)),formula(ast(a)))
 envproof={}
 if current=='under_antecedent':envproof['hxy']=('x','y')
 body=body.strip()
 if current=='composition_seed':
  assert body.startswith('by\n');s=body[len('by\n'):].strip();assert s.startswith('have happ : T ')
  t,rest=s[len('have happ : T '):].split(' :=',1);statement=formula(ast(t))
  val,body=rest.split('\n  exact ',1);assert proof(ast(val),{},hyps)==statement
  envproof['happ']=statement
 value=proof(ast(body),envproof,hyps);assert value==target,(current,value,target)
 lemmas[current]=(params,hyps,target);results.append(current)
assert results[:52]==['d'+str(n)for n in range(1,53)]and len(results)==58
assert counts['mp']==66 and counts['restricted_rows']==19 and counts['seed_uses']==5,counts
# Same six public headers/definitions and unchanged adapter bytes.
B=Path('/tmp/k215-generic-cd52/inputs/DominatedImplication.baseline.lean').read_text();B=re.sub(r'/\-.*?\-/','',B,flags=re.S)
canon=lambda s:re.sub(r'\s+',' ',s).strip()
for n in ['Language','rho8','Restricted']:
 pattern=rf'^(?:structure|def) {n}\b.*?(?=^(?:structure|private|def|section))'
 assert canon(re.search(pattern,source,re.M|re.S)[0])==canon(re.search(pattern,B,re.M|re.S)[0]),n
for n in ['rho8_all','composition','lift_right']:
 pattern=rf'^theorem {n}\b(.*?) :='
 assert canon(re.search(pattern,source,re.M|re.S)[0])==canon(re.search(pattern,B,re.M|re.S)[0]),n
baseline=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean').read_bytes()
adapter=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean').read_bytes()
assert adapter==Path('/tmp/k215-generic-cd52/inputs/DomRho8.adapter.lean').read_bytes()
r={'status':'PASS_INDEPENDENT_FREE_CONSTRUCTOR_SOURCE_AUDIT','candidate_sha256':pin,'checked_private_bodies':results,'counts':counts,'public_apis_equal':['Language','rho8','Restricted','rho8_all','composition','lift_right'],'unchanged_adapter_sha256':hashlib.sha256(adapter).hexdigest(),'source_metrics':{'baseline_core_bytes':len(baseline),'candidate_core_bytes':P.stat().st_size,'saved_bytes':len(baseline)-P.stat().st_size,'baseline_core_lines':len(baseline.splitlines()),'candidate_core_lines':len(P.read_bytes().splitlines()),'combined_core_adapter_bytes':P.stat().st_size+len(adapter)},'compiler_invoked':False,'supplied_producer_imported_or_executed':False,'scope':'Own finite parser interprets only prefix implication syntax, explicit lemma applications/MP and exact relation guard constructors. No equation/normalization, semantic valuation, Lean elaboration or kernel acceptance is assumed. Public seed discharge read separately.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out=O/'source-audit.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
