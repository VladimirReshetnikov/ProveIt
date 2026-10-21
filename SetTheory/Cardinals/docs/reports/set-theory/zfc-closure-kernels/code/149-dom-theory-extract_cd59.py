import json,re,sys,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent));import zero_cd as z
HERE=Path(__file__).resolve().parent
base=HERE/'evidence/bounded_cd_refined_result.json'
if not base.exists():base=HERE.parent/'prior_reports/research218_progress_latex/research218_companion/checks/dominated/bounded_cd_refined_result.json'
old=json.loads(base.read_text())['formulas'];terms=[z.parse(x['term'])for x in old]
text=(HERE/'contexts_hyper.out').read_text();text=text.split('============================== PROOF ')[1].split('============================== end of proof')[0]
def parsep(s):
 tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[(),]',s);idx=0;vs={}
 def go():
  nonlocal idx
  t=tokens[idx];idx+=1
  if t=='c':
   assert tokens[idx]=='(';idx+=1;a=go();assert tokens[idx]==',';idx+=1;b=go();assert tokens[idx]==')';idx+=1;return z.C(a,b)
  if t=='t':return 'T'
  return vs.setdefault(t,len(vs))
 ans=go();assert idx==len(tokens);return ans
proof=[];byid={}
for line in text.splitlines():
 m=re.match(r'(\d+) P\((.*?)\)(?: #.*?)?\.  \[(.*?)\]\.',line)
 if not m:continue
 id=int(m[1]);t=parsep(m[2]);why=m[3]
 if why=='goal':continue
 if why=='assumption':
  label=re.search(r'label\("(.*?)"\)',line)[1]
  why={'axiom-label':label}
 else:
  q=re.fullmatch(r'hyper\(2,a,(\d+),a,b,(\d+),a\)',why);assert q,why
  why={'major':int(q[1]),'minor':int(q[2])}
 proof.append((id,t,why));byid[id]=(t,why)
new=[];oldmap={};pmap={}
def add(term,rule,origin):
 idx=len(new);n={'id':idx,'term':term,'rule':rule,'origin':origin};new.append(n);return idx

def cdadd(term,ma,mi,origin):
 a=tupletree(new[ma]['term']);b=tupletree(new[mi]['term']);ans,sa,sb,cycles=z.detach(a,b,details=True)
 assert ans==term,(origin,z.fmt(ans),z.fmt(term));assert cycles==0,'New proof unexpectedly needs cyclic unification'
 return add(term,{'kind':'mp_substitution','major':ma,'minor':mi,'major_substitution':sa,'minor_substitution':sb},origin)
def tupletree(t):return tuple(map(tupletree,t)) if isinstance(t,list) else t

def oldadd(i):
 if i in oldmap:return oldmap[i]
 n=old[i];t=terms[i];par=n['parent']
 if 'seed'in par:idx=add(t,{'kind':'truth' if t=='T' else 'dominated_rho8'},'prior_fragment:'+str(i))
 else:idx=cdadd(t,oldadd(par['major']),oldadd(par['minor']),'prior_fragment:'+str(i))
 oldmap[i]=idx;return idx
for id,t,why in proof:
 if 'axiom-label'in why:
  l=why['axiom-label']
  if l.startswith('checked_'):
   i=int(l[8:]);assert terms[i]==t,(l,t,terms[i]);idx=oldadd(i)
  elif l=='subterm_context_8':idx=add(t,{'kind':'dominated_rho8'},'context_depth3')
  else:raise ValueError(l)
 else:idx=cdadd(t,pmap[why['major']],pmap[why['minor']],'prover9:'+str(id))
 pmap[id]=idx
root=pmap[88397]
result={'theorem':'cd59_from_dominated_rho8','claim':'For all natural p,q,r: D((p→q)→(((p→r)→p)→q)) where D retains truth0, MP, and rho8 instances with U≤A.','implication_code':'I(a,b)=4*((a+b)*(a+b+1)//2+b)','truth_code':0,'root':root,'nodes':new,'sources':{'prior_fragments_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'prover9_source_repo':'https://github.com/ai4reason/Prover9','prover9_proof':'contexts_hyper.out'},'limits':'Finite propositional source theorem. No machine construction, enumeration change, or binary runtime claim.'}
(HERE/'cd59_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print({'nodes':len(new),'root':root,'formula':z.fmt(tupletree(new[root]['term'])),'prior_nodes':len(oldmap),'new_prover_steps':sum('major'in y for _,_,y in proof)})
