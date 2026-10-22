"""Own inert syntax/MP/guard review; never imports or invokes an upstream renderer."""
from pathlib import Path
import re,json,subprocess,hashlib
O=Path(__file__).resolve().parent
REV='49e99c5b7cc6c2e164331961de28bad3904361fd'
BASE='Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
read=lambda name:subprocess.check_output(['git','show',REV+':'+BASE+name+'.lean']).decode()
core=read('DominatedImplication');luk=read('Lukasiewicz')
I=lambda a,b:('I',a,b)
R=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
def sub(t,env):return (t[0],sub(t[1],env),sub(t[2],env))if isinstance(t,tuple)else env.get(t,t)
class Parse:
 def __init__(self,s,db,counts,facts=None):
  self.ts=re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|≼|[()]',s);assert ''.join(self.ts)==re.sub(r'\s+','',s);self.i=0;self.db=db;self.counts=counts;self.facts=facts or{}
 def pop(self,want=None):
  t=self.ts[self.i];self.i+=1;assert want is None or t==want,(want,t);return t
 def group(self,f):
  if self.ts[self.i]!='(':return f()
  self.pop('(');v=f();self.pop(')');return v
 def term(self):
  def f():
   n=self.pop()
   if n in('wim','L.imp'):return I(self.term(),self.term())
   assert re.fullmatch(r'v\d+|[a-z]|_',n),n;return n
  return self.group(f)
 def guard(self,pair):
  def f():
   n=self.pop();a,b=pair
   if n=='L.refl':v=self.term();assert a==b and(v=='_'or v==a)
   elif n in('le_l','le_r'):
    v=self.term();assert isinstance(b,tuple);fixed,grown=(2,1)if n=='le_l'else(1,2);assert b[fixed]==v;self.guard((a,b[grown]))
   else:assert self.facts[n]==pair
  self.group(f)
 def proof(self):
  def f():
   n=self.pop()
   if n=='h.mp':
    p,q=self.proof(),self.proof();assert isinstance(p,tuple)and p[0]=='I'and p[1]==q,(p,q);self.counts['mp']+=1;return p[2]
   if n=='h.rho8':
    a,b,c,u=[self.term()for _ in range(4)];self.guard((u,a));self.counts['restricted_rows']+=1;return R(a,b,c,u)
   if n in self.db:
    self.pop('h');args,target,guards=self.db[n];env=dict(zip(args,[self.term()for _ in args]));
    for u,a in guards:self.guard((sub(u,env),sub(a,env)))
    return sub(target,env)
   assert n in self.facts,n;return self.facts[n]
  return self.group(f)
 def end(self):assert self.i==len(self.ts),self.ts[self.i:]
db={};counts={'mp':0,'restricted_rows':0};matches=list(re.finditer(r'private theorem (d\d+)\b',core))
assert[m.group(1)for m in matches]==['d'+str(i)for i in range(1,59)if i not in(56,58)]
for i,m in enumerate(matches):
 end=matches[i+1].start()if i+1<len(matches)else core.index('/-- Restricted rows',m.end())
 header,body=core[m.end():end].split(':=',1);args=[a for g in re.findall(r'\(([^():]+) : A\)',header)for a in g.split()];facts={};guards=[]
 for n,s in re.findall(r'\((hb\d+) : (.*?)\)\s*:',header,re.S):
  p=Parse(s,db,counts);u=p.term();p.pop('≼');a=p.term();p.end();facts[n]=(u,a);guards.append((u,a))
 p=Parse(re.split(r':\s*T\s+',header)[-1],db,counts);target=p.term();p.end();before=counts['mp'];p=Parse(body.strip(),db,counts,facts);assert p.proof()==target,m.group(1);p.end();assert counts['mp']==before+1;db[m.group(1)]=(args,target,guards)
private=dict(counts)
targets={'rho8_all':R('a','b','c','u'),'composition':I(I('a','b'),I(I('b','c'),I('a','c'))),'lift_right':I(I('x','a'),I('x','b')),'k':I('a',I('b','a')),'peirce':I(I(I('a','b'),'a'),'a'),'s':I(I('a',I('b','c')),I(I('a','b'),I('a','c')))}
public=list(re.finditer(r'(?m)^theorem (\w+)\b',core));assert[m.group(1)for m in public]==list(targets)
for i,m in enumerate(public):
 end=public[i+1].start()if i+1<len(public)else core.index('\nend\n',m.end());body=core[m.end():end].split(':=',1)[1];body=re.sub(r'/--.*?-/\s*$','',body,flags=re.S).strip();p=Parse(body,db,counts,{'hab':I('a','b')});assert p.proof()==targets[m.group(1)],m.group(1);p.end()
assert counts=={'mp':59,'restricted_rows':23}and private=={'mp':56,'restricted_rows':23}
assert not re.search(r'WithSeed|h\.truth|\b0\b|Nat\.|sorry|native_decide|(?m:^\s*axiom\b)',core)
root=Path('/home/codex/.codex/worktrees/ec20/Proofs')
current=(root/BASE/'DominatedImplication.lean').read_text();oldluk=(root/BASE/'Lukasiewicz.lean').read_text()
remove_comments=lambda t:re.sub(r'/\-.*?\-/','',t,flags=re.S)
header=lambda text,name:re.sub(r'\s+',' ',re.search(r'(?m)^(?:structure|def|theorem) '+name+r'\b.*?(?::=| where\n)',text,re.S).group()).strip()
for name in ['Language','rho8','Restricted','rho8_all','composition','lift_right']:assert header(core,name)==header(current,name),name
for name in ['Implicational','k','peirce','composition','s']:assert header(luk,name)==header(oldluk,name),name
marker='namespace SetTheory.BusyBeaver.ZFC.Tarski';assert luk[luk.index(marker):]==oldluk[oldluk.index(marker):]
phase13=Path('/tmp/k215-phase13-shared-basis/candidate/BusyBeaver/ZFC');files=['DominatedImplication','ImplicationalBasis','Lukasiewicz'];oldmetric=sum((phase13/(n+'.lean')).stat().st_size for n in files);oldlines=sum(len((phase13/(n+'.lean')).read_text().splitlines())for n in files)
r={'status':'PASS_OWN_INERT_FORMULA_SOURCE_CHECK','upstream_revision':REV,'private_proofs':len(matches),'private_counts':private,'all_counts':counts,'public_targets':list(targets),'relation_proof_rules':['hypothesis','reflexivity','left growth','right growth'],'normalization_or_truth_used':False,'current_six_core_headers_unchanged':True,'current_five_Lukas_headers_unchanged':True,'entire_Tarski_tail_bytes_unchanged':True,'upstream_pair_bytes':len(core.encode())+len(luk.encode()),'upstream_pair_lines':len(core.splitlines())+len(luk.splitlines()),'phase13_three_file_bytes':oldmetric,'phase13_three_file_lines':oldlines,'saved_bytes_over_phase13':oldmetric-len(core.encode())-len(luk.encode()),'saved_lines_over_phase13':oldlines-len(core.splitlines())-len(luk.splitlines()),'inputs':{n:{'sha256':hashlib.sha256(s.encode()).hexdigest(),'bytes':len(s.encode())}for n,s in [('upstream_core',core),('upstream_Lukas',luk),('current_core',current),('current_Lukas',oldluk)]},'scope':'Own data-only strict free-constructor proof syntax check; no generator, compiler or archived/provided code executed. This is not Lean elaboration or endpoint acceptance.'}
(O/'source-audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
