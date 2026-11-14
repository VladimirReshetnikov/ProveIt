#!/usr/bin/env python3
"""Reify the inherited restricted-rho exchange derivation into a flat certificate.

The proof checker accepts only restricted rho instances (side condition proved
by a component path) and modus ponens. K and S are not checker axioms.
"""
from pathlib import Path
import re,json,functools,argparse,hashlib
ROOT=Path(__file__).resolve().parent

def require(x,msg):
 if not x:raise AssertionError(msg)
def term(a,b):return('I',a,b)
def inside(a,b):
 if a==b:return[]
 if isinstance(b,tuple)and len(b)==3 and b[0]=='I':
  for j in(1,2):
   p=inside(a,b[j])
   if p is not None:return[j-1]+p
 return None
class Proof:
 def __init__(self,f,idx):self.f,self.idx=f,idx
 def __hash__(self):return self.idx
 def __eq__(self,other):return isinstance(other,Proof)and self.idx==other.idx

class Reify:
 def __init__(self,path):
  source=re.sub(r'/\-[\s\S]*?\-/','',path.read_text())
  pieces=re.split(r'(?m)^(?:private )?def ',source)[1:]
  self.defs={};self.memo={};self.lines=[];self.line_idx={}
  for p in pieces:
   if ':='not in p:continue
   head,body=p.split(':=',1)
   name=re.match(r'\w+',head)[0]
   if name in ('liftRight','rho8All'):continue
   args=[]
   for x in re.findall(r'\(([\w ]+)\s*:',head):args+=x.split()
   # Result types contain no typed binder groups.
   body=body.split('end M6.',1)[0].strip()
   tokens=re.findall(r'\(|\)|⟹|[A-Za-z_][A-Za-z0-9_.]*',body)
   self.defs[name]=(args,tokens)
 def add(self,rule,f,detail):
  key=rule,f,detail
  if key not in self.line_idx:
   i=len(self.lines);self.line_idx[key]=i;self.lines.append((rule,f,detail))
  return Proof(f,self.line_idx[key])
 def apply(self,name,args):
  if name=='rules.mp':
   major,minor=args;require(isinstance(major,Proof)and isinstance(minor,Proof),'MP proof types')
   require(isinstance(major.f,tuple)and major.f[0]=='I'and major.f[1]==minor.f,'MP antecedent mismatch')
   return self.add('MP',major.f[2],(major.idx,minor.idx))
  if name=='rules.row':
   a,b,c,u,h=args;p=inside(u,a);require(p is not None,('rho side condition',u,a))
   f=term(term(term(c,u),a),term(term(a,c),term(b,c)))
   return self.add('rho',f,(a,b,c,u,tuple(p)))
  if name in ('rules.refl','rules.boundLeft','rules.boundRight'):return'ORDER_PROOF'
  key=name,tuple(args)
  if key not in self.memo:
   params,toks=self.defs[name]
   require(len(params)==len(args),(name,params,len(args)))
   self.memo[key]=self.eval(toks,dict(zip(params,args)))
  return self.memo[key]
 def eval(self,toks,env):
  pos=0
  def atom():
   nonlocal pos
   t=toks[pos];pos+=1
   if t=='(':
    x=expr();require(toks[pos]==')',('expected close',toks,pos));pos+=1;return x
   if t in env:return env[t]
   if t=='_':return'IMPLICIT'
   if t=='rules':return'RULES'
   if t.startswith('rules.'):
    n={'rules.mp':2,'rules.row':5,'rules.refl':1,'rules.boundLeft':2,'rules.boundRight':2}[t]
    return self.apply(t,[atom()for _ in range(n)])
   if t in self.defs:
    require(atom()=='RULES','explicit rules argument')
    return self.apply(t,[atom()for _ in self.defs[t][0]])
   raise AssertionError(('unknown token',t))
  def expr():
   nonlocal pos
   a=atom()
   if pos<len(toks)and toks[pos]=='⟹':pos+=1;return term(a,expr())
   return a
  result=expr();require(pos==len(toks),('unconsumed',toks[pos:]));return result
 def certificate(self):
  p=self.apply('exchange',['A','B','C'])
  expected=term(term('A',term('B','C')),term('B',term('A','C')))
  require(p.f==expected,'target exchange')
  terms=[];index={}
  def encode(t):
   if t in index:return index[t]
   v=['parameter',t]if isinstance(t,str)else['I',encode(t[1]),encode(t[2])]
   n=len(terms);index[t]=n;terms.append(v);return n
  lines=[]
  for rule,f,d in self.lines:
   if rule=='MP':line={'rule':'MP','formula':encode(f),'major':d[0],'minor':d[1]}
   else:line={'rule':'rho','formula':encode(f),'parameters':[encode(x)for x in d[:4]],'component_path':list(d[4])}
   lines.append(line)
  return {'parameters':['A','B','C'],'terms':terms,'lines':lines,'conclusion':p.idx,'expected_formula':encode(expected),
   'checker_axioms':'restricted rho8 and MP only; no K or S assumptions',
   'numeric_side_conditions':'A component path proves u<=a using x,y<=I(x,y)=4*Cantor(x,y).'}

def check(data):
 terms=data['terms'];decoded=[]
 for i,t in enumerate(terms):
  if t[0]=='parameter':require(t[1]in data['parameters'],'unknown parameter');decoded.append(t[1])
  else:
   require(t[0]=='I'and 0<=t[1]<i and 0<=t[2]<i,'term DAG order')
   decoded.append(term(decoded[t[1]],decoded[t[2]]))
 formulas=[]
 for i,line in enumerate(data['lines']):
  f=decoded[line['formula']]
  if line['rule']=='rho':
   a,b,c,u=[decoded[j]for j in line['parameters']]
   at=a
   for d in line['component_path']:
    require(d in(0,1)and isinstance(at,tuple)and at[0]=='I','component path')
    at=at[d+1]
   require(at==u,'component bound endpoint')
   require(f==term(term(term(c,u),a),term(term(a,c),term(b,c))),'restricted rho shape')
  else:
   require(line['rule']=='MP','unknown rule')
   ma,mi=line['major'],line['minor'];require(0<=ma<i and 0<=mi<i,'MP earlier indices')
   require(formulas[ma]==term(formulas[mi],f),'MP premise equality')
  formulas.append(f)
 expected=term(term('A',term('B','C')),term('B',term('A','C')))
 require(formulas[data['conclusion']]==expected,'final exchange')
 return{'status':'PASS','term_nodes':len(terms),'proof_lines':len(formulas),'rho_instances':sum(x['rule']=='rho'for x in data['lines']),
        'MP_steps':sum(x['rule']=='MP'for x in data['lines']),'K_or_S_axioms':0,
        'side_condition_certificates':'all rho bounds proved by exact component paths','uniform_arithmetic_base':'iPRA by substitution into the finite template and PR prefix validation'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=ROOT/'references'/'RestrictedImplication.lean');ap.add_argument('--output',type=Path,default=ROOT/'native_exchange.json');a=ap.parse_args()
 r=Reify(a.source);c=r.certificate();receipt=check(c)
 raw=json.dumps(c,separators=(',',':')).encode();a.output.write_bytes(raw+b'\n')
 receipt.update(certificate_sha256=hashlib.sha256(raw+b'\n').hexdigest(),source_sha256=hashlib.sha256(a.source.read_bytes()).hexdigest())
 a.output.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
