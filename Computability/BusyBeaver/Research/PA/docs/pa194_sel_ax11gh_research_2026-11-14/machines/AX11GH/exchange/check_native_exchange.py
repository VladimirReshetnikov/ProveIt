#!/usr/bin/env python3
"""Check a uniform exchange proof using only restricted rho8 and MP.

Every rho side condition u<=a has an explicit path witnessing u as a
component of a. Under I(x,y)=4*Cantor(x,y), x,y<=I(x,y), so those finite
paths prove the numerical side conditions in iPRA. No K/S axiom or Lean
parser is trusted by this checker.
"""
from pathlib import Path
import argparse,json,hashlib

def need(ok,msg):
 if not ok:raise ValueError(msg)
def check(data):
 need(data['parameters']==['A','B','C'],'three declared parameters')
 terms=data['terms'];canonical={};variables={}
 for j,t in enumerate(terms):
  need(isinstance(t,list),'term record')
  if t[0]=='parameter':
   need(len(t)==2 and t[1]in data['parameters'],'parameter name')
   variables[t[1]]=j
  else:
   need(len(t)==3 and t[0]=='I','implication constructor')
   need(all(isinstance(k,int)and 0<=k<j for k in t[1:]),'acyclic term references')
  key=tuple(t);need(key not in canonical,'canonical term uniqueness');canonical[key]=j
 need(set(variables)=={'A','B','C'},'parameter inventory')
 def I(a,b):
  key=('I',a,b);need(key in canonical,'missing target implication');return canonical[key]
 formulas=[];n_rho=0;n_mp=0;max_path=0
 for j,line in enumerate(data['lines']):
  f=line['formula'];need(isinstance(f,int)and 0<=f<len(terms),'formula index')
  if line['rule']=='rho':
   p=line['parameters'];need(len(p)==4 and all(isinstance(k,int)and 0<=k<len(terms)for k in p),'rho parameters')
   a,b,c,u=p;at=a;path=line['component_path']
   need(isinstance(path,list),'bound path')
   for d in path:
    need(d in(0,1)and terms[at][0]=='I','bound path follows implication component')
    at=terms[at][d+1]
   need(at==u,'bound path endpoint')
   need(f==I(I(I(c,u),a),I(I(a,c),I(b,c))),'restricted rho instance')
   n_rho+=1;max_path=max(max_path,len(path))
  else:
   need(line['rule']=='MP','only rho and MP allowed')
   ma,mi=line['major'],line['minor'];need(isinstance(ma,int)and isinstance(mi,int)and 0<=ma<j and 0<=mi<j,'earlier MP premises')
   need(terms[formulas[ma]]==['I',formulas[mi],f],'MP equality');n_mp+=1
  formulas.append(f)
 A,B,C=[variables[x]for x in ('A','B','C')]
 expected=I(I(A,I(B,C)),I(B,I(A,C)))
 n=data['conclusion'];need(isinstance(n,int)and 0<=n<len(formulas),'conclusion index')
 need(formulas[n]==expected,'exact exchange conclusion')
 return{'status':'PASS','claim':'(A -> (B -> C)) -> (B -> (A -> C))','term_nodes':len(terms),'proof_lines':len(formulas),
        'restricted_rho_instances':n_rho,'MP_steps':n_mp,'maximum_component_path_length':max_path,'K_or_S_axioms':0,
        'all_numeric_dominance_guards_have_component_paths':True,
        'scope':'Finite uniform native-calculus proof; arithmetic component bounds require only iPRA, no semantic PA consistency assumption.'}
def main():
 root=Path(__file__).resolve().parent
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--certificate',type=Path,default=root/'native_exchange.json');p.add_argument('--output',type=Path)
 a=p.parse_args();raw=a.certificate.read_bytes();r=check(json.loads(raw));r['certificate_sha256']=hashlib.sha256(raw).hexdigest()
 if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
if __name__=='__main__':main()
