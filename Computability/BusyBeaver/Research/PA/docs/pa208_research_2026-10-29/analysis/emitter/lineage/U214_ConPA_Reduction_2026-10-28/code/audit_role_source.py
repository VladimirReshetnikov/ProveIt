#!/usr/bin/env python3
"""Independent exact CFG and symbolic constructor audit of the role-changed source.
This imports neither the search nor the source constructor. Standard library only.
"""
from pathlib import Path
import sys,json,hashlib,argparse
RANGES={'m166':(26,52),'m121':(52,78),'m168':(107,133),'m119':(78,105),'m180':(78,107),'m181':(695,723),'m218':(995,1042)}
TOK={'m166':'a','m121':'b','m168':'c','m119':'I','m180':'Q','m181':'R','m218':'N'}
def require(p,msg):
 if not p:raise ValueError(msg)
def cfg(rows):
 bounds={}
 for i,(p,o,a)in enumerate(rows):
  for j in range(len(p)+1):
   v=p[:j]
   if v not in bounds:bounds[v]=[i,i+1]
   else:bounds[v][1]=i+1
 out=[]
 for i,(p,o,a)in enumerate(rows):
  if o=='CI':dst=(i+1,)
  elif o=='CH':dst=()
  else:
   which='1'if o=='CC'else'0';n=a if o!='CD'else 1
   poss=[j for j,c in enumerate(p)if c==which]
   require(n<=len(poss),('escapingbranch',i,p,o,a))
   anc=p[:poss[-n]];d=bounds[anc][0 if o=='CC'else 1]
   dst=(d,i+1)if o=='CD'else(d,)
  out.append((o,a,dst))
 return out

def symbolic(tokens):
 stack=['old-stack'];cur='old-current'
 for t in tokens:
  if t in('a','b','c'):stack.append(cur);cur=t
  elif t=='N':cur=('I',cur,'F')
  else:require(t in('I','Q','R')and len(stack)>1,'underflow');cur=(t,stack.pop(),cur)
 require(stack==['old-stack','old-current'],'wrong stack effect')
 return cur

def audit(path,oldpath,kpath,tokenpath):
 raw=path.read_bytes();new=json.loads(raw);old=json.loads(oldpath.read_text());k=json.loads(kpath.read_text())
 word=json.loads(tokenpath.read_text());tokens=[TOK[t]for t in word]
 I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);R=lambda a,b:('R',a,b)
 E=R('c','a');G=Q('a',I(R('a','c'),R('a','b')))
 U=Q('c',I(E,'a'));L=Q('c',I('a',I(G,E)))
 H=Q('a',I(U,I(L,'F')))
 require(symbolic(tokens)==H,'wrong exact symbolic shell')
 oc,nc,kc=map(cfg,(old,new,k))
 start=2885;expected=[]
 for name in word:
  lo,hi=RANGES[name];offset=start+len(expected)
  for o,a,dst in kc[lo:hi]:
   require(o!='CH'and all(lo<=x<=hi for x in dst),('unclosedmacro',name))
   expected.append((o,a,tuple(offset+x-lo for x in dst)))
 stop=start+len(expected);oldstop=3622;delta=stop-oldstop
 require(nc[start:stop]==expected,'emitter primitive CFG differs')
 require(len(new)==len(old)+delta,'wrong length')
 shift=lambda x:x if x<oldstop else x+delta
 ext=0
 for i in list(range(start))+list(range(oldstop,len(old))):
  o,a,dst=oc[i]
  require(all(not start<d<oldstop for d in dst),'retained branch enters emitter interior')
  expectedrow=(o,a,tuple(shift(d)for d in dst))
  require(nc[shift(i)]==expectedrow,('changed exterior CFG',i,nc[shift(i)],expectedrow));ext+=1
 import source_language as s
 ar,n=s.graph_arithmetic(new);ir=s.graph_intervals(new);require(ar==ir,'independent resolvers disagree')
 return {'status':'EXACT_CONSTRUCTOR_AND_EXTERIOR_CFG_PASS','source_sha256':hashlib.sha256(raw).hexdigest(),'input_u218_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),'metrics':s.metrics(s.tree(new)),'emitter_interval':[start,stop],'emitter_primitives':len(expected),'exterior_primitives':ext,'no_stray_checks':n,'macro_word':tokens,'symbolic_shell':H,'scope':'Physical compilation and logical calibration are separate obligations. The exact retained gate is unchanged; the logical alternative uses matrix/output a, source b, tested c.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('old_source',type=Path);p.add_argument('baseline',type=Path);p.add_argument('tokens',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
 r=audit(a.source,a.old_source,a.baseline,a.tokens);v=json.dumps(r,indent=2)+'\n'
 if a.output:a.output.write_text(v)
 print(v,end='')
