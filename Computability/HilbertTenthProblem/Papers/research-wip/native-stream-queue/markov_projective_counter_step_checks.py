#!/usr/bin/env python3
"""Fresh bounded evidence; reads predecessor prose bytes only, never runs old code."""
import argparse,collections,hashlib,json,pathlib
READS={'markov_mask_matrix_lift.md':[[1,104]],'group_projective_zero_mortality6.md':[[1,125],[185,280]],'matrix193_crt_selector.md':[[115,190]],'matrix193_positive_crt_duration.md':[[1,100]]}
def ck(b,m):
 if not b:raise RuntimeError(m)
class Graph:
 def __init__(self,ports):self.ports=ports;self.rows=[];self.res=[]
 def gate(self,n,op,a,b):self.rows.append([n,op,a,b]);return n
 def sos(self):
  terms=[self.gate('square_'+str(j),'*',r,r) for j,r in enumerate(self.res)]
  out=terms[0]
  for j,t in enumerate(terms[1:],1):out=self.gate('join_'+str(j),'+',out,t)
  self.output=out
 def packet(self):
  self.sos();seen=set(self.ports);degree={x:1 for x in self.ports};used={};counts=collections.Counter()
  for n,op,a,b in self.rows:
   ck(n not in seen,'duplicate');ck(all(isinstance(v,int) or v in seen for v in [a,b]),'topology')
   da=0 if isinstance(a,int) else degree[a];db=0 if isinstance(b,int) else degree[b]
   degree[n]=da+db if op=='*' else max(da,db);counts['M' if op=='*' else 'A']+=1;seen.add(n);used[n]=(a,b)
  live=set();todo=[self.output]
  while todo:
   x=todo.pop()
   if not isinstance(x,str) or x in live:continue
   live.add(x);todo.extend(used.get(x,()))
  ck(live==seen,'liveness')
  return {'ports':self.ports,'source':self.rows,'residuals':self.res,'output':self.output,'M':counts['M'],'A':counts['A'],'total':len(self.rows),'degree_upper':degree[self.output]}
def boolean(g,j,B,C):
 e=g.gate('e'+j,'-',B,1);t=g.gate('t'+j,'-',B,2);u=g.gate('u'+j,'-',C,1)
 g.res += [g.gate('rb'+j,'*',e,t),g.gate('rz'+j,'*',t,u)];return e

def direct(T=None):
 ports=['C','Cp','B'] if T is None else ['x']+[f'C{j}' for j in range(1,T+1)]+[f'B{j}' for j in range(T)]
 g=Graph(ports);cur='C' if T is None else g.gate('C0','+','x',1)
 for j in range(1 if T is None else T):
  s=str(j);B='B' if T is None else 'B'+s;cp='Cp' if T is None else 'C'+str(j+1)
  e=boolean(g,s,B,cur);diff=g.gate('diff'+s,'-',cp,cur);g.res.append(g.gate('rt'+s,'+',diff,e));cur=cp
 if T is not None:g.res.append(g.gate('endpoint','-',cur,1))
 return g.packet()
def raw(T=None):
 if T is None:ports=['C','Cp','B','X','H','Xp','Hp']
 else:ports=['x','H0']+[f'X{j}' for j in range(1,T+1)]+[f'H{j}' for j in range(1,T+1)]+[f'B{j}' for j in range(T)]
 g=Graph(ports)
 if T is None:
  e=boolean(g,'0','B','C')
  for suffix,C,X,H in [('', 'C','X','H'),('p','Cp','Xp','Hp')]:
   prod=g.gate('link_product'+suffix,'*',H,C);g.res.append(g.gate('link'+suffix,'-',X,prod))
  cases=[('0',e,'X','H','Xp','Hp')]
 else:
  c0=g.gate('C0','+','x',1);g.gate('X0','*','H0',c0);cases=[]
  for j in range(T):
   s=str(j);e=g.gate('e'+s,'-','B'+s,1);t=g.gate('t'+s,'-','B'+s,2);u=g.gate('u'+s,'-','X'+s,'H'+s)
   g.res += [g.gate('rb'+s,'*',e,t),g.gate('rz'+s,'*',t,u)]
   cases.append((s,e,'X'+s,'H'+s,'X'+str(j+1),'H'+str(j+1)))
 for j,e,X,H,Xp,Hp in cases:
  eh=g.gate('eh'+j,'*',e,H);num=g.gate('num'+j,'-',X,eh);qx=g.gate('qx'+j,'*',7,Xp)
  g.res.append(g.gate('rx'+j,'-',qx,num));qh=g.gate('qh'+j,'*',7,Hp);g.res.append(g.gate('rh'+j,'-',qh,H))
 if T is not None:g.res.append(g.gate('endpoint','-','X'+str(T),'H'+str(T)))
 return g.packet()
def ev(p,vals):
 v=dict(vals)
 for n,op,a,b in p['source']:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b];v[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return v[p['output']]
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=pathlib.Path,required=True);a.add_argument('--output');a.add_argument('--expect');args=a.parse_args()
 pins={}
 for name,spans in READS.items():
  b=(args.root/name).read_bytes();ls=b.splitlines(keepends=True);pins[name]={'sha256':hashlib.sha256(b).hexdigest(),'read_spans':[{'first':s,'last':e,'sha256':hashlib.sha256(b''.join(ls[s-1:e])).hexdigest()} for s,e in spans]}
 packets={'direct_local':direct(),'raw_local':raw()}
 ck((packets['direct_local']['M'],packets['direct_local']['A'])==(5,7),'direct count')
 ck((packets['raw_local']['M'],packets['raw_local']['A'])==(13,13),'raw count')
 local=0
 for C in range(1,7):
  for Cp in range(1,7):
   for B in range(1,5):
    valid=(B==1 and C==Cp==1) or (B==2 and C>=2 and Cp==C-1)
    ck((ev(packets['direct_local'],dict(C=C,Cp=Cp,B=B))==0)==valid,'direct semantics')
    for h in [1,2,5]:
     vals=dict(C=C,Cp=Cp,B=B,X=7*h*C,H=7*h,Xp=h*Cp,Hp=h)
     ck((ev(packets['raw_local'],vals)==0)==valid,'raw semantics');local+=1
 history=0
 for T in [1,2,4]:
  pd=direct(T);pr=raw(T);packets['direct_'+str(T)]=pd;packets['raw_'+str(T)]=pr
  ck((pd['M'],pd['A'],pd['degree_upper'])==(5*T+1,8*T+2,4),'direct history count')
  ck((pr['M'],pr['A'],pr['degree_upper'])==(9*T+2,10*T+2,6),'raw history count')
  for x in range(1,T+3):
   d={'x':x};v={'x':x,'H0':7**T}
   for j in range(T):
    B=2 if x>j else 1;C=max(x-j-1,0)+1;d['B'+str(j)]=v['B'+str(j)]=B;d['C'+str(j+1)]=C
    v['H'+str(j+1)]=7**(T-j-1);v['X'+str(j+1)]=7**(T-j-1)*C
   ck((ev(pd,d)==0)==(x<=T),'direct history semantics');ck((ev(pr,v)==0)==(x<=T),'raw history semantics');history+=1
 # Omitted-integrality counterexample: positive raw homogeneous step with ratio3/2 ->1/2.
 ck(7*1==21-(2-1)*14 and 7*2==14,'rational counterexample')
 data={'status':'BOUNDED_EXPLICIT_GRAPHS_NO_UNIVERSAL_OR_MINIMUM_CLAIM','helper_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'pins':pins,'packets':packets,'counts':{'local_lift_cases':local,'history_cases':history,'arrays':len(packets),'rows':sum(p['total'] for p in packets.values())},'counterexample_without_integral_input':{'X':21,'H':14,'Xp':1,'Hp':2,'B':2},'scope':'Fresh graphs only; predecessor prose bytes authenticated without program import or execution. Finite evaluations corroborate the independent symbolic proof.'}
 payload=(json.dumps(data,indent=2,sort_keys=True)+'\n').encode()
 if args.expect:ck(payload==pathlib.Path(args.expect).read_bytes(),'receipt mismatch')
 if args.output:
  with open(args.output,'xb') as f:f.write(payload)
 print(json.dumps(data['counts'],sort_keys=True))
if __name__=='__main__':main()
