#!/usr/bin/env python3
"""Literal matrix checks for the published U15 repeated unary block; no old code."""
import argparse
import hashlib
import json
from pathlib import Path

PINS={
 'group_directed_semigroup193.json':'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'neary_woods_explicit_universal_tm.md':'b04739084d093b1ee20dde5dbcf851f4cfac4d6895978f971211f9027cfdac8f',
 'matrix193_power_block_obstruction.md':'60f442caa77c68f11c73a4995fbebc4582a0ef64b3a9e41dfd68c27d8782d978'}
I=((1,0),(0,1)); Q=((1,0),(2,1)); G=((11,4),(8,3)); H=((35,16),(24,11))

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def mm(a,b):return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def inv(a):
 need(det(a)==1,'determinant')
 return ((a[1][1],-a[0][1]),(-a[1][0],a[0][0]))
def det(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def power(a,n):
 r=I
 while n:
  if n&1:r=mm(r,a)
  a=mm(a,a);n//=2
 return r
def E(j):return ((1+4*j,2),(-8*j*j,1-4*j))
def neg(a):return tuple(tuple(-v for v in r) for r in a)
def trace(a):return a[0][0]+a[1][1]
def evaluate(w,codes):
 out=I
 for c in w:out=mm(out,E(codes[c]))
 return out
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def verify(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 packet=json.loads((root/'group_directed_semigroup193.json').read_text())['packet'];codes=packet['top_codes']
 need(codes['0']==1 and codes['1']==2,'actual code interface')
 # These four exact identities prove the formula for every i>=1.
 need(mm(mm(Q,E(1)),inv(Q))==E(0),'conjugate first letter')
 need(mm(mm(Q,E(2)),inv(Q))==E(1),'conjugate second letter')
 need(mm(E(0),E(1))==neg(G),'conjugate alternating pair')
 need(mm(G,power(E(1),2))==H,'tail positive matrix')
 need(det(G)==det(H)==1 and min(v for m in (G,H) for r in m for v in r)>0,'positive unimodular matrices')
 blocks=[]
 for i in range(1,17):
  word='01'*(8*i-5)+'11';mat=evaluate(word,codes)
  expected=neg(mm(power(G,8*i-6),H))
  need(mm(mm(Q,mat),inv(Q))==expected,'uniform block formula')
  need(det(mat)==1 and trace(mat)<-2,'hyperbolic block')
  blocks.append(dict(index=i,word=word,matrix=mat,trace=trace(mat),determinant=det(mat)))
 for left in blocks:
  for right in blocks:
   a=mm(left['matrix'],right['matrix'])
   need(det(a)==1 and trace(a)>2,'two-block consequence')
 W=blocks[0]['matrix'];B=mm(W,W);a=trace(B)//2
 need(trace(B)==2*a and a==39979681,'even block parameter')
 D=tuple(tuple(B[i][j]-a*int(i==j) for j in range(2)) for i in range(2))
 delta=a*a-1;need(mm(D,D)==((delta,0),(0,delta)),'exact quadratic algebra')
 cases=[];chi,psi=1,0
 for x in range(13):
  formula=tuple(tuple(chi*int(i==j)+psi*D[i][j] for j in range(2)) for i in range(2))
  need(formula==power(B,x),'Pell power identity')
  need(chi*chi-delta*psi*psi==1,'Pell norm')
  cases.append(dict(x=x,chi=chi,psi=psi,matrix=formula))
  chi,psi=a*chi+delta*psi,chi+a*psi
 padding=evaluate('0000',codes)
 need(trace(padding)==2 and det(padding)==1,'padding unipotent')
 # Generic fixed-context target = chi*C + psi*D_context, with signed fixed numerals.
 source=[]
 for k in ('00','01','10','11'):
  source += [[f'u{k}','*','chi',f'C{k}'],[f'v{k}','*','psi',f'D{k}'],[f't{k}','+',f'u{k}',f'v{k}']]
 out=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
  primary_pdf_sha256='6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b',
  scope='Exact matrix/recurrence checks only. Published TM-to-U15 theorem imported; no program compiler or unbounded membership checker executed or emitted.',
  encoded_block=blocks[0],uniform_positive_conjugation={'G':G,'H':H,'identity':'Q Phi(A_i) Q^-1 = -G^(8i-6) H'},
  bounded_evidence={'single_blocks':blocks,'two_block_products':256},
  even_block={'word':blocks[0]['word']*2,'matrix':B,'trace':trace(B),'determinant':det(B),'Pell_parameter':a,'D':D,'Delta':delta,'power_fixtures':cases},
  optional_padding={'word':'0000','matrix':padding,'trace':trace(padding),'semantic_role':'S padding in primary equation(3); not data'},
  supplied_Pell_coordinate_target={'source':source,'M':8,'A':4,'total':12,'supplied_ports':['chi','psi'],'scope':'Only target assembly from correctly indexed Pell coordinates; their exact index=x relation is unpaid.'},
  ordinary_input_theorem='For each c.e. S subset of positive integers, effective fixed U_S,V_S exist with valid U15 configuration U_S W^x V_S halting iff x in S; W=(01)^3 11. Also possible with W^2 by source unary length2x+4.',
  affine_loader_transfers=False,raw_ones_universality_proved=False,complete_Diophantine_bound=None)
 return json.loads(json.dumps(out))

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
 a=p.add_mutually_exclusive_group(required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path)
 args=p.parse_args();out=verify(args.root)
 if args.expect:need(exact(out,json.loads(args.expect.read_text())),'typed receipt')
 else:args.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print('PASS: actual U15 block trace -8942; uniform positive conjugation; 13 exact even-block Pell powers.')
if __name__=='__main__':main()
