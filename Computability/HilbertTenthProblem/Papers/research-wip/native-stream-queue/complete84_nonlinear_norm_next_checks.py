#!/usr/bin/env python3
"""Fresh data-only source audit and formal Cayley numerator identities.
No predecessor helper or old complete source is executed or imported.
"""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}
NEW = [
 ['cayley_den','-','kappa2','A'],
 ['cayley_sum','+','kappa2','A'],
 ['cayley_twok','+','index_rhs','index_rhs'],
 ['cayley_pD','*','cayley_sum','R14'],
 ['cayley_bc','*','cayley_twok','R10a'],
 ['cayley_Dbc','*','A','cayley_bc'],
 ['cayley_Dnum','+','cayley_pD','cayley_Dbc'],
 ['cayley_pc','*','cayley_sum','R10a'],
 ['cayley_bD','*','cayley_twok','R14'],
 ['cayley_cnum','+','cayley_pc','cayley_bD'],
 ['cayley_Dnum2','*','cayley_Dnum','cayley_Dnum'],
 ['cayley_cnum2','*','cayley_cnum','cayley_cnum'],
 ['cayley_Dcnum2','*','A','cayley_cnum2'],
 ['norm_main','-','cayley_Dnum2','cayley_Dcnum2'],
 ['cayley_den2','*','cayley_den','cayley_den'],
 ['cayley_target','*','A','cayley_den2'],
]

def need(v,m):
 if not v:raise ValueError(m)

def const(n):return {(0,)*5:n} if n else {}
def var(i):
 e=[0]*5;e[i]=1;return {tuple(e):1}
def add(p,q,s=1):
 r=dict(p)
 for e,c in q.items():r[e]=r.get(e,0)+s*c
 return {e:c for e,c in r.items() if c}
def mul(p,q):
 r={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(a+b for a,b in zip(e,f));r[g]=r.get(g,0)+c*d
 return {e:c for e,c in r.items() if c}
def serial(p):return [[list(e),c] for e,c in sorted(p.items())]
def run(root):
 for name,h in PINS.items():need(hashlib.sha256((root/name).read_bytes()).hexdigest()==h,name)
 packet=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
 source=packet['source'];old={r[0]:r for r in source}
 guards=[['A','+','a_square','a4m5'],['kappa2','*','index_rhs','index_rhs'],['index_rhs','+','odd_index','index_product'],['index_product','*','delta','A'],['odd_index','+','scaled_t','inner_bits'],['L15','*','R14','R14'],['c2','*','R10a','R10a'],['Ac2','*','A','c2'],['norm_main','-','L15','Ac2'],['aux_coefficient_root','*','i','Ac2'],['polynomial','-','seven_units','A']]
 for row in guards:need(old[row[0]]==row,'literal guard')
 keep=[r for r in source if r[0] not in ('L15','norm_main','polynomial')]
 remaining=keep+NEW+[['polynomial','-','seven_units','cayley_target']]
 out=[];seen=set(packet['free'])
 while remaining:
  ready=next((r for r in remaining if all(not isinstance(x,str) or x in seen for x in r[2:])),None)
  need(ready is not None,'topology');need(ready[0] not in seen,'duplicate')
  out.append(ready);seen.add(ready[0]);remaining.remove(ready)
 rows={r[0]:r for r in out};live={'polynomial'};pending=['polynomial']
 while pending:
  node=pending.pop()
  if node not in rows:continue
  for x in rows[node][2:]:
   if isinstance(x,str) and x not in live:live.add(x);pending.append(x)
 need(live==set(rows)|set(packet['free']),'liveness')
 m=sum(r[1]=='*' for r in out);a=len(out)-m
 need((len(source),len(out),m,a)==(84,98,56,42),'ledger')
 D,c,k,d,P=[var(i) for i in range(5)]
 env={'R14':D,'R10a':c,'index_rhs':k,'A':d,'kappa2':mul(k,k)}
 for name,op,x,y in NEW:
  left=env[x] if isinstance(x,str) else const(x);right=env[y] if isinstance(y,str) else const(y)
  env[name]=mul(left,right) if op=='*' else add(left,right,1 if op=='+' else -1)
 norm=add(mul(D,D),mul(d,mul(c,c)),-1)
 need(env['norm_main']==mul(env['cayley_den2'],norm),'norm numerator identity')
 oldfinal=add(mul(P,norm),d,-1)
 newfinal=add(mul(P,env['norm_main']),env['cayley_target'],-1)
 need(newfinal==mul(env['cayley_den2'],oldfinal),'whole factor identity')
 factored=[list(r) for r in source]
 factored[-1][0]='cayley_old_output'
 factored += [NEW[0],NEW[14],['polynomial','*','cayley_den2','cayley_old_output']]
 fm=sum(r[1]=='*' for r in factored);fa=len(factored)-fm
 need((len(factored),fm,fa)==(87,49,38),'factored ledger')
 fseen=set(packet['free']); frows={r[0]:r for r in factored}
 need(len(frows)==87,'factored duplicate')
 for row in factored:
  need(all(not isinstance(x,str) or x in fseen for x in row[2:]),'factored topology')
  fseen.add(row[0])
 flive={'polynomial'}; todo=['polynomial']
 while todo:
  node=todo.pop()
  if node not in frows:continue
  for x in frows[node][2:]:
   if isinstance(x,str) and x not in flive:flive.add(x);todo.append(x)
 need(flive==set(frows)|set(packet['free']),'factored liveness')
 return {'factored_source':factored,'factored_ledger':{'M':fm,'A':fa,'total':len(factored)},'status':'SCOPED_NONLINEAR_CLASSIFICATION_AND_CAYLEY_OBSTRUCTION','pins':PINS,'parent_packet':packet,'new_source':out,'literal_guards':guards,'retained_literal_rows':len(keep),'replacement_rows':NEW,'ledger':{'M':m,'A':a,'total':len(out)},'same_free_ports':packet['free'],'same_witnesses':packet['witnesses'],'same_input':packet['ordinary_input'],'formal_variable_order':['D','c','kappa','Delta','P_other_six_factors'],'formal_norm_numerator':serial(env['norm_main']),'formal_denominator_square':serial(env['cayley_den2']),'formal_whole_output':serial(newfinal),'whole_identity':'F98=(kappa^2-Delta)^2 F84','scope':'No circuit lower bound, new universal bound, or polynomial-classification proof by testing. Formal new-cut identities plus unchanged literal rows; no old source numerical execution.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=run(a.root)
 with a.output.open('x') as f:json.dump(r,f,indent=2);f.write('\n')
 print('PASS: explicit98=56M+42A and factored87=49M+38A; exact norm and whole-output multiplier identities.')
if __name__=='__main__':main()
