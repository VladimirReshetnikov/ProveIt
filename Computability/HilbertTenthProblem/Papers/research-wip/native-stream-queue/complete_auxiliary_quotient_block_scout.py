#!/usr/bin/env python3
"""Bounded exact V-block audit; no predecessor code executes."""
import argparse
import copy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path

PINS = {
 'complete85_auxiliary_bezout_projection.py':'3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0',
 'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
 'complete86_ordinary_auxiliary_projection.py':'130c8a09570866f3b510f4092aef3ab7fd61154f6c8776fcdba870d80a59019d',
 'complete86_ordinary_auxiliary_projection.json':'f46dd919a038b6dd646489e64585331de30b8c91a380cf9611afbf288122a9a6',
 'complete86_ordinary_auxiliary_projection.md':'cc3230f10c193d35df2820dad73b71f03b09493dfeca52618b1b23e9e0e59570',
 'auxiliary_norm_five_gate_lower_bound.md':'e2d587ed384b77703fff8be6a7eaa0d619ee11d9c922749c8a2024ae45934910',
}
V_OLD = [
 ['auxiliary_Tf','*','auxiliary_quotient','f'],
 ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2','*','r_lhs','L16'],
 ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
]
V_HORNER = [
 ['vb_cT','*','R10a','auxiliary_quotient'],
 ['vb_Rf','*','r_lhs','f'],
 ['vb_o','-','vb_cT','vb_Rf'],
 ['vb_fo','*','f','vb_o'],
 ['aux_u_rhs','-','vb_fo','R10a'],
]
V_FLAT = [
 ['vb_cT','*','R10a','auxiliary_quotient'],
 ['vb_cTf','*','vb_cT','f'],
 ['vb_Rf2','*','r_lhs','L16'],
 ['vb_left','-','vb_cTf','R10a'],
 ['aux_u_rhs','-','vb_left','vb_Rf2'],
]
GAP_PROVIDER = [
 ['vb_a_plus_one','+','R12',1],
 ['vb_gap_base','*','vb_a_plus_one','ic2'],
 ['f','+','strong_gap','vb_gap_base'],
]
GAP_FACTORED = [
 ['vb_aux_root','*','i','Ac2'],
 ['R16','*','vb_aux_root','vb_aux_root'],
 ['vb_gap_square','*','strong_gap','strong_gap'],
 ['vb_twice_base','*',2,'vb_gap_base'],
 ['vb_gap_minus_t','-','strong_gap','ic2'],
 ['vb_gap_cross','*','vb_twice_base','vb_gap_minus_t'],
 ['norm_strong','+','vb_gap_square','vb_gap_cross'],
]

def require(ok, message):
 if not ok: raise ValueError(message)

def digest(data): return hashlib.sha256(data).hexdigest()

def same(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def evaluate(source, values):
 e=dict(values)
 for n,op,a,b in source:
  x=e[a] if isinstance(a,str) else a
  y=e[b] if isinstance(b,str) else b
  e[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return e

def live_schedule(rows, free, output):
 table={r[0]:r for r in rows}
 require(len(table)==len(rows),'duplicate definitions')
 require(not(set(table)&set(free)),'free/register collision')
 marked=set()
 def visit(n):
  if not isinstance(n,str) or n in free: return
  require(n in table,'undefined '+n)
  if n in marked: return
  marked.add(n)
  visit(table[n][2]);visit(table[n][3])
 visit(output)
 require(marked==set(table),'dead private gates')
 out=[];done=set(free)
 while len(out)<len(rows):
  advanced=False
  for row in rows:
   n,op,a,b=row
   if n in done: continue
   require(op in ('*','+','-'),'bad opcode')
   if all(not isinstance(x,str) or x in done for x in (a,b)):
    out.append(row);done.add(n);advanced=True
  require(advanced,'cycle')
 used={x for r in rows for x in r[2:] if isinstance(x,str)}&set(free)
 require(used==set(free),'unused supplied port')
 return out

def packet(parent, kind):
 p=copy.deepcopy(parent)
 rows=p['source']; table={r[0]:r for r in rows}
 require(all(table.get(r[0])==r for r in V_OLD),'unexpected V producer')
 require(table['L16']==['L16','*','f','f'],'paid f square')
 oldnames={r[0] for r in V_OLD}
 require(all(not(any(x in oldnames-{'aux_u_rhs'} for x in r[2:])) for r in rows if r[0] not in oldnames),'private V consumer')
 if kind in ('horner','flat'):
  rows=[r for r in rows if r[0] not in oldnames]+copy.deepcopy(V_HORNER if kind=='horner' else V_FLAT)
 elif kind.startswith('gap_'):
  require(p['normalized'] is True,'gap chart normalized only')
  premises=[['c2','*','R10a','R10a'],['Ac2','*','A','c2'],['ic2','*','i','c2'],['a_square','*','R12','R12'],['a4','*',4,'R12'],['a4m5','+','a4',3],['A','+','a_square','a4m5']]
  require(all(table.get(r[0])==r for r in premises),'gap coefficient premises')
  p['free']=['strong_gap' if x=='f' else x for x in p['free']]
  p['witnesses']=['strong_gap' if x=='f' else x for x in p['witnesses']]
  rows=rows+copy.deepcopy(GAP_PROVIDER)
  if kind=='gap_factored':
   old={'ic22','strong_difference','R16','norm_strong'}
   require(table['ic22']==['ic22','*','ic2','ic2'] and table['strong_difference']==['strong_difference','*','A','ic22'],'strong cone')
   require(table['R16']==['R16','*','A','strong_difference'] and table['norm_strong']==['norm_strong','-','L16','strong_difference'],'strong output')
   require(all(not(any(x in old-{'R16','norm_strong'} for x in r[2:])) for r in rows if r[0] not in old),'private strong consumers')
   rows=[r for r in rows if r[0] not in old]+copy.deepcopy(GAP_FACTORED)
 else: require(kind=='baseline','unknown kind')
 rows=live_schedule(rows,p['free'],p['output'])
 counts={'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows),'total':len(rows)}
 deg={x:0 if x in p['fixed_numerals'] else 1 for x in p['free']}
 for n,op,a,b in rows:
  da=deg[a] if isinstance(a,str) else 0; db=deg[b] if isinstance(b,str) else 0
  deg[n]=da+db if op=='*' else max(da,db)
 return {'kind':kind,'normalized':p['normalized'],'source':rows,'free':p['free'],'fixed_numerals':p['fixed_numerals'],'ordinary_input':p['ordinary_input'],'witnesses':p['witnesses'],'output':p['output'],'ledger':counts,'exact_degree':None if kind.startswith('gap_') else p['exact_degree'],'gate_degree_upper':deg[p['output']],'relation':'signed polynomial graph identity after f=strong_gap+(a+1)*i*c²; positive-zero bijection' if kind.startswith('gap_') else 'identical polynomial on unchanged supplied coordinates'}

# Tiny exact sparse polynomial arithmetic; only local identities are expanded.
N=8
ZERO=(0,)*N

def const(x): return {} if x==0 else {ZERO:Fraction(x)}
def var(i): return {tuple(int(j==i) for j in range(N)):Fraction(1)}
def add(a,b,sgn=1):
 o=dict(a)
 for m,c in b.items():
  o[m]=o.get(m,0)+sgn*c
  if not o[m]: del o[m]
 return o

def mul(a,b):
 o={}
 for x,c in a.items():
  for y,d in b.items():
   z=tuple(i+j for i,j in zip(x,y));o[z]=o.get(z,0)+c*d
 return {m:c for m,c in o.items() if c}

def local_checks():
 c,T,R,f,a,t,g,i=[var(j) for j in range(N)]
 f2=mul(f,f); target=add(add(mul(c,mul(T,f)),c,-1),mul(R,f2),-1)
 env={'R10a':c,'auxiliary_quotient':T,'r_lhs':R,'f':f,'L16':f2}
 for rows in (V_OLD,V_HORNER,V_FLAT):
  e=dict(env)
  for n,op,x,y in rows:
   x=e[x] if isinstance(x,str) else const(x); y=e[y] if isinstance(y,str) else const(y)
   e[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
  require(e['aux_u_rhs']==target,'local V coefficient identity')
 b=add(a,const(1)); delta=add(mul(a,a),add(mul(const(4),a),const(3)))
 newf=add(g,mul(b,t))
 direct=add(mul(newf,newf),mul(delta,mul(t,t)),-1)
 factored=add(mul(g,g),mul(mul(const(2),mul(b,t)),add(g,t,-1)))
 require(direct==factored,'gap strong coefficient identity')
 lhs=mul(mul(delta,delta),mul(mul(i,mul(c,c)),mul(i,mul(c,c))))
 h=mul(i,mul(delta,mul(c,c)))
 require(lhs==mul(h,h),'auxiliary coefficient identity')
 # Symbolic determinant of the quadratic coefficient matrix in c,T,f,R.
 alpha,beta=var(0),var(1);z=const(0);half=const(Fraction(1,2))
 mat=[[alpha,half,z,z],[half,z,z,z],[z,z,beta,const(Fraction(-1,2))],[z,z,const(Fraction(-1,2)),z]]
 det=const(0)
 for p in itertools.permutations(range(4)):
  inv=sum(p[u]>p[v] for u in range(4) for v in range(u+1,4)); term=const((-1)**inv)
  for u in range(4):term=mul(term,mat[u][p[u]])
  det=add(det,term)
 require(det==const(Fraction(1,16)),'uniform quadratic determinant')
 return {'V_templates':3,'V_monomials':len(target),'gap_strong_identity':True,'gap_auxiliary_coefficient_identity':True,'quadratic_matrix_determinant':'1/16','lower_bound_scope':'Independent c,T,R,f; initially paid c²,f²,Δc²; Δ specialized to 0 for lower bound. Arbitrary rational constants and unrestricted other operation type. No whole-core lower bound.'}

def verify(root):
 for name,sha in PINS.items(): require(digest((root/name).read_bytes())==sha,'pin '+name)
 parents=[json.loads((root/(name+'.json')).read_text())['packet'] for name in ('complete85_auxiliary_bezout_projection','complete86_ordinary_auxiliary_projection')]
 forms=[];numerics=0;rationals=0;retained=0
 for parent in parents:
  require(len(parent['witnesses'])==18 and parent['ordinary_input']=='x','parent interface')
  kinds=['baseline','horner','flat']+(['gap_direct','gap_factored'] if parent['normalized'] else [])
  for kind in kinds:
   p=packet(parent,kind); forms.append(p)
   for j in range(48):
    values={x:Fraction(((j+3)*(k+5))%17-8,1 if j<24 else (k%3)+1) for k,x in enumerate(p['free'])}
    e=evaluate(p['source'],values)
    old=dict(values)
    if kind.startswith('gap_'):
     old.pop('strong_gap');old['f']=e['f']
    pe=evaluate(parent['source'],old)
    require(e[p['output']]==pe[parent['output']],'entire signed graph evaluation')
    for row in p['source']:
     n=row[0]
     if n in pe:
      require(e[n]==pe[n],'retained register '+n);retained+=1
    numerics+=1;rationals+=j>=24
 counts=[p['ledger']['total'] for p in forms]
 require(counts==[85,85,85,88,91,86,86,86],'complete ledger')
 # Exact positive strong-component examples and gap-coordinate inverses.
 pell=0
 for a in range(1,7):
  A=a+2;D=A*A-1;F,U=1,0
  for n in range(1,9):
   F,U=A*F+D*U,F+A*U
   g=F-(a+1)*U
   require(g>0 and F==g+(a+1)*U and F*F-D*U*U==1,'positive Pell gap')
   pell+=1
 return {'source_sha256':digest(Path(__file__).read_bytes()),'pins':copy.deepcopy(PINS),'scope':'Eight complete source schedules only; six same-polynomial schedules and two normalized positive Pell-gap charts. No improved universal bound or global circuit optimum. Component examples are not full native zeros.','local':local_checks(),'complete_forms':forms,'general_source_proofs':{'V_private_cuts':6,'gap_provider_graphs':2,'gap_factored_norm_and_coefficient_cuts':2,'full_retained_rows_preserved_by_construction':True},'aggregate_gates':sum(len(p['source']) for p in forms),'whole_signed_evaluations':numerics,'rational_assignments':rationals,'retained_register_values':retained,'positive_strong_component_cases':pell,'proof_scope':'General lower bound and positive chart theorem are in the companion proof; coefficient identities and finite checks do not replace them.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
 require(not(args.output and args.expect),'choose output or expect')
 result=verify(args.root)
 if args.expect:require(same(result,json.loads(args.expect.read_text())),'receipt differs')
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','sources':len(result['complete_forms']),'gates':result['aggregate_gates'],'whole_evaluations':result['whole_signed_evaluations']}))
if __name__=='__main__':main()
