#!/usr/bin/env python3
"""Shared strong/auxiliary monomial-coefficient scheduling: bounded negative scout.
No parent imports, source writes, or claim that finite cases prove universality.
"""
import argparse,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660','complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98','complete75_normalized_strong87.py':'7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8','complete75_coupled_index_linear88.py':'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed','complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749'}
import itertools
WITNESSES=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap','eta','zeta','y_aux','Z','delta','rho','sigma']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
def inspect(rows):
 names={n for n,_,_,_ in rows};need(len(names)==len(rows),'duplicate source name')
 free={a for _,_,x,y in rows for a in (x,y) if type(a)is str and a not in names};seen=set(free)
 for n,op,a,b in rows:
  need(type(n)is str and op in ['+','-','*'] and n not in seen,'bad row')
  need(all(type(x)is int or type(x)is str and x in seen for x in [a,b]),'bad operand');seen.add(n)
 d={n:(a,b) for n,_,a,b in rows};live=set()
 def visit(x):
  if type(x)is int or x in free or x in live:return
  need(x in d,'not closed');live.add(x)
  for y in d[x]:visit(y)
 visit('polynomial');need(live==names,'dead gates')
 c=Counter(op for _,op,_,_ in rows)
 return {'operations':len(rows),'M':c['*'],'A':c['+']+c['-'],'free':sorted(free),'live_gates':len(live)}
ATOMS={(1,0,0):'A',(0,1,0):'i',(0,0,1):'R10a',(0,0,2):'c2',(1,0,2):'Ac2'}
TARGETS=((1,2,4),(2,2,4))
BOX=(2,2,4)
OLD_BLOCK=('ic2','ic22','strong_difference','R16')

def search():
 states={frozenset(ATOMS):()};levels=[];solutions=[];edge_count=[]
 for depth in range(4):
  entries=[]
  for st in states:entries.append(sorted(st))
  entries.sort()
  levels.append({'depth':depth,'reachable_sets':len(states),'sets_sha256':sha(json.dumps(entries,separators=(',',':')).encode()),'both_targets_present':sum(all(x in st for x in TARGETS) for st in states)})
  need(not levels[-1]['both_targets_present'],'unexpected <=3 coefficient schedule')
  nxt={};edges=0
  for st,path in states.items():
   for a,b in itertools.combinations_with_replacement(sorted(st),2):
    c=tuple(x+y for x,y in zip(a,b))
    if c in st or any(x>y for x,y in zip(c,BOX)):continue
    edges+=1;new=st|{c};route=path+((a,b,c),)
    if all(x in new for x in TARGETS):solutions.append(route)
    if depth<3:nxt.setdefault(new,route)
  edge_count.append(edges);states=nxt
 need([x['reachable_sets'] for x in levels]==[1,13,116,891],'search census changed')
 need(len(solutions)==21 and len({tuple(sorted(c for a,b,c in p)) for p in solutions})==12,'terminal transition census changed')
 return levels,edge_count,solutions

def emit(old,path):
 nodes={n:(o,a,b) for n,o,a,b in old if n not in OLD_BLOCK};names=dict(ATOMS);rows=[]
 for idx,(a,b,c) in enumerate(path):
  need(a in names and b in names and c not in names,'invalid monomial schedule')
  need(tuple(x+y for x,y in zip(a,b))==c,'wrong exponent addition')
  n='shared_coefficient_'+str(idx);nodes[n]=('*',names[a],names[b]);rows.append([n,'*',names[a],names[b]]);names[c]=n
 alias={'strong_difference':names[TARGETS[0]],'R16':names[TARGETS[1]]}
 for n,(o,a,b) in list(nodes.items()):nodes[n]=(o,alias.get(a,a),alias.get(b,b))
 out=[];seen=set();active=set()
 def visit(n):
  if type(n)is int or n not in nodes or n in seen:return
  need(n not in active,'cycle');active.add(n);op,a,b=nodes[n];visit(a);visit(b);out.append([n,op,a,b]);seen.add(n);active.remove(n)
 visit('polynomial');return out,alias

def monomial_proof(old,new,alias):
 # Expand multiplication-only cones at independent Delta,i,c cuts, including
 # both actually paid c² and Delta*c² initial ports.
 def exponents(rows):
  env={'A':(1,0,0),'i':(0,1,0),'R10a':(0,0,1)}
  for n,op,a,b in rows:
   if n in env:continue
   if op=='*' and type(a)is str and a in env and type(b)is str and b in env:env[n]=tuple(x+y for x,y in zip(env[a],env[b]))
  return env
 a=exponents(old);b=exponents(new)
 for vec,name in ATOMS.items():need(a[name]==vec and b[name]==vec,'initial actual port identity')
 for vec,name in zip(TARGETS,['strong_difference','R16']):need(a[name]==vec and b[alias[name]]==vec,'literal coefficient identity')
 return 7

def downstream(old,new,alias):
 table={}
 def inter(x):
  if x not in table:table[x]=len(table)
  return table[x]
 def run(rows,cuts):
  env={}
  for n,op,a,b in rows:
   if n in cuts:env[n]=inter(('proved_monomial',cuts[n]));continue
   a=inter(('int',a)) if type(a)is int else env.get(a,inter(('input',a)))
   b=inter(('int',b)) if type(b)is int else env.get(b,inter(('input',b)))
   if op in ['+','*'] and b<a:a,b=b,a
   env[n]=inter((op,a,b))
  return env
 before=run(old,{'strong_difference':0,'R16':1});after=run(new,{alias['strong_difference']:0,alias['R16']:1})
 for n in FACTORS+['polynomial']:need(before[n]==after[n],'complete downstream identity '+n)
 return 9

def verify(root):
 for f,s in PINS.items():need(sha((root/f).read_bytes())==s,'parent source pin '+f)
 old=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())['source'][0]['source'];baseline=inspect(old)
 need(baseline['operations']==87 and baseline['M']==48 and baseline['A']==39,'wrong baseline')
 consumers={n:[] for n in OLD_BLOCK}
 for n,o,a,b in old:
  for v in (a,b):
   if v in consumers:consumers[v].append(n)
 need(consumers=={'ic2':['ic22','ic22'],'ic22':['strong_difference'],'strong_difference':['R16','norm_strong'],'R16':['L17']},'hidden coefficient consumers')
 levels,edges,solutions=search();forms=[];comparisons=0;signed=0;identities=0;rng=random.Random(870043)
 for idx,path in enumerate(solutions):
  rows,alias=emit(old,path);led=inspect(rows);need(led==baseline,'non-tied full source cost/interface')
  identities+=monomial_proof(old,rows,alias)+downstream(old,rows,alias)
  for case in range(32):
   v={n:rng.randrange(-4,5) if case%2 else rng.randrange(1,5) for n in WITNESSES+['x']};B=[16,32,64,128][case%4]
   v.update(Bm1=B-1,Kconstant=3+B*5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=4+B-1)
   a=execute(old,v);b=execute(rows,v)
   for n in FACTORS+['polynomial']:need(a[n]==b[n],'numeric full factor/output identity');comparisons+=1
   signed+=case%2
  forms.append({'index':idx,'monomial_products':[[list(a),list(b),list(c)] for a,b,c in path],'source':rows,'coefficient_aliases':alias,'ledger':led,'exact_degree':169,'degree_reason':'Same complete polynomial as authenticated87/169 parent','all_value_identity':True})
 return {'status':'PASS_BOUNDED_NO_IMPROVEMENT','self_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'baseline':baseline,'scope':'Only multiplication-only coefficient-one monomial schedules for Q=Delta*i²*c⁴ and K=Delta²*i²*c⁴ at fixed paid ports Delta,i,c,c²,Delta*c². No general arithmetic lower bound or claim covering additions, subtractions, altered coordinates, norms or finalizers.','proof_domain':'Identical entire polynomial on every integer/rational tuple; inherited full positive-zero universal contract unchanged.','initial_ports':[[list(k),v] for k,v in sorted(ATOMS.items())],'targets':[list(v) for v in TARGETS],'target_box':BOX,'reachable_levels':levels,'eligible_edges_by_level':edges,'minimal_added_multiplications':4,'canonical_prefix_terminal_transitions':21,'distinct_terminal_monomial_sets':12,'literal_symbolic_checks':identities,'complete_numeric_assignments':21*32,'signed_assignments':signed,'full_factor_output_comparisons':comparisons,'forms':forms}

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=json.loads(json.dumps(verify(v.root)))
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'saved receipt mismatch')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['minimal_added_multiplications'],[(x['depth'],x['reachable_sets']) for x in r['reachable_levels']],r['complete_numeric_assignments'])
if __name__=='__main__':main()
