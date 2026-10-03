#!/usr/bin/env python3
"""Fresh finite grouping search for eight actual U9 tail-shift bases.
Read authenticated JSON; isolate only the reviewed subset-DP definition.
No historical builders, old census, or materialized enormous numerals.
"""
import argparse, ast, copy, hashlib, json, random
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
PINS = {'neary_woods_universal_product_scale253.json': 'a32b58aee2baf3d6d1a66489784f9cc9f5ab2bac296b9a7eb0a116785a3eef1b', 'neary_woods_universal_product_scale253.md': '9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f', 'neary_woods_universal_product_scale_partitions.json': '4964171fecbbbf7a8b392a250514ecff73f36b51334d01c435d3203fa4fd949e', 'neary_woods_universal_product_scale_partitions.md': 'bd622f5b13098d7af85432dfa263bb1bff9fa544f1b929da15116d05d097480e', 'neary_woods_universal_joint_and_coupled_partitions.py': '0fbae7aff7568958e9fff00dc2678b1ab1801a5a59d4e58f5e3ea4000dedde74', 'neary_woods_universal_joint_and_coupled_partitions.md': '0291eb1ce182bbe5e9799ee5641389cb09130d195634f347b47c9abfac5306b6', 'neary_woods_universal_tail_quotient253.json': '48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f', 'neary_woods_universal_tail_quotient253.md': '328b9a3d62a989f78cd3c7b388eba01800a9d92e7cb8df6ac58184df9982653b', 'review_neary_woods_tail_quotient_math.json': 'a4628a89462a1073be7c50c4aa5b119c66e80b7e5cdb6803be19c16c6839e8f3', 'review_neary_woods_tail_quotient_math.md': '4efffe5d793992c4e2fc3dc9112482cda55780ab7746b2d5e98d0b3275eedda5', 'binary_tag_parameterized_compressed_compiler.py': '13da39c3292f8e19f7881f4543fa704c42edec12f29bd10b06f2df555385c0df', 'neary_woods_universal_u9_tag_chain.json': 'b4d78b1be42f6e8c16180311ce371c486d75f9de646b4d78edaf0bcd2491b727', 'neary_woods_tail_quotient_all16.py': '0ed907103449c2fea80113ef39c407531c4350c8e8207a888c23f5a299f664b9', 'neary_woods_tail_quotient_all16.json': '13282605960e782b2389042f2ebd6ce12f3961c8c48e579a86739bc1e77ee6da', 'neary_woods_tail_quotient_all16.md': 'c0cb462011e78cbb879ca64300f48d3dfb25241de66b0de08dcc5d9d1d7f47e4'}
PARENT='neary_woods_universal_product_scale253.json'
OLD='neary_woods_universal_product_scale_partitions.json'
OPTIMIZER='neary_woods_universal_joint_and_coupled_partitions.py'
BETA='and__bound_beta'; CUT='and__bs_X_bound'; Z='factored_pack_Z'; S='factored_pack_inner'

def need(c,m):
 if not c:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def authenticate(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'source pin: '+name)
def closure(rows,roots):
 nodes={n:(a,b) for n,o,a,b in rows};live=set();todo=list(roots)
 while todo:
  x=todo.pop()
  if type(x)is str and x in nodes and x not in live:live.add(x);todo.extend(nodes[x])
 return [r for r in rows if r[0] in live]
def degree_table(rows,coordinates):
 d={n:1 for n in coordinates};nodes={n:(o,a,b) for n,o,a,b in rows}
 for pre in ('geo__','and__'):
  X,a,c,G,H=[pre+s for s in ('wn2','R12','R10a','gam','a4m5')]
  expected={pre+'R15':('-',pre+'L15',pre+'Ac2'),pre+'L15':('*',pre+'R14',pre+'R14'),pre+'R14':('+',pre+'D1',G),pre+'D1':('+',X,pre+'cam2'),pre+'cam2':('*',c,a),pre+'A':('+',pre+'a_square',H),pre+'a_square':('*',a,a),H:('+',pre+'a4',3),pre+'a4':('*',4,a),G:('*',pre+'ga',H),pre+'Ac2':('*',pre+'A',pre+'c2'),pre+'c2':('*',c,c)}
  need(all(nodes.get(n)==v for n,v in expected.items()),'literal main-norm cone')
 at=lambda x:d[x] if type(x)is str else 0
 for n,o,a,b in rows:
  if n in ('geo__R15','and__R15'):
   pre=n[:-3];X,A,c,G,H=[d[pre+s] for s in ('wn2','R12','R10a','gam','a4m5')]
   # All-value identity: (X+G)(X+G+2ac)-Hc^2.
   d[n]=max(2*X,2*G,X+G,X+A+c,G+A+c,H+2*c)
  else:d[n]=at(a)+at(b) if o=='*' else max(at(a),at(b))
 return d

def graph_ledger(rows,out,parameters,auxiliaries,recipes):
 known=set(parameters+auxiliaries);need(len(known)==len(parameters)+len(auxiliaries),'unique supplied coordinates');fixed=set();M=0
 for n,o,a,b in rows:
  need(type(n)is str and n not in known and o in ('+','-','*'),'unique typed operation')
  for x in(a,b):
   if type(x)is str:need(x in known,'closed graph')
   elif type(x)is dict:need(set(x)=={'fixed_numeral'} and x['fixed_numeral'] in recipes,'fixed leaf');fixed.add(x['fixed_numeral'])
   else:need(type(x)is int,'integer leaf')
  known.add(n);M+=o=='*'
 need(len(closure(rows,[out]))==len(rows),'every paid gate live')
 supplied={x for n,o,a,b in rows for x in (a,b) if type(x)is str and x in parameters+auxiliaries}
 need(supplied==set(parameters+auxiliaries),'all supplied coordinates used')
 need(fixed==set(recipes),'all eleven numeral roles retained')
 return dict(operations=len(rows),M=M,A=len(rows)-M,witnesses=len(auxiliaries),supplied_parameters=len(parameters),all_gates_live=True,fixed_numeral_roles=len(fixed))

def base(entry,index):
 rows=copy.deepcopy(entry['source']);nodes={n:(o,a,b) for n,o,a,b in rows}
 need(nodes[CUT]==('+',S,BETA),'literal old tail cut')
 need([n for n,o,a,b in rows if BETA in (a,b)]==[CUT],'single quotient consumer')
 need([n for n,o,a,b in rows if CUT in (a,b)]==['and__wn2'],'single cut consumer')
 need(nodes[Z]==('*','factored_pack_q_minus_one','and__F3'),'literal tail offset')
 need(nodes[S]==('+','factored_pack_A_plus_one','factored_pack_scaled_B'),'literal old offset')
 need(all(BETA not in r[2:] and CUT not in r[2:] for r in closure(rows,[S,Z])),'offsets independent of beta')
 rows=[[n,o,Z,b] if n==CUT else [n,o,a,b] for n,o,a,b in rows]
 factors=list(entry['ledger']['degree']['factor_degree_bounds'])
 ordinary=[[a,b] for n,o,a,b in rows if n.startswith('loader_residual_')]
 need(all(o=='-' for n,o,a,b in rows if n.startswith('loader_residual_')),'ordinary residual signs')
 core=closure(rows,factors+[x for pair in ordinary for x in pair]);coordinates=entry['parameters']+entry['auxiliaries']
 degrees=degree_table(core,coordinates)
 olddegrees=degree_table(entry['source'],coordinates)
 need(olddegrees[entry['output']]==entry['ledger']['polynomial']['degree_upper_bound'],'old bound independently reproduced')
 return dict(saved_parent_index=index,base=index%8,merged=index>=8,normalized=entry['ledger']['normalized_prefixes'],positive_scale=entry['ledger']['positive_scale_prefixes'],parameters=entry['parameters'],auxiliaries=entry['auxiliaries'],source=rows,output=entry['output'],core=core,factors=factors,ordinary=ordinary,weights=[degrees[n] for n in factors],residual=max([0]+[max(degrees.get(a,0),degrees.get(b,0)) for a,b in ordinary]),core_operations=len(core),core_M=sum(o=='*' for n,o,a,b in core),canonical_degree_upper_bound=degree_table(rows,coordinates)[entry['output']])

def emit(b,plan):
 rows=copy.deepcopy(b['core']);groups=[]
 def gate(name,op,a,v):
  name='tailpart__'+name;rows.append([name,op,a,v]);return name
 for j,block in enumerate(plan['partition']):
  g=b['factors'][block[0]]
  for k,i in enumerate(block[1:]):g=gate('group_%d_%d'%(j,k),'*',g,b['factors'][i])
  groups.append(g)
 comparisons=copy.deepcopy(b['ordinary'])+[[g,1] for g in groups]
 anchor=plan['anchor'];terms=[]
 for j,(a,v) in enumerate(b['ordinary']):
  r=gate('ordinary_%d'%j,'-',a,v);terms.append(gate('ordinary_square_%d'%j,'*',r,r))
 for j,g in enumerate(groups):
  if j==anchor:continue
  r=gate('unit_%d'%j,'-',g,1);terms.append(gate('unit_square_%d'%j,'*',r,r))
 if terms:
  out=terms[0]
  for j,t in enumerate(terms[1:]):out=gate('sum_%d'%j,'+',out,t)
  if anchor is not None:
   positive=gate('positive','+',out,1);out=gate('scaled','*',groups[anchor],positive);out=gate('output','-',out,1)
 else:
  need(anchor==0 and len(groups)==1,'pure product finalizer');out=gate('output','-',groups[0],1)
 certificate=dict(operations=len(b['core'])+len(b['factors'])-len(groups),M=b['core_M']+len(b['factors'])-len(groups),A=len(b['core'])-b['core_M'],comparisons=len(comparisons),witnesses=len(b['auxiliaries']))
 return rows,out,groups,comparisons,certificate

def execute(rows,values,numerals):
 e=dict(values)
 def at(x):return e[x] if type(x)is str else numerals[x['fixed_numeral']] if type(x)is dict else x
 for n,o,a,b in rows:
  a,b=at(a),at(b);e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e

def graph_pullback(old_rows,new_rows,coordinates):
 # The sole changed sum satisfies (beta+Z-S)+S=beta+Z;
 # induction at every downstream DAG gate proves the full identity.
 table={}
 def intern(x):
  if x not in table:table[x]=len(table)
  return table[x]
 def graph(rows):
  e={n:intern(('supplied',n)) for n in coordinates}
  at=lambda v:e[v] if type(v)is str else intern(('literal',stable(v)))
  for n,o,a,v in rows:e[n]=intern(('proved_tail_cut',)) if n==CUT else intern((o,at(a),at(v)))
  return e
 need([[a,v] for a,v in zip(old_rows,new_rows) if a!=v]==[[[CUT,'+',S,BETA],[CUT,'+',Z,BETA]]] and len(old_rows)==len(new_rows),'sole changed operand in complete source')
 left,right=graph(old_rows),graph(new_rows)
 need(all(left[n]==right[n] for n,o,a,v in new_rows),'all complete registers agree under pullback')
 return len(new_rows)

def frontier(records,witnesses=None):
 xs=sorted((x for x in records if witnesses is None or x['witnesses']==witnesses),key=lambda x:(x['operations'],x['degree_upper_bound'],x['base'],x['groups']))
 out=[];bound=float('inf')
 for r in xs:
  if r['degree_upper_bound']<bound:out.append(r);bound=r['degree_upper_bound']
 return out

def load_optimizer(root):
 tree=ast.parse((root/OPTIMIZER).read_text());nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='optimal_partitions']
 need(len(nodes)==1 and not nodes[0].decorator_list,'isolated reviewed definition')
 namespace={'lru_cache':lru_cache}
 exec(compile(ast.Module(body=nodes,type_ignores=[]),'pinned subset minimax function','exec'),namespace)
 return namespace['optimal_partitions']

def small_validation(opt):
 # Separate restricted-growth enumeration, not calls into the old verifier.
 rng=random.Random(312604);cases=0;partitions=0
 for n in range(1,8):
  for repeat in range(2):
   weights=[rng.randrange(1,35) for _ in range(n)];r=rng.randrange(20);best={}
   def visit(i,groups):
    nonlocal partitions
    if i==n:
     partitions+=1;ws=[sum(weights[j] for j in g) for g in groups]
     values=[2*max([r]+ws)]+[w+2*max([r]+[x for j,x in enumerate(ws) if j!=a]) for a,w in enumerate(ws)]
     k=len(groups);best[k]=min(best.get(k,float('inf')),min(values));return
    for g in groups:g.append(i);visit(i+1,groups);g.pop()
    groups.append([i]);visit(i+1,groups);groups.pop()
   visit(0,[]);answer,_=opt(weights,r)
   need(best=={p['groups']:p['degree_upper_bound'] for p in answer},'independent small Bell enumeration');cases+=1
 return dict(instances=cases,partitions=partitions,maximum_factors=7)

def verify(root):
 authenticate(root);parent=json.loads((root/PARENT).read_text());historical=json.loads((root/OLD).read_text());entries=parent['canonical_sources'];need(len(entries)==16,'actual saved inventory')
 tree=ast.parse((root/'binary_tag_parameterized_compressed_compiler.py').read_text());recipes=[ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='NUMERALS' for t in n.targets)]
 need(len(recipes)==1 and len(recipes[0])==11,'eleven recipes');recipes=recipes[0]
 fixed=json.loads((root/'neary_woods_universal_u9_tag_chain.json').read_text())['fixed_recipe']
 opt=load_optimizer(root);validation=small_validation(opt);bases=[base(e,i) for i,e in enumerate(entries)];searches=[];plans=[];counts=Counter();ledgers=[]
 transferred=json.loads((root/'neary_woods_tail_quotient_all16.json').read_text())['forms']
 for b,t in zip(bases,transferred):
  need(b['source']==t['source'] and b['core']==t['core_source'] and b['factors']==t['inventory']['factor_ports'] and b['ordinary']==t['inventory']['ordinary_comparisons'],'independently rebuilt transfer agrees with frozen all16 packet')
 for i,b in enumerate(bases[:8]):
  need(b['weights']==bases[i+8]['weights'] and b['ordinary']==bases[i+8]['ordinary'] and b['core_operations']==bases[i+8]['core_operations'],'duration interfaces share weighted base')
  need('and__' in b['positive_scale'],'all eight eligible joint-scale projections')
  answer,stats=opt(b['weights'],b['residual']);floor=min([2*max(b['residual'],max(b['weights']))]+[sum(w for w in b['weights'] if w>t)+2*max(b['residual'],t) for t in set([0]+b['weights']) if t<max(b['weights'])])
  local=[]
  for plan in answer:
   p=copy.deepcopy(plan);g=p['groups'];n=len(b['factors']);m=len(b['ordinary']);cost=b['core_operations']+n+3*m-1+2*g
   if m==0 and g==1 and p['anchor'] is not None:cost=b['core_operations']+n
   p.update(base=i,operations=cost,witnesses=len(b['auxiliaries']))
   need(p['degree_upper_bound']>=floor,'analytic family floor');local.append(p);plans.append(p)
  need(min(p['degree_upper_bound'] for p in local)==floor,'floor attained')
  searches.append(dict(base=i,weights=b['weights'],factors=b['factors'],ordinary=b['ordinary'],residual=b['residual'],core_operations=b['core_operations'],core_M=b['core_M'],core_A=b['core_operations']-b['core_M'],family_floor=floor,best_by_group_count=local,statistics=stats))
 fronts={str(w):frontier(plans,w) for w in (None,43,44)}
 selected={(p['base'],p['groups']) for f in fronts.values() for p in f};sources=[];rng=random.Random(261312)
 for i,b in enumerate(bases):
  counts['canonical_register_pullbacks']+=graph_pullback(entries[i]['source'],b['source'],b['parameters']+b['auxiliaries'])
  oldbase=copy.deepcopy(b);oldbase['core']=closure(entries[i]['source'],b['factors']+[x for pair in b['ordinary'] for x in pair])
  for plan in searches[b['base']]['best_by_group_count']:
   rows,out,groups,comparisons,cert=emit(b,plan);ledger=graph_ledger(rows,out,b['parameters'],b['auxiliaries'],recipes);degrees=degree_table(rows,b['parameters']+b['auxiliaries'])
   need(ledger['operations']==plan['operations'] and degrees[out]==plan['degree_upper_bound'],'literal source matches paid objective')
   oldrows,oldout,oldgroups,oldcomparisons,oldcert=emit(oldbase,plan)
   need(oldout==out and oldgroups==groups and oldcomparisons==comparisons and oldcert==cert,'unchanged full grouping interface')
   counts['grouped_register_pullbacks']+=graph_pullback(oldrows,rows,b['parameters']+b['auxiliaries'])
   record=dict(saved_parent_index=i,base=b['base'],merged=b['merged'],groups=plan['groups'],partition=plan['partition'],anchor=plan['anchor'],group_degree_bounds=[sum(b['weights'][j] for j in g) for g in plan['partition']],degree_upper_bound=degrees[out],exact_degree_claimed=False,certificate=cert,polynomial=ledger,source_sha256=sha(stable(rows).encode()))
   ledgers.append(record);counts['compiled_sources']+=1;counts['paid_gates']+=len(rows)
   if (b['base'],plan['groups']) not in selected:continue
   source=dict(record,source=rows,output=out,parameters=b['parameters'],auxiliaries=b['auxiliaries'],factors=b['factors'],ordinary=b['ordinary'],group_registers=groups,comparisons=comparisons)
   for case in range(4):
    values={n:rng.randrange(-2,3) for n in b['parameters']+b['auxiliaries']};nums={n:rng.randrange(-2,3) for n in recipes}
    if case==3:values={n:Fraction(v,3) for n,v in values.items()};nums={n:Fraction(v,3) for n,v in nums.items()};counts['rational_values']+=1
    e=execute(rows,values,nums);v=dict(values);v[BETA]+=e[Z]-e[S];old=execute(oldrows,v,nums)
    need(all(old[n]==e[n] for n,o,a,z in rows),'every complete grouped register under signed pullback')
    def value(x):return e[x] if type(x)is str else x
    total=sum((value(a)-value(z))**2 for a,z in b['ordinary'])+sum((e[g]-1)**2 for j,g in enumerate(groups) if j!=plan['anchor'])
    expected=total if plan['anchor'] is None else e[groups[plan['anchor']]]*(1+total)-1
    need(e[out]==expected,'actual complete finalizer value')
    counts['full_finalizer_values']+=1;counts['complete_numeric_register_pullbacks']+=len(rows)
   sources.append(source)
 # Reuse only frozen minima for the eight unchanged, joint-unprojected bases.
 unchanged=[]
 for j,search in enumerate(historical['searches']):
  if 'and__' in search['positive_scale_prefixes']:continue
  for p in search['best_by_group_count']:
   unchanged.append(dict(base=8+j,groups=len(p['partition']),operations=p['polynomial']['operations'],degree_upper_bound=p['polynomial']['degree_upper_bound'],witnesses=p['certificate']['witnesses'],provenance='frozen unchanged minimum',normalized=search['normalized_prefixes'],positive_scale=search['positive_scale_prefixes']))
 need(len({p['base'] for p in unchanged})==8,'eight unchanged historical bases')
 combined={str(w):frontier(plans+unchanged,w) for w in (None,43,44,45)}
 need([(p['operations'],p['degree_upper_bound']) for p in fronts['43']]==[(253,982),(255,848),(256,802),(257,604),(258,558),(259,404),(260,398),(261,312)],'fresh 43-witness frontier')
 need(len(searches)==8 and len(ledgers)==240 and len(sources)==30,'bounded inventory')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,scope='Eight actual eligible bases times two duration interfaces. Every per-group optimum compiled and recounted; thirty frontier sources saved. Weighted degree upper bounds, not exact polynomial degrees or unrestricted lower bounds. Inherited unbounded valid shifted-U9 program/input relation only. No historical census run.',fixed_numeral_recipes=recipes,fixed_u9_recipe=fixed,degree_convention='Every supplied input/program parameter/positive witness degree1; each of eleven literal fixed numeral recipes degree0.',searches=searches,frontiers=fronts,combined_with_eight_unchanged_historical_bases=combined,ledgers=ledgers,selected_sources=sources,small_independent_validation=validation,audit_totals=dict(counts),positive_zero_claim='Within each fixed base every regrouping has the same complete positive zero set on valid program slices; the tail shift gives the reviewed signed pullback and positive-zero bijection. Cross-base parameterizations are not identified.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();receipt=verify(args.root)
 if args.expect:need(stable(receipt)==stable(json.loads(args.expect.read_text())),'exact saved receipt')
 if args.output:args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=receipt['status'],audit_totals=receipt['audit_totals'],frontier43=[(p['operations'],p['degree_upper_bound']) for p in receipt['frontiers']['43']],combined=[(p['operations'],p['degree_upper_bound'],p['witnesses']) for p in receipt['combined_with_eight_unchanged_historical_bases']['None']])))
if __name__=='__main__':main()
