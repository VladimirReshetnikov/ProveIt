#!/usr/bin/env python3
"""Independent complete-source review of the bounded U9 tail partition packet.
Reads original saved JSON. Executes only the authenticated previous independent
review's arithmetic primitives; no author module, optimizer or old suite runs.
"""
import argparse,ast,copy,hashlib,json,random,types
from pathlib import Path
from fractions import Fraction
from collections import Counter
if not __debug__:raise RuntimeError('run without -O')
AUTHOR={
 'neary_woods_universal_tail_partitions.py':'e8c629e104dbd7fcb60881d23c61d68649f0f96e86123f008ad61ee1bee71f83',
 'neary_woods_universal_tail_partitions.json':'a0f113e07ac5ff57d957e2dfbf1cb5c974fe1ca1476aac14c8e6ea37e95f08d0',
 'neary_woods_universal_tail_partitions.md':'f6673dfebc6966b550ecd364c8f97b4cd02c7043a00070f6efc18a2102a7b387'}
REVIEW={
 'review_neary_woods_tail_quotient_all16.py':'2a53fe75a2a09da6c89d78998ce657808499a292e1a4236ec6c5340db5930875',
 'review_neary_woods_tail_quotient_all16.json':'bb5e24c65e4b42f227607f37c37fc68df86ae51c8f221526c328317f31635244',
 'review_neary_woods_tail_quotient_all16.md':'eaff6403d43070f10cd7d9246a48e81389c510981c2438e4b8a52cad53befa02'}
EXTRA={
 'review_u9_tail_weighted_minima.py':'a04f2ab03b8ac58baba482562369b59e3d33d65ba6ede1d1afeaf6d97b5cd194',
 'review_u9_tail_weighted_minima.json':'46e5dc74716572bb4ce347b09fc3b699c905f25c51f79dffc5c59d9b4a557ff4',
 'review_u9_tail_weighted_minima.md':'2735b134042a1281214419b36ddb711fee3a01be02458d1b3c301fd780afcdf9',
 'neary_woods_universal_product_scale_partitions.json':'4964171fecbbbf7a8b392a250514ecff73f36b51334d01c435d3203fa4fd949e',
 'neary_woods_universal_product_scale_partitions.md':'bd622f5b13098d7af85432dfa263bb1bff9fa544f1b929da15116d05d097480e',
 'neary_woods_universal_joint_and_coupled_partitions.py':'0fbae7aff7568958e9fff00dc2678b1ab1801a5a59d4e58f5e3ea4000dedde74',
 'neary_woods_universal_joint_and_coupled_partitions.md':'0291eb1ce182bbe5e9799ee5641389cb09130d195634f347b47c9abfac5306b6'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def digest(v):return sha(stable(v).encode())
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def blobs(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'pinned bytes '+n);out[n]=b
 return out

def load_review(path,raw):
 name='review_neary_woods_tail_quotient_all16.py';m=types.ModuleType('_independent_prior_ring');m.__file__=str(Path(path)/name)
 exec(compile(raw[name],m.__file__,'exec'),m.__dict__)
 return m

def table_degrees(core,coordinates,R,original):
 # Recheck source-guarded main identity on the full original child first;
 # use only its independently derived core degree entries below.
 full=R.normal_rows(R.independent_child(original));d,factors,res,leaders,shape=R.degrees_and_shape(full,coordinates,['@fixed:'+n for n in R.FIXED],original)
 return {n:d[n]for n,o,a,b in R.normal_rows(core)},factors,res,shape

def reconstruct_bases(parents,R,transfer):
 answer=[]
 for i,p in enumerate(parents):
  rows=R.independent_child(p);normal=R.normal_rows(rows);D={n:(o,a,b)for n,o,a,b in rows}
  factors=list(p['ledger']['degree']['factor_degree_bounds']);ordinary=[[a,b]for n,o,a,b in rows if n.startswith('loader_residual_')]
  roots=factors+[v for ab in ordinary for v in ab];live=R.ancestors(normal,roots);core=[r for r in rows if r[0]in live]
  degrees,ff,rr,shape=table_degrees(core,p['parameters']+p['auxiliaries'],R,p)
  need(ff==factors and [[D[n][1],D[n][2]]for n in rr]==ordinary,'actual factor and ordinary interface')
  need(core==transfer[i]['core_source']and rows==transfer[i]['source'],'independent original JSON reconstruction agrees with reviewed all16')
  need('and__bound_beta'not in R.ancestors(normal,['factored_pack_Z','factored_pack_inner']),'offset independence')
  oldcore=[r for r in p['source']if r[0]in live]
  need(len(oldcore)==len(core)and sum(a!=b for a,b in zip(oldcore,core))==1,'exact core edit')
  answer.append(dict(index=i,parent=p,rows=rows,core=core,oldcore=oldcore,factors=factors,ordinary=ordinary,degree=degrees,weights=[degrees[n]for n in factors],residual=max([0]+[max(degrees.get(a,0),degrees.get(b,0))for a,b in ordinary]),shape_premises=shape))
 return answer

def schedule(core,factors,ordinary,partition,anchor):
 # Independent literal emitter. Every block retains the stored factor order;
 # arithmetic names are chosen to compare the saved source bytes exactly.
 rows=copy.deepcopy(core);groups=[]
 def add(s,op,a,b):
  name='tailpart__'+s;rows.append([name,op,a,b]);return name
 for blockno,block in enumerate(partition):
  head=factors[block[0]]
  for j,f in enumerate(block[1:]):head=add('group_%d_%d'%(blockno,j),'*',head,factors[f])
  groups.append(head)
 parts=[]
 for i,(left,right)in enumerate(ordinary):
  residual=add('ordinary_%d'%i,'-',left,right)
  parts.append(add('ordinary_square_%d'%i,'*',residual,residual))
 for i,g in enumerate(groups):
  if i!=anchor:
   residual=add('unit_%d'%i,'-',g,1)
   parts.append(add('unit_square_%d'%i,'*',residual,residual))
 if parts:
  out=parts[0]
  for i,term in enumerate(parts[1:]):out=add('sum_%d'%i,'+',out,term)
  if anchor is not None:
   out=add('positive','+',out,1);out=add('scaled','*',groups[anchor],out);out=add('output','-',out,1)
 else:
  need(anchor==0 and len(groups)==1,'the only empty-SOS case');out=add('output','-',groups[0],1)
 return rows,out,groups

def exact_finalizer(rows,out,corelen,factors,ordinary,partition,anchor,R):
 # Independent coefficient proof, without cuts at computed group products.
 n=len(factors)+len(ordinary);z=(0,)*n
 def C(x):return {z:x}if x else{}
 def V(i):return {tuple(int(i==j)for j in range(n)):1}
 e={f:V(i)for i,f in enumerate(factors)}
 for name,op,a,b in rows[corelen:]:
  if name.startswith('tailpart__ordinary_')and op=='-':
   j=int(name.rsplit('_',1)[1]);need([a,b]==ordinary[j],'ordinary residual literal sign');e[name]=V(len(factors)+j);continue
  aa=C(a)if type(a)is int else e[a];bb=C(b)if type(b)is int else e[b]
  e[name]=R.smmul(aa,bb)if op=='*'else R.smadd(aa,bb,1 if op=='+'else -1)
 blocks=[]
 for block in partition:
  p=C(1)
  for j in block:p=R.smmul(p,V(j))
  blocks.append(p)
 value=C(0)
 for j in range(len(ordinary)):r=V(len(factors)+j);value=R.smadd(value,R.smmul(r,r))
 for j,p in enumerate(blocks):
  if j!=anchor:r=R.smadd(p,C(1),-1);value=R.smadd(value,R.smmul(r,r))
 if anchor is not None:value=R.smadd(R.smmul(blocks[anchor],R.smadd(C(1),value)),C(1),-1)
 need(e[out]==value,'complete formal factor/residual finalizer identity')
 return len(value),digest(sorted((list(m),c)for m,c in value.items()))

def minfront(rows,w=None):
 # This is only a readout of already supplied plans, not an optimizer.
 candidates=sorted([r for r in rows if w is None or r['witnesses']==w],key=lambda r:(r['operations'],r['degree_upper_bound'],r['base'],r['groups']))
 bound=float('inf');out=[]
 for r in candidates:
  if r['degree_upper_bound']<bound:out.append(r);bound=r['degree_upper_bound']
 return out

def verify(root,artifacts,review_root):
 ar=blobs(artifacts,AUTHOR);review=blobs(review_root,REVIEW);R=load_review(review_root,review)
 manifest=dict(R.PINS);manifest.update(R.AUTHOR);manifest.update(EXTRA);dep=blobs(root,manifest)
 saved=json.loads(ar['neary_woods_universal_tail_partitions.json']);ap=R.literal_assignment(ar['neary_woods_universal_tail_partitions.py'],'PINS')
 need(exact(saved['pins'],ap)and all(manifest.get(n)==h for n,h in ap.items()),'independent complete author dependency authentication')
 need(saved['source_sha256']==AUTHOR['neary_woods_universal_tail_partitions.py'],'author source receipt digest')
 p=json.loads(dep['neary_woods_universal_product_scale253.json'])['canonical_sources'];transfer=json.loads(dep['neary_woods_tail_quotient_all16.json'])['forms'];bases=reconstruct_bases(p,R,transfer)
 recipes=R.literal_assignment(dep['binary_tag_parameterized_compressed_compiler.py'],'NUMERALS');fixed=json.loads(dep['neary_woods_universal_u9_tag_chain.json'])['fixed_recipe']
 need(exact(saved['fixed_numeral_recipes'],recipes)and exact(saved['fixed_u9_recipe'],fixed),'eleven compiler recipe and fixed U9 interface conservation')
 need(len(saved['searches'])==8 and len(saved['ledgers'])==240 and len(saved['selected_sources'])==30,'literal bounded inventory')
 ledger_by_key={(r['saved_parent_index'],r['groups']):r for r in saved['ledgers']};selected={(r['saved_parent_index'],r['groups']):r for r in saved['selected_sources']}
 need(len(ledger_by_key)==240 and len(selected)==30,'no duplicated supplied records')
 counts=Counter();records=[];planlist=[];rng=random.Random(312261257)
 for i,b in enumerate(bases):
  old=b['parent'];search=saved['searches'][i%8];factors=b['factors'];ordinary=b['ordinary'];n=len(factors);m=len(ordinary);core=b['core'];cm=sum(r[1]=='*'for r in core);free=old['parameters']+old['auxiliaries'];fixedports=['@fixed:'+s for s in R.FIXED]
  need(search['base']==i%8 and search['weights']==b['weights']and search['factors']==factors and search['ordinary']==ordinary and search['residual']==b['residual'],'actual optimization input vectors and ordinary equations')
  need([search['core_operations'],search['core_M'],search['core_A']]==[len(core),cm,len(core)-cm],'actual weighted-base paid core')
  # Prefix floor is independently calculated, without running subset DP.
  ws=sorted(b['weights'],reverse=True);floors=[2*max([b['residual']]+ws)]+[sum(ws[:j])+2*max(b['residual'],ws[j]if j<len(ws)else 0)for j in range(1,len(ws)+1)]
  need(search['family_floor']==min(floors)==(312 if i%8<4 else 688),'closed-form family floor')
  plans=search['best_by_group_count'];need([r['groups']for r in plans]==list(range(1,n+1)),'one recorded plan per group count')
  counts['shape_premises']+=b['shape_premises']
  for plan in plans:
   k=plan['groups'];partition=plan['partition'];anchor=plan['anchor']
   need(type(partition)is list and len(partition)==k and all(type(g)is list and g and all(type(j)is int for j in g)for g in partition),'typed nonempty factor groups')
   need(sorted(j for g in partition for j in g)==list(range(n)),'disjoint exhaustive factor partition')
   need(anchor is None or type(anchor)is int and 0<=anchor<k,'optional valid anchor')
   rows,out,groups=schedule(core,factors,ordinary,partition,anchor);oldrows,oldout,oldgroups=schedule(b['oldcore'],factors,ordinary,partition,anchor)
   need(out==oldout and groups==oldgroups,'complete regrouped parent interface')
   normal=R.normal_rows(rows);oldnormal=R.normal_rows(oldrows);ring=R.RingDAG();ne=ring.run(normal,free+fixedports);pull=ring.add(ring.add(ring.val('and__bound_beta'),ne['factored_pack_Z']),ne['factored_pack_inner'],-1);oe=ring.run(oldnormal,free+fixedports,{'and__bound_beta':pull})
   need(all(ne[name]==oe[name]for name,op,a,z in normal),'entire grouped signed graph identity without author cuts')
   counts['grouped_register_identities']+=len(rows)
   M,A,naive=R.ledger(normal,free+fixedports,[out],fixedports)
   terms,fh=exact_finalizer(rows,out,len(core),factors,ordinary,partition,anchor,R)
   counts['formal_finalizers']+=1;counts['formal_finalizer_monomials']+=terms
   d={v:1 for v in free};d.update({v:0 for v in fixedports});d.update(b['degree'])
   for name,op,a,z in normal[len(core):]:
    da=d[a]if type(a)is str else 0;dz=d[z]if type(z)is str else 0;d[name]=da+dz if op=='*'else max(da,dz)
   groupweights=[sum(b['weights'][j]for j in g)for g in partition]
   expected=2*max([b['residual']]+groupweights)if anchor is None else groupweights[anchor]+2*max([b['residual']]+[w for j,w in enumerate(groupweights)if j!=anchor])
   cost=len(core)+n+3*m-1+2*k if not(m==0 and k==1 and anchor==0)else len(core)+n
   need(d[out]==expected==plan['degree_upper_bound']and len(rows)==cost==plan['operations'],'literal complete cost and guarded degree objective')
   cert=dict(operations=len(core)+n-k,M=cm+n-k,A=len(core)-cm,comparisons=m+k,witnesses=len(old['auxiliaries']))
   poly=dict(operations=M+A,M=M,A=A,witnesses=len(old['auxiliaries']),supplied_parameters=len(old['parameters']),all_gates_live=True,fixed_numeral_roles=11)
   record=dict(saved_parent_index=i,base=i%8,merged=i>=8,groups=k,partition=partition,anchor=anchor,group_degree_bounds=groupweights,degree_upper_bound=expected,exact_degree_claimed=False,certificate=cert,polynomial=poly,source_sha256=digest(rows))
   need(exact(record,ledger_by_key[i,k]),'every field of 240 complete source ledgers and hashes')
   counts['paid_gates']+=len(rows);counts['M']+=M;counts['A']+=A;counts['certificate_gates']+=cert['operations'];counts['comparison_ports']+=m+k
   counts['anchor_finalizers'if anchor is not None else'SOS_finalizers']+=1
   if i<8:planlist.append(plan)
   if (i,k)in selected:
    expected_saved=dict(record,source=rows,output=out,parameters=old['parameters'],auxiliaries=old['auxiliaries'],factors=factors,ordinary=ordinary,group_registers=groups,comparisons=ordinary+[[g,1]for g in groups])
    need(exact(selected[i,k],expected_saved),'every field of thirty literal full saved witnesses')
    counts['selected_paid_gates']+=len(rows);counts['selected_sources']+=1
    for case in range(2):
     v={s:Fraction(rng.randrange(-3,4),3)if case else rng.randrange(-3,4)for s in free+fixedports};nv=R.numeric(normal,v);ov=dict(v);ov['and__bound_beta']+=nv['factored_pack_Z']-nv['factored_pack_inner'];pv=R.numeric(oldnormal,ov)
     need(all(nv[name]==pv[name]for name,op,a,z in normal),'selected full scalar pullback')
     at=lambda x:nv[x]if type(x)is str else x
     sq=sum((at(a)-at(z))**2 for a,z in ordinary)+sum((nv[g]-1)**2 for j,g in enumerate(groups)if j!=anchor)
     need(nv[out]==(sq if anchor is None else nv[groups[anchor]]*(1+sq)-1),'selected full scalar finalizer')
     counts['numeric_cases']+=1;counts['rational_cases']+=case
   records.append(dict(index=i,groups=k,operations=M+A,M=M,A=A,certificate_operations=cert['operations'],comparisons=m+k,degree_upper=expected,source_sha256=digest(rows),finalizer_coefficient_sha256=fh))
  # Canonical identity follows separately at all original computed ports.
  ring=R.RingDAG();ne=ring.run(R.normal_rows(b['rows']),free+fixedports);pull=ring.add(ring.add(ring.val('and__bound_beta'),ne['factored_pack_Z']),ne['factored_pack_inner'],-1);oe=ring.run(R.normal_rows(old['source']),free+fixedports,{'and__bound_beta':pull})
  need(all(ne[name]==oe[name]for name,op,a,z in b['rows']),'whole original canonical source pullback');counts['canonical_register_identities']+=len(b['rows'])
 fronts={str(w):minfront(planlist,w)for w in (None,43,44)}
 need(exact(fronts,saved['frontiers']),'frontier readout of separately reviewed optimal plans')
 weighted=json.loads(dep['review_u9_tail_weighted_minima.json']);need(weighted['compared_author_pins']==AUTHOR,'same author packet in independent weighted proof')
 for a,b in zip(saved['searches'],weighted['searches']):
  need(a['base']==b['base']and a['weights']==b['weights'],'same actual source weights in independent optimization')
  need([(x['groups'],x['operations'],x['degree_upper_bound'])for x in a['best_by_group_count']]==[(x['groups'],x['operations'],x['degree_upper_bound'])for x in b['best_by_group_count']],'all120 separately certified weighted minima match current source schedules')
 wanted={(plan['base'],plan['groups'])for ff in fronts.values()for plan in ff}
 need(set(selected)=={(b['index'],k)for b in bases for base,k in wanted if b['index']%8==base},'all and only thirty frontier sources saved')
 # Old sources are explicitly an authenticated metadata union, not a replay.
 historical=json.loads(dep['neary_woods_universal_product_scale_partitions.json']);unchanged=[]
 for j,s in enumerate(historical['searches']):
  if 'and__'in s['positive_scale_prefixes']:continue
  for plan in s['best_by_group_count']:
   unchanged.append(dict(base=8+j,groups=len(plan['partition']),operations=plan['polynomial']['operations'],degree_upper_bound=plan['polynomial']['degree_upper_bound'],witnesses=plan['certificate']['witnesses'],provenance='frozen unchanged minimum',normalized=s['normalized_prefixes'],positive_scale=s['positive_scale_prefixes']))
 need(len({r['base']for r in unchanged})==8,'precise unchanged historical inventory')
 combined={str(w):minfront(planlist+unchanged,w)for w in (None,43,44,45)}
 need(exact(combined,saved['combined_with_eight_unchanged_historical_bases']),'exact metadata union with unchanged historical minima')
 need(counts['paid_gates']==counts['grouped_register_identities']==64918 and len(records)==240 and counts['selected_sources']==30,'independent full inventory totals')
 need(saved['audit_totals']==dict(canonical_register_pullbacks=4102,compiled_sources=240,complete_numeric_register_pullbacks=31040,full_finalizer_values=120,grouped_register_pullbacks=64918,paid_gates=64918,rational_values=30),'author evidence counters authenticated separately')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,prior_review_pins=REVIEW,dependency_pins=manifest,counts=dict(counts),records=records,frontiers=fronts,combined_frontiers=combined,scope='All240 recorded plans rebuilt from original source JSON, all30 selected complete sources byte-compared, every signed graph and formal finalizer proved. Source-guarded degree upper bounds only. Finite optimality inherited from separate weighted review; no optimizer/author/historical verifier executed. Eight historical bases used as authenticated metadata only.')

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--review-root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);args=a.parse_args();r=verify(args.root,args.artifacts,args.review_root)
 need(exact(r,json.loads(json.dumps(r))),'exact JSON type roundtrip')
 if args.expect:need(exact(r,json.loads(args.expect.read_bytes())),'exact saved independent receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'])))
if __name__=='__main__':main()
