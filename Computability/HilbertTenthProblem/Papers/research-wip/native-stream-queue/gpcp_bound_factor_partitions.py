"""Exact64-base GPCP factor family with a guarded signed-bound companion.

The geometry index unit must share a group with another enabled bound or
G. This gives a positive section onto the matching unconverted-bound
strong mask; different groupings need not have identical supplied zeros.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import gpcp_positive_bound_units767 as parent
import gpcp_shared_selectors774 as native

PREFIXES=('geo__','and__','hist__and__')
H=('and_X_bound_unit','history_X_bound_unit','geometry_X_bound_unit','geometry_index_bound_unit')
G='history_global_unit'
EXPECTED=[(767,228339),(768,154765),(769,153683),(770,9484),(771,7280),
          (772,6198),(773,6156),(774,5074),(775,4106),(776,3384),(777,3304),(782,3046)]
DATA=tuple(k for k in native.ACTIVE if k not in
           ('comparisons','unit_factors','unit_register','regroup','unit_product'))


def flags(inline_initial,ordinary_mask,and_bounds,geometry_bounds):
    assert all(type(v)is bool for v in (inline_initial,and_bounds,geometry_bounds))
    assert type(ordinary_mask)is int and 0<=ordinary_mask<8
    return inline_initial,ordinary_mask,and_bounds,geometry_bounds


def closure(rows,roots):
    nodes={n:(a,b) for n,o,a,b in rows};assert len(nodes)==len(rows)
    needed=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if isinstance(n,str) and n in nodes and n not in needed:
            needed.add(n);todo.extend(nodes[n])
    return [row for row in rows if row[0] in needed]


def dependency_contract(packet):
    rebuilt={p+n for p in PREFIXES for n in ('f','i','j','o','y_aux')}
    assert len(rebuilt)==15 and rebuilt<=set(packet['auxiliaries'])
    d={n:{n} for n in packet['parameters']+packet['auxiliaries']}
    at=lambda n:d[n] if isinstance(n,str) else set()
    for n,o,a,b in packet['source']:d[n]=at(a)|at(b)
    allowed={(p+'H17',p+'aux_u_rhs') for p in PREFIXES}
    allowed|={(p+'ic22',p+'R16') for i,p in enumerate(PREFIXES) if packet['ordinary_mask']>>i&1}
    for a,b in packet['ordinary_comparisons']:
        if (a,b) not in allowed:assert not (at(a)|at(b))&rebuilt
    for factor in packet['unit_factors']:
        if factor not in {p+n for p in PREFIXES for n in ('P17','f_square_minus_one')}:
            assert not at(factor)&rebuilt
    for p in PREFIXES:
        own={p+n for n in ('f','i','j','o','y_aux')}
        for n,o,a,b in packet['source']:
            if a in own or b in own:assert n.startswith(p)
        for n in ('P17','H17','aux_u_rhs'):assert not (at(p+n)&rebuilt)-own
        for n in ('R12','R10a','R10b','R11','R14','wn2','sn2'):assert not at(p+n)&rebuilt
    return dict(rebuilt_coordinates=sorted(rebuilt),local_linear_and_strong_exceptions=sorted(allowed),
                unchanged_main_outer_bound_checksum_global_dependencies=True)


def rewrite_base(old,ordinary_mask=0):
    flags(old.get('inline_initial'),ordinary_mask,old.get('and_bounds'),old.get('geometry_bounds'))
    assert old==parent.build(inline_initial=old['inline_initial'],and_bounds=old['and_bounds'],
                             geometry_bounds=old['geometry_bounds']),'complete canonical767 parent required'
    factors=list(old['unit_factors']);pairs=list(old['comparisons'][:-1])
    core=closure(old['source'],factors+[v for pair in pairs for v in pair]);initial_size=len(core)
    rows=list(core);by={n:(o,a,b) for n,o,a,b in rows}
    for bit,p in enumerate(PREFIXES):
        if not ordinary_mask>>bit&1:continue
        Q=p+'normalized_strong_Q';N=p+'f_square_minus_one';K=p+'R16';I=p+'ic22'
        assert by[Q]==('*',p+'A',I) and by[N]==('-',p+'L16',Q) and by[K]==('*',p+'A',Q)
        assert {n for n,o,a,b in rows if Q in (a,b)}=={N,K}
        assert N in factors and (I,K) not in pairs
        assert not ({Q}&native.leaves({k:old[k] for k in DATA}))
        change={N:('-',p+'L16',1),K:('*',p+'A',N)}
        rows=[(n,*change.get(n,(o,a,b))) for n,o,a,b in rows]
        factors.remove(N);pairs.append((I,K))
    rows=closure(rows,factors+[v for pair in pairs for v in pair])
    assert len(rows)==initial_size-ordinary_mask.bit_count()
    p={k:deepcopy(old[k]) for k in DATA}
    p.update(source=rows,factor_source=rows,unit_factors=factors,ordinary_comparisons=pairs,
             ordinary_mask=ordinary_mask,and_bounds=old['and_bounds'],geometry_bounds=old['geometry_bounds'],
             bound_unit_specs=deepcopy(old['bound_unit_specs']),history_packet=deepcopy(old['history_packet']),
             global_factor=G,distinguished_factor=H[3] if old['geometry_bounds'] else None,
             companion_factors=[f for f in factors if f in set(H[:3])|{G}] if old['geometry_bounds'] else [],
             normalized_strong_factors=[s+'f_square_minus_one' for i,s in enumerate(PREFIXES) if not ordinary_mask>>i&1],
             ordinary_strong_comparisons=[(s+'ic22',s+'R16') for i,s in enumerate(PREFIXES) if ordinary_mask>>i&1],
             witnesses=len(old['auxiliaries']),bound_factor_base=True,
             parent_source_sha256=hashlib.sha256(json.dumps(old['source'],separators=(',',':')).encode()).hexdigest(),
             projection='At fixed strong mask, admissible grouped zeros project surjectively onto the matching771 strong-mask zero set by explicit bound/global slack maps. Across masks only the outer projection outside15 local auxiliaries agrees.',
             identical_supplied_positive_zeros_between_partitions=False,
             cross_strong_same_tuple_claim=False)
    assert p['parameters'][0]=='x' and len(p['parameters'])==4
    p['strong_dependency_contract']=dependency_contract(p)
    # The current factor contract is rebuilt; no inherited normalized-core
    # or all-factors-positive flag is copied into the successor.
    return p


@lru_cache(None)
def _base(inline_initial,ordinary_mask,and_bounds,geometry_bounds):
    return rewrite_base(parent.build(inline_initial=inline_initial,and_bounds=and_bounds,
                                     geometry_bounds=geometry_bounds),ordinary_mask)


def base(*,inline_initial=True,ordinary_mask=0,and_bounds=True,geometry_bounds=True):
    key=flags(inline_initial,ordinary_mask,and_bounds,geometry_bounds)
    return deepcopy(_base(*key))


def _key(packet):
    return flags(*(packet[k] for k in ('inline_initial','ordinary_mask','and_bounds','geometry_bounds')))


def partition_contract(packet,partition,anchor):
    n=len(packet['unit_factors'])
    assert isinstance(partition,(list,tuple)) and partition
    assert all(isinstance(g,(list,tuple)) and g for g in partition)
    assert all(type(i)is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g)==list(range(n))
    assert anchor is None or type(anchor)is int and 0<=anchor<len(partition)
    if packet['distinguished_factor'] is not None:
        hi=packet['unit_factors'].index(packet['distinguished_factor'])
        buddies={packet['unit_factors'].index(f) for f in packet['companion_factors']}
        assert any(hi in g and buddies.intersection(g) for g in partition),'HI requires an enabled H or G companion in its group'
    return tuple(tuple(g) for g in partition),anchor


@lru_cache(None)
def _grouped(key,partition,anchor):
    p=deepcopy(_base(*key));partition,anchor=partition_contract(p,partition,anchor)
    rows=list(p['source']);products=[];names={n for n,o,a,b in rows}
    for j,group in enumerate(partition):
        value=p['unit_factors'][group[0]]
        for i,k in enumerate(group[1:]):
            name=f'gpcp_group_{j}_{i}';assert name not in names;names.add(name)
            rows.append((name,'*',value,p['unit_factors'][k]));value=name
        products.append(value)
    pairs=p['ordinary_comparisons']+[(value,1) for j,value in enumerate(products) if j!=anchor]
    comparisons=pairs if anchor is None else pairs+[(products[anchor],1)]
    ops=Counter(o for n,o,a,b in rows)
    p.update(source=rows,group_products=products,factor_partition=[list(g) for g in partition],
             partition_anchor=anchor,comparisons=comparisons,unit_register=None if anchor is None else products[anchor],
             operations=len(rows),multiplications=ops['*'],additions_subtractions=ops['+']+ops['-'],
             equations=len(comparisons),bound_factor_partition=True)
    return p


def grouped(original,partition,anchor):
    key=_key(original);assert original==_base(*key),'complete canonical factor base required'
    partition,anchor=partition_contract(original,partition,anchor)
    return deepcopy(_grouped(key,partition,anchor))


def checked(packet):
    key=_key(packet);partition,anchor=partition_contract(_base(*key),packet['factor_partition'],packet['partition_anchor'])
    assert packet==_grouped(key,partition,anchor),'complete canonical current factor plan required'


def _polynomial_source(packet):
    rows=list(packet['source']);pairs=packet['comparisons'] if packet['partition_anchor'] is None else packet['comparisons'][:-1]
    names={n for n,o,a,b in rows};acc=None
    def add(n,o,a,b):
        assert n not in names;names.add(n);rows.append((n,o,a,b));return n
    for i,(a,b) in enumerate(pairs):
        residual=add(f'gpcp_residual_{i}','-',a,b);square=add(f'gpcp_square_{i}','*',residual,residual)
        acc=square if acc is None else add(f'gpcp_sum_{i}','+',acc,square)
    assert acc is not None
    if packet['partition_anchor'] is None:return rows,acc
    positive=add('gpcp_positive','+',acc,1);product=add('gpcp_anchored','*',packet['unit_register'],positive)
    return rows,add('gpcp_output','-',product,1)


def polynomial_source(packet):
    checked(packet);return _polynomial_source(packet)


def _degrees(packet,rows=None):
    return native.raw_degrees(dict(packet,source=packet['source'] if rows is None else rows))


def highest_form_certificate(packet,rows,out,prime=1000000007):
    """An explicit nonzero evaluation certifies the symbolic highest forms."""
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    top={n:1+i%3 for i,n in enumerate(degrees)}
    for p in PREFIXES:top[p+'tau_gap']=top[p+'eta']=top[p+'zeta']=1
    d=lambda n:degrees[n] if isinstance(n,str) else 0
    t=lambda n:top[n] if isinstance(n,str) else n
    guarded=_degrees(packet,rows)
    for n,o,a,b in rows:
        da,db=d(a),d(b)
        if o=='*':degrees[n]=da+db;top[n]=t(a)*t(b)%prime
        else:
            degrees[n]=max(da,db);u=t(a) if da==degrees[n] else 0;v=t(b) if db==degrees[n] else 0
            top[n]=(u+v if o=='+' else u-v)%prime
        for p in PREFIXES:
            if n!=p+'R15':continue
            X,ac,g,a0,c,h=[p+v for v in ('wn2','cam2','gam','R12','R10a','a4m5')]
            high=d(ac)+d(g)
            assert high>max(2*d(X),d(X)+d(ac),d(X)+d(g),2*d(g),d(h)+2*d(c))
            degrees[n]=high;top[n]=2*t(ac)*t(g)%prime
    assert degrees==guarded and all(top[f] for f in packet['unit_factors'])
    residual=[(max(d(a),d(b)),((t(a) if d(a)>=d(b) else 0)-(t(b) if d(b)>=d(a) else 0))%prime) for a,b in packet['ordinary_comparisons']]
    maximum=max(v for v,c in residual)
    assert any(v==maximum and c for v,c in residual) and top[out]
    return dict(prime=prime,output_degree=degrees[out],output_leading_value=top[out],
                all_factor_highest_forms_nonzero=True,maximum_original_residual_nonzero=True)


def degree_audit(packet):
    checked(packet);rows,out=_polynomial_source(packet);degrees=_degrees(packet,rows)
    d=lambda n:degrees[n] if isinstance(n,str) else 0
    weights=[d(n) for n in packet['unit_factors']];r=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons'])
    groups=[sum(weights[i] for i in g) for g in packet['factor_partition']]
    assert groups==[d(n) for n in packet['group_products']]
    anchor=packet['partition_anchor']
    objective=2*max([r]+groups) if anchor is None else groups[anchor]+2*max([r]+[v for j,v in enumerate(groups) if j!=anchor])
    assert degrees[out]==objective
    certificate=highest_form_certificate(packet,rows,out)
    return dict(exact_degree=objective,factor_degrees=weights,maximum_original_residual_degree=r,
                group_degrees=groups,highest_form_certificate=certificate)


def ledger(packet):
    checked(packet);rows,out=_polynomial_source(packet);ops=Counter(o for n,o,a,b in rows)
    c,n,m,g=len(packet['factor_source']),len(packet['unit_factors']),len(packet['ordinary_comparisons']),len(packet['group_products'])
    assert len(rows)==c+n+3*m-1+2*g and len(closure(rows,[out]))==len(rows)
    return dict(inline_initial=packet['inline_initial'],ordinary_mask=packet['ordinary_mask'],
                and_bounds=packet['and_bounds'],geometry_bounds=packet['geometry_bounds'],
                partition=packet['factor_partition'],anchor=packet['partition_anchor'],
                core_operations=c,factors=n,ordinary_comparisons=m,
                certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=ops['*'],additions_subtractions=ops['+']+ops['-'],**degree_audit(packet)))


def optimal(weights,residual,distinguished=None,buddies=()):
 weights=tuple(weights);n=len(weights);size=1<<n;full=size-1
 assert n and all(type(w)is int and w>0 for w in weights)
 assert type(residual)is int and residual>=0
 hi=0 if distinguished is None else 1<<distinguished
 buddy=sum(1<<i for i in buddies)
 assert (not hi and not buddy) or (hi and buddy and not hi&buddy)
 sums=[0]*size;largest=[0]*size;count=[0]*size
 for m in range(1,size):
  bit=m&-m;j=bit.bit_length()-1;rest=m^bit
  sums[m]=sums[rest]+weights[j];largest[m]=max(largest[rest],weights[j]);count[m]=count[rest]+1
 def feasible(m,k):
  if k==0:return m==0
  if not m or k>count[m]:return False
  if m&hi:return bool(m&buddy) and k<count[m]
  return True
 def lower(m,k):
  if not m:return 0
  bound=max(largest[m],(sums[m]+k-1)//k)
  if m&hi:
   b=min(weights[i] for i in buddies if m>>i&1)
   bound=max(bound,weights[distinguished]+b)
  return bound
 visited=0
 @lru_cache(None)
 def sub(m,k):
  nonlocal visited
  assert feasible(m,k),(m,k)
  if k==0:return 0,()
  if k==1:return sums[m],(m,)
  if not m&hi and count[m]==k:return largest[m],tuple(1<<i for i in range(n) if m>>i&1)
  atoms=[1<<i for i in range(n) if m>>i&1]
  if m&hi:
   b=min((i for i in buddies if m>>i&1),key=lambda i:weights[i]);pair=hi|(1<<b)
   atoms=[a for a in atoms if not a&pair]+[pair]
  bins=[0]*k;total=[0]*k
  for atom in sorted(atoms,key=lambda a:(-sums[a],a)):
   j=min(range(k),key=lambda j:total[j]);bins[j]|=atom;total[j]+=sums[atom]
  best=max(total);chosen=tuple(sorted(bins));lb=lower(m,k)
  assert all(feasible(b,1) for b in bins)
  if best==lb:return best,chosen
  first=m&-m;s=m
  while s:
   rest=m^s
   if s&first and feasible(s,1) and feasible(rest,k-1) and sums[s]<best:
    visited+=1
    v,groups=sub(rest,k-1);value=max(sums[s],v)
    if value<best:
     best,chosen=value,tuple(sorted((s,)+groups))
     if best==lb:break
   s=(s-1)&m
  return best,chosen
 plans=[]
 for k in range(1,n+1-int(bool(hi))):
  peak,groups=sub(full,k);best=2*max(residual,peak);anchor=None
  for a in range(1,size):
   rest=full^a
   if not feasible(a,1) or not feasible(rest,k-1):continue
   lb=sums[a]+2*max(residual,lower(rest,k-1))
   if lb>=best:continue
   peak,others=sub(rest,k-1);v=sums[a]+2*max(residual,peak)
   if v<best:best,groups,anchor=v,(a,)+others,0
  partition=[[i for i in range(n) if g>>i&1] for g in groups]
  assert sorted(sum(partition,[]))==list(range(n)) and len(partition)==k
  ds=[sum(weights[i] for i in g) for g in partition]
  assert best==(2*max([residual]+ds) if anchor is None else ds[anchor]+2*max([residual]+[d for j,d in enumerate(ds) if j!=anchor]))
  assert not hi or any(distinguished in g and set(g)&set(buddies) for g in partition)
  plans.append(dict(groups=k,partition=partition,anchor=anchor,degree_upper_bound=best))
 return plans,dict(memoized_subproblems=sub.cache_info().currsize,subset_candidates=visited,mask_space=size,distinguished=distinguished,buddies=list(buddies))

def partitions(n):
 def go(j,parts):
  if j==n:yield [list(g) for g in parts];return
  for k in range(len(parts)):
   parts[k].append(j);yield from go(j+1,parts);parts[k].pop()
  parts.append([j]);yield from go(j+1,parts);parts.pop()
 yield from go(0,[])


def _floor(weights,residual,hi,buddies):
    n=len(weights);full=(1<<n)-1
    def legal(mask):return hi is None or not mask>>hi&1 or any(mask>>j&1 for j in buddies)
    def peak(mask):
        value=max([0]+[weights[j] for j in range(n) if mask>>j&1])
        if hi is not None and mask>>hi&1:
            value=max(value,weights[hi]+min(weights[j] for j in buddies if mask>>j&1))
        return value
    best=2*max(residual,peak(full));anchor=None;checked=0
    for mask in range(1,full+1):
        rest=full^mask
        if not legal(mask) or not legal(rest):continue
        checked+=1
        value=sum(weights[j] for j in range(n) if mask>>j&1)+2*max(residual,peak(rest))
        if value<best:best,anchor=value,mask
    return dict(exact_family_floor=best,anchor_mask=anchor,admissible_anchor_masks_checked=checked)


@lru_cache(None)
def _search(key):
    b=_base(*key);degrees=_degrees(b);weights=[degrees[f] for f in b['unit_factors']]
    d=lambda n:degrees[n] if isinstance(n,str) else 0
    residual=max(max(d(a),d(c)) for a,c in b['ordinary_comparisons'])
    hi=None if b['distinguished_factor'] is None else b['unit_factors'].index(b['distinguished_factor'])
    buddies=tuple(b['unit_factors'].index(f) for f in b['companion_factors'])
    plans,statistics=optimal(weights,residual,hi,buddies);records=[]
    for plan in plans:
        p=grouped(b,plan['partition'],plan['anchor']);rec=ledger(p)
        assert rec['polynomial']['exact_degree']==plan['degree_upper_bound']
        records.append(rec)
    floor=_floor(weights,residual,hi,buddies)
    assert min(r['polynomial']['exact_degree'] for r in records)==floor['exact_family_floor']
    floor['attained_operations']=min(r['polynomial']['operations'] for r in records if r['polynomial']['exact_degree']==floor['exact_family_floor'])
    return dict(inline_initial=key[0],ordinary_mask=key[1],and_bounds=key[2],geometry_bounds=key[3],
                factor_names=b['unit_factors'],weights=weights,residual=residual,
                search_statistics=statistics,best_by_group_count=records,floor_certificate=floor)


def search(*,inline_initial=True,ordinary_mask=0,and_bounds=True,geometry_bounds=True):
    return deepcopy(_search(flags(inline_initial,ordinary_mask,and_bounds,geometry_bounds)))


def _front(records):
    result=[];best=float('inf')
    for rec in sorted(records,key=lambda r:(r['polynomial']['operations'],r['polynomial']['exact_degree'])):
        if rec['polynomial']['exact_degree']<best:
            result.append(rec);best=rec['polynomial']['exact_degree']
    return result


@lru_cache(None)
def _frontier(inline_initial):
    return _front([r for inline in ((False,True) if inline_initial is None else (inline_initial,))
                   for mask in range(8) for ands in (False,True) for geo in (False,True)
                   for r in _search((inline,mask,ands,geo))['best_by_group_count']])


def frontier(inline_initial=None):
    assert inline_initial is None or type(inline_initial)is bool
    return deepcopy(_frontier(inline_initial))


def build(operations=782,*,inline_initial=None):
    rec=next(r for r in frontier(inline_initial) if r['polynomial']['operations']==operations)
    b=base(**{k:rec[k] for k in ('inline_initial','ordinary_mask','and_bounds','geometry_bounds')})
    return grouped(b,rec['partition'],rec['anchor'])


def execute(rows,values):
    env=dict(values)
    for n,o,a,b in rows:
        assert n not in env
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return env


def project_slacks(packet,values):
    """Formal integer map; positivity is a positive-zero theorem at fixed mask."""
    checked(packet);env=execute(packet['source'],values);result=dict(values)
    for _,name,lhs,rhs,beta in packet['bound_unit_specs']:result[beta]+=env[name]
    result[parent.parent.BETA]+=env[G]-1
    return result


def section_slacks(packet,values):
    """Positive section from the same-mask unconverted bound parent zeros."""
    checked(packet);signs={f:1 for f in [G]+[s[1] for s in packet['bound_unit_specs']]}
    if packet['distinguished_factor'] is not None:
        block=next(g for g in packet['factor_partition'] if packet['unit_factors'].index(H[3]) in g)
        buddy=next(packet['unit_factors'][i] for i in block if packet['unit_factors'][i] in packet['companion_factors'])
        signs[H[3]]=signs[buddy]=-1
    result=dict(values)
    for _,name,lhs,rhs,beta in packet['bound_unit_specs']:result[beta]-=signs[name]
    result[parent.parent.BETA]+=1-signs[G]
    return result


def _manual(packet,env):
    at=lambda n:env[n] if isinstance(n,str) else n
    groups=[prod(env[packet['unit_factors'][i]] for i in g) for g in packet['factor_partition']]
    anchor=packet['partition_anchor']
    residual=sum((at(a)-at(b))**2 for a,b in packet['ordinary_comparisons'])
    residual+=sum((v-1)**2 for j,v in enumerate(groups) if j!=anchor)
    return residual if anchor is None else groups[anchor]*(1+residual)-1


def source_audit(packet,cases=4,seed=767782):
    checked(packet);key=_key(packet);b=_base(*key);normal=_base(key[0],0,key[2],key[3]);old=_base(key[0],key[1],False,False)
    rows,out=_polynomial_source(packet);counts=Counter();rng=random.Random(seed)
    at=lambda e,n:e[n] if isinstance(n,str) else n
    def ungrouped(p,e):return prod(e[f] for f in p['unit_factors'])*(1+sum((at(e,a)-at(e,c))**2 for a,c in p['ordinary_comparisons']))-1
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-1,3) if signed else rng.randrange(1,3) for n in packet['parameters']+packet['auxiliaries']}
        if case==0:values.update({f'hist__Shat{i}':1 for i in range(57)});counts['zero_selector_cases']+=1
        env=execute(rows,values);assert env[out]==_manual(packet,env)
        counts['complete_grouped_manual_outputs']+=1;counts['signed_grouped_outputs']+=signed
        mapped=project_slacks(packet,values);past=execute(old['source'],mapped)
        altered={G,parent.parent.GLOBAL_PAIR[0]}|{s[2] for s in packet['bound_unit_specs']}
        assert all(env[n]==past[n] for n,o,a,c in old['source'] if n not in altered)
        assert past[G]==1
        for _,name,lhs,rhs,beta in packet['bound_unit_specs']:assert past[lhs]==past[rhs]
        multiplier=env[G]*prod(env[s[1]] for s in packet['bound_unit_specs'])
        assert ungrouped(b,env)+1==multiplier*(ungrouped(old,past)+1)
        counts['complete_fixed_mask_bound_projection_maps']+=1
        first=execute(normal['source'],values);lift=dict(values)
        for i,p in enumerate(PREFIXES):
            if key[1]>>i&1:lift[p+'i']=first[p+'A']*values[p+'i']
        second=execute(b['source'],lift);correction={}
        for i,p in enumerate(PREFIXES):
            if key[1]>>i&1:
                delta=first[p+'A'];N=first[p+'f_square_minus_one'];gap=first[p+'H17']**2-first[p+'y_aux']**2
                assert second[p+'ic22']-second[p+'R16']==delta*(1-N)
                correction[p+'P17']=first[p+'P17']+delta*(N-1)*gap
        assert all(second[f]==correction.get(f,first[f]) for f in b['unit_factors'])
        assert all(at(second,a)-at(second,c)==at(first,a)-at(first,c) for a,c in normal['ordinary_comparisons'])
        counts['complete_bound_core_strong_corrections']+=1
    return dict(counts)


def small_objective_audit():
    rng=random.Random(767);cases=enumerated=objectives=0
    for n in range(2,9):
        for mode in range(4):
            w=[rng.randrange(1,30) for _ in range(n)];r=rng.randrange(30)
            hi=None if mode==0 else rng.randrange(n)
            buddies=() if hi is None else tuple(i for i in range(n) if i!=hi and (mode==3 or i==(hi+1)%n or rng.randrange(2)))
            best={}
            for partition in partitions(n):
                if hi is not None and not any(hi in g and set(g)&set(buddies) for g in partition):continue
                enumerated+=1;ds=[sum(w[i] for i in g) for g in partition]
                candidates=[2*max([r]+ds)]+[d+2*max([r]+[v for j,v in enumerate(ds) if j!=a]) for a,d in enumerate(ds)]
                objectives+=len(candidates);k=len(partition);best[k]=min(best.get(k,float('inf')),*candidates)
            plans,_=optimal(w,r,hi,buddies)
            assert best=={p['groups']:p['degree_upper_bound'] for p in plans}
            cases+=1
    return dict(cases=cases,independently_enumerated_legal_partitions=enumerated,objectives=objectives)


def sign_section_audit():
    from itertools import product
    counts=Counter()
    for others in (1,3):
        hi=0;gindex=others+1;n=others+4;buddies=set(range(1,others+2))
        for p in partitions(n):
            block=next(g for g in p if hi in g);eligible=set(block)&buddies
            if not eligible:
                counts['excluded_gap_one_partitions']+=1;continue
            signs=[1]*n;signs[hi]=signs[min(eligible)]=-1
            assert all(prod(signs[i] for i in g)==1 for g in p)
            for gi,gx,beta in product((1,2,7),(2,15,127),(1,2,19)):
                old=[gi]+[gx]*others;new=[v-signs[i] for i,v in enumerate(old)]
                assert all(v>0 for v in new) and all(new[i]+signs[i]==v for i,v in enumerate(old))
                bg=beta+1-signs[gindex];assert bg>0 and bg+signs[gindex]-1==beta
                counts['positive_exact_sign_sections']+=1
            counts['admissible_partition_sign_products']+=1
    return dict(counts)


def guard_audit():
    total=0
    def reject(call):
        nonlocal total
        try:call()
        except (AssertionError,KeyError):total+=1
        else:raise AssertionError('malformed caller accepted')
    old=parent.build()
    for k,v in [('source',old['source'][:-1]),('parameters',[]),('unit_factors',[]),('bound_unit_specs',[]),('projection','wrong')]:
        reject(lambda k=k,v=v:rewrite_base(dict(old,**{k:v})))
    for key in [(1,0,True,True),(True,True,True,True),(True,8,True,True),(True,0,1,True),(True,0,True,0)]:
        reject(lambda key=key:base(**dict(zip(('inline_initial','ordinary_mask','and_bounds','geometry_bounds'),key))))
    b=base();n=len(b['unit_factors']);all_indices=list(range(n))
    for part,anchor in [([[0]],None),([[]],0),([all_indices],True),([all_indices],1),([list(range(n-1))+[True]],None),([[i] for i in range(n)],None)]:
        reject(lambda part=part,anchor=anchor:grouped(b,part,anchor))
    reject(lambda:grouped(dict(b,companion_factors=[]),[all_indices],0))
    p=grouped(b,[all_indices],0)
    for k,v in [('source',p['source'][:-1]),('ordinary_comparisons',[]),('projection','wrong'),('strong_dependency_contract',{}),('unit_register','bad')]:
        for api in (polynomial_source,degree_audit,project_slacks,section_slacks):
            if api in (project_slacks,section_slacks):reject(lambda k=k,v=v,api=api:api(dict(p,**{k:v}),{}))
            else:reject(lambda k=k,v=v,api=api:api(dict(p,**{k:v})))
    return total


def verify():
    studies=[];audits=Counter()
    for inline in (False,True):
        for mask in range(8):
            for ands in (False,True):
                for geo in (False,True):
                    key=(inline,mask,ands,geo);study=deepcopy(_search(key));studies.append(study)
                    b=_base(*key);one=grouped(b,[list(range(len(b['unit_factors'])))],0)
                    # One complete output/map fixture per strong/bound/interface
                    # base, in both positive and signed source domains.
                    audits.update(source_audit(one,4,767000+len(studies)))
    fronts={str(i):_frontier(i) for i in (None,False,True)}
    assert [(r['polynomial']['operations'],r['polynomial']['exact_degree']) for r in fronts['None']]==EXPECTED
    assert min(s['floor_certificate']['exact_family_floor'] for s in studies if s['inline_initial'])==101326
    assert min(s['floor_certificate']['exact_family_floor'] for s in studies if not s['inline_initial'])==3046
    selected=[];seen=set()
    for records in fronts.values():
        for rec in records:
            key=(rec['inline_initial'],rec['ordinary_mask'],rec['and_bounds'],rec['geometry_bounds'])
            token=(key,tuple(map(tuple,rec['partition'])),rec['anchor'])
            if token in seen:continue
            seen.add(token);p=grouped(_base(*key),rec['partition'],rec['anchor']);rows,out=polynomial_source(p)
            example=ledger(p);example.update(source=rows,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                                            comparisons=p['comparisons'],audit=source_audit(p,8,782000+len(selected)))
            selected.append(example)
    return dict(status='PASS_GPCP_BOUND_FACTOR_PARTITIONS',studies=studies,frontiers=fronts,
                optimal_literal_ledgers=sum(len(s['best_by_group_count']) for s in studies),selected_sources=selected,
                full_base_audits=dict(audits),small_objective_audit=small_objective_audit(),
                sign_sections=sign_section_audit(),rejected_callers=guard_audit(),
                scope='Exactly64 current767-based interfaces/strong masks/paired bounds; all partitions with HI sharing a group with an enabled otherH orG. Exact formal-polynomial degrees and finite objective, not an all-circuit optimum. At fixed strong mask, explicit positive slack projections/sections; across strong masks only the outer projection outside15 auxiliaries agrees. Different grouped supplied zero sets may differ; no full compiled Pell zero is materialized.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert result==json.loads(path.read_text()),'receipt mismatch'
    print(result['status']);print(EXPECTED);print('LEDGERS',result['optimal_literal_ledgers'],'SELECTED',len(result['selected_sources']));print(result['full_base_audits'])
