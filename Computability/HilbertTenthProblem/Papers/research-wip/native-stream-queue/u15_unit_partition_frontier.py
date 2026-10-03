"""Exact finite partition/finalizer frontier for the complete ordinary U15 source.

Enumerates all 877 partitions of six protected norms and one checksum,
with all 4140 SOS/single-anchor schedules. This is a finite-family optimum, not a global
arithmetic lower bound. Complete supplied integer zero sets are unchanged.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import random

PINS={
 'u15_packed_composed_units511.py':'234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38',
 'u15_packed_unit_product524.py':'667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611',
}
WEIGHTS=(12,78,332,726,898,834,65)
DEFAULT_GROUPS=((0,1,2,6),(3,),(4,),(5,))
PRIMES=(1000000007,1000000009)


def require(ok,message):
    if not ok:raise ValueError(message)


def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def _key(groups,anchor):
    require(type(groups) is list and groups,'Groups must be a nonempty exact list')
    require(all(type(g) is list and g and all(type(i) is int for i in g) for g in groups),'Groups require exact lists of exact integers')
    require(all(g==sorted(g) and len(set(g))==len(g) for g in groups),'Group indices must strictly increase')
    require(sorted(i for g in groups for i in g)==list(range(7)),'Partition must contain every factor exactly once')
    require([g[0] for g in groups]==sorted(g[0] for g in groups),'Canonical first-element group order required')
    require(anchor is None or type(anchor) is int and 0<=anchor<len(groups),'Anchor must be None or an exact group index')
    return tuple(tuple(g) for g in groups),anchor


def partitions(n=7):
    require(type(n) is int and 0<=n<=7,'Exact partition size 0 through 7 required')
    if n==0:yield [];return
    for p in partitions(n-1):
        for i in range(len(p)):yield p[:i]+[p[i]+[n-1]]+p[i+1:]
        yield p+[[n-1]]


def _paths(root):
    here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve();paths=[]
    for name,wanted in PINS.items():
        path=here/name if (here/name).is_file() else root/name
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==wanted,'Pinned source changed or missing: '+name);paths.append(path)
    return root,paths


def _load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


@lru_cache(None)
def _bundle(root_text,*path_texts):
    root,paths=_paths(root_text);require(tuple(map(str,paths))==path_texts,'Dependency path changed')
    parent,unit=[_load(p,'_partition_'+str(i)) for i,p in enumerate(paths)]
    old=parent.build(True,grouped=False,root=root);parent.checked(old,root=root)
    grouped=unit.rewrite(old,finalizer='sos');unit._validate_degree_packet(grouped)
    require(old['ledger']['polynomial']==dict(operations=523,M=211,A=312),'Wrong ungrouped source')
    require(len(grouped['unit_factors'])==7,'Expected seven factors')
    tail=grouped['source'][-6:]
    product=grouped['unit_factors'][0]['factor'];expected=[]
    for i,m in enumerate(grouped['unit_factors'][1:],1):
        n='unit_product'+str(i);expected.append((n,'*',product,m['factor']));product=n
    require(exact(tail,expected),'Unexpected unit product schedule')
    base=deepcopy(grouped);base['source']=base['source'][:-6];base['comparisons']=base['comparisons'][:-1]
    require(len(base['source'])==431 and len(base['comparisons'])==24,'Unexpected base dimensions')
    for key in ('unit_product_register','finalizer','finalizer_requested','polynomial_source','output','ledger','loader_comparison_count','grouped_units','composition'):
        base.pop(key,None)
    base['pre_partition_loader_comparison_count']=old['loader_comparison_count']
    base['canonical_parent']={'file':next(iter(PINS)),'sha256':PINS[next(iter(PINS))],'ordinary':True,'grouped':False}
    base['source_lineage']=dict(base['source_lineage'],**PINS)
    base['unit_incoming_packet_digest']=unit.digest(old)
    return dict(parent=parent,unit=unit,old=old,base=base)


def _context(root=None):
    root,paths=_paths(root);b=_bundle(str(root),*map(str,paths));b['parent']._context(root);return root,b


def _emit(b,groups,anchor):
    unit=b['unit'];p=deepcopy(b['base']);rows=p['source'];pairs=p['comparisons'];products=[];mapping=[]
    for j,g in enumerate(groups):
        product=p['unit_factors'][g[0]]['factor']
        for k,index in enumerate(g[1:],1):
            n=f'partition_product{j}_{k}';rows.append((n,'*',product,p['unit_factors'][index]['factor']));product=n
        products.append(product);mapping.append(dict(group_index=j,factor_indices=list(g),register=product,new_comparison_index=len(pairs),weight=sum(WEIGHTS[i] for i in g)))
        pairs.append((product,1))
    if anchor is None:full,out=unit._sos(rows,pairs)
    else:
        full=list(rows);acc=1
        for j,(a,c) in enumerate(pairs):
            if j==24+anchor:continue
            r=f'partition_res{j}';s=f'partition_sq{j}';n=f'partition_anchor{j}'
            full.extend([(r,'-',a,c),(s,'*',r,r),(n,'+',acc,s)]);acc=n
        full.extend([('partition_times_anchor','*',products[anchor],acc),('partition_polynomial','-','partition_times_anchor',1)]);out='partition_polynomial'
    unit._source_check(full,p['parameters'],p['auxiliaries']);live={out}
    for n,op,a,c in reversed(full):
        if n in live:live.update(v for v in (a,c) if type(v) is str)
    require(all(n in live for n,op,a,c in full),'Dead partition gate')
    upper,_=unit._degrees(p,full,out);g=len(groups)
    p.update(kind='ordinary_u15_unit_partition',groups=[list(x) for x in groups],anchor=anchor,unit_group_map=mapping,
      current_comparison_counts=dict(retained_loader=15,retained_history=9,unit_groups=g,total=24+g),
      comparisons=pairs,polynomial_source=full,output=out,
      ledger=dict(certificate=unit._count(rows),polynomial=unit._count(full),equations=len(pairs),positive_witnesses=len(p['auxiliaries']),formal_degree_upper_bound=upper,exact_degree_claimed=False),
      full_polynomial_identity=(g==7 and anchor is None),
      parent_relation=('Identical complete polynomial on all supplied integer tuples; unchanged positive coordinates.' if g==7 and anchor is None
                       else 'Exactly the same full supplied integer zero set; unchanged positive coordinates; complete off-zero correction recorded.'),
      scope='Complete ordinary valid-program first-halt relation inherited from the pinned source; finite partition/finalizer frontier only, no global arithmetic lower bound.')
    require(p['ledger']['polynomial']==dict(operations=509+2*g,M=211,A=298+2*g),'Wrong paid partition ledger')
    return p


def build(groups=None,*,anchor=None,root=None):
    groups=[list(g) for g in DEFAULT_GROUPS] if groups is None else groups
    key,anchor=_key(groups,anchor);return _emit(_context(root)[1],key,anchor)


def canonical_parent(*,root=None):return deepcopy(_context(root)[1]['old'])


def checked(p,*,root=None):
    require(type(p) is dict,'Complete canonical packet required');groups,anchor=_key(p.get('groups'),p.get('anchor'))
    require(exact(p,_emit(_context(root)[1],groups,anchor)),'Noncanonical partition packet');return p


def polynomial_source(p,*,root=None):return deepcopy(checked(p,root=root)['polynomial_source'])


def _degree(p):
    certs=[];main={m['factor']:m['prefix'] for m in p['unit_factors'] if m['kind']=='main'}
    factors={m['factor'] for m in p['unit_factors']}
    for prime in PRIMES:
        env={n:(0 if n in p['fixed_parameters'] else 1,(i%7)+1,{n} if n in p['fixed_parameters'] else set()) for i,n in enumerate(p['parameters']+p['auxiliaries'])}
        def val(x):return env[x] if type(x) is str else (0,x%prime,set())
        def mul(x,y):return (x[0]+y[0],x[1]*y[1]%prime,x[2]|y[2])
        def add(x,y,sign=1):
            d=max(x[0],y[0]);return (d,((x[1] if x[0]==d else 0)+sign*(y[1] if y[0]==d else 0))%prime,(x[2] if x[0]==d else set())|(y[2] if y[0]==d else set()))
        factor_degrees={}
        for n,op,a,c in p['polynomial_source']:
            if n in main:
                pref=main[n];A=val(pref+'R12');C=val(pref+'R10a');H=val(pref+'a4m5');V=add(val(pref+'wn2'),mul(val(pref+'ga'),H))
                env[n]=add(add(mul(val(2),mul(mul(A,C),V)),mul(V,V)),mul(H,mul(C,C)),-1)
            else:env[n]=mul(val(a),val(c)) if op=='*' else add(val(a),val(c),1 if op=='+' else -1)
            if n in factors:
                require(env[n][1] and not env[n][2],'Factor degree certificate failed');factor_degrees[n]=env[n][0]
        require(tuple(factor_degrees[m['factor']] for m in p['unit_factors'])==WEIGHTS,'Actual factor degree changed')
        d,c,deps=env[p['output']];require(c and not deps,'Complete top coefficient vanished or depends on fixed numerals')
        certs.append(dict(prime=prime,degree=d,leading_coefficient=c,fixed_parameter_dependencies=[],factor_degrees=factor_degrees))
    sums=[sum(WEIGHTS[i] for i in g) for g in p['groups']];a=p['anchor']
    expected=max(1936,2*max(sums)) if a is None else sums[a]+max([1936]+[2*s for i,s in enumerate(sums) if i!=a])
    require(all(c['degree']==expected for c in certs),'Exact degree differs from finite objective')
    return dict(exact_degree=expected,certificates=certs,group_weights=sums,
      guarded_source_identity='(a*c+X+ga*H)^2-(a^2+H)*c^2=2*a*c*(X+ga*H)+(X+ga*H)^2-H*c^2; H=4*a+3')


def degree_audit(p,*,root=None):return _degree(checked(p,root=root))


def evaluate(p,values,*,signed=False,root=None):
    p=checked(p,root=root);b=_context(root)[1];v=b['unit']._assignment(p,values,signed)
    return b['unit'].execute(p['polynomial_source'],v)[p['output']]


def _identity(b,p,v):
    unit=b['unit'];old=b['old'];before=unit.execute(old['polynomial_source'],v);after=unit.execute(p['polynomial_source'],v)
    rr=[unit.at(before,a)-unit.at(before,c) for a,c in old['comparisons']];retained=0;factors=[]
    for m in p['unit_factors']:
        f=1+m['residual_sign']*rr[m['old_index']];require(f==after[m['factor']],'Factor residual identity failed')
        if m['kind']!='checksum':require(f%4!=3,'Protected factor sign exclusion failed')
        factors.append(f)
    for m in p['unit_retained_comparison_map']:
        a,c=p['comparisons'][m['new_index']];require(unit.at(after,a)-unit.at(after,c)==rr[m['old_index']],'Retained residual changed');retained+=rr[m['old_index']]**2
    products=[]
    for m in p['unit_group_map']:
        t=1
        for i in m['factor_indices']:t*=factors[i]
        require(t==after[m['register']],'Group product differs');products.append(t)
    a=p['anchor'];expected=retained+sum((t-1)**2 for t in products) if a is None else products[a]*(1+retained+sum((t-1)**2 for j,t in enumerate(products) if j!=a))-1
    require(before[old['output']]==sum(r*r for r in rr) and after[p['output']]==expected,'Complete output identity failed')
    require((before[old['output']]==0)==(expected==0),'Integer zero equality failed')
    if p['full_polynomial_identity']:require(before[old['output']]==expected,'Singleton SOS identity failed')
    return dict(parent_output=before[old['output']],child_output=expected,group_products=products,retained_square_sum=retained)


def identity(p,values,*,signed=False,root=None):
    p=checked(p,root=root);b=_context(root)[1];return _identity(b,p,b['unit']._assignment(p,values,signed))


def verify(root=None):
    b=_context(root)[1];counts=Counter();records=[];best={};allpart=list(partitions());require(len(allpart)==877,'Wrong partition count')
    rng=random.Random(5171936)
    for groups in allpart:
        key,_=_key(groups,None);counts['partitions']+=1
        for anchor in [None]+list(range(len(groups))):
            p=_emit(b,key,anchor);degree=_degree(p);cost=p['ledger']['polynomial']['operations'];d=degree['exact_degree'];g=len(groups)
            record=dict(groups=groups,anchor=anchor,operations=cost,degree=d,ledger=p['ledger'],source_sha256=b['unit'].digest(p['polynomial_source']),degree_certificates=degree['certificates'])
            records.append(record);counts['complete_schedules']+=1;counts['leading_certificates']+=2
            opt=(g,anchor is not None)
            if opt not in best or d<best[opt]['degree']:best[opt]=record
            # One deterministic signed full-source identity for every emitted form.
            v={n:rng.randrange(-2,3) for n in p['parameters']+p['auxiliaries']};_identity(b,p,v)
            counts['signed_complete_output_identities']+=1;counts['parent_residual_checks']+=31
    require(counts['complete_schedules']==4140,'Wrong complete schedule census')
    points=sorted(set((r['operations'],r['degree']) for r in records))
    pareto=[x for x in points if not any(y!=x and y[0]<=x[0] and y[1]<=x[1] for y in points)]
    require(pareto==[(511,4881),(513,3120),(515,2116),(517,1936)],'Unexpected finite Pareto frontier')
    frontier=[]
    def reject(fn):
        try:fn()
        except (ValueError,TypeError,KeyError):counts['malformed_calls_rejected']+=1;return
        raise AssertionError('Malformed call accepted')
    for cost,d in pareto:
        r=next(r for r in records if (r['operations'],r['degree'])==(cost,d));p=build(r['groups'],anchor=r['anchor'],root=root)
        for case in range(16):
            signed=case>=8;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
            identity(p,v,signed=signed,root=root);counts['public_output_identities']+=1
        for field in ('source','polynomial_source','comparisons','groups','unit_factors','unit_group_map','unit_retained_comparison_map','ledger'):
            q=deepcopy(p);q[field]=None;reject(lambda q=q:checked(q,root=root));reject(lambda q=q:degree_audit(q,root=root))
        for field in ('unit_native__main','native__R14'):
            q=deepcopy(p);i=next(i for i,row in enumerate(q['source']) if row[0]==field);row=q['source'][i];q['source'][i]=(field,'*',row[2],row[3]);reject(lambda q=q:degree_audit(q,root=root))
        v={n:1 for n in p['parameters']+p['auxiliaries']}
        for n in v:
            for bad in (True,1.0,None):
                q=dict(v);q[n]=bad;reject(lambda q=q:evaluate(p,q,root=root))
        for bad in (0,1,1.0,None):reject(lambda bad=bad:evaluate(p,v,signed=bad,root=root))
        clone=build(r['groups'],anchor=r['anchor'],root=root);clone['source'].clear();require(exact(build(r['groups'],anchor=r['anchor'],root=root),p),'Build cache leaked');counts['copy_checks']+=1
        clone=canonical_parent(root=root);clone['source'].clear();require(exact(canonical_parent(root=root),b['old']),'Parent cache leaked');counts['copy_checks']+=1
        frontier.append(dict(compiler=p,degree=degree_audit(p,root=root)))
    for groups in ((),[],[[0,1,2,3,4,5]],[[0,1,2,3,4,5,6,6]],[[1],[0,2,3,4,5,6]],[[False,1,2,3,4,5,6]],[[0.0,1,2,3,4,5,6]]):reject(lambda groups=groups:build(groups,root=root))
    for a in (True,False,0.0,-1,7,'0'):reject(lambda a=a:build(anchor=a,root=root))
    return dict(status='PASS_U15_PARTITION_FRONTIER',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dependency_pins=PINS,
      counts=dict(counts),factor_weights=list(WEIGHTS),retained_sos_degree=1936,pareto=[dict(operations=c,exact_degree=d) for c,d in pareto],
      per_group_mode_minima=[best[k] for k in sorted(best)],forms=records,frontier_compilers=frontier,
      scope='All 877 partitions and all 4140 SOS/single-anchor schedules in this fixed seven-factor source family, each actual complete source counted and exact degree certified; not a global lower bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path);parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify(args.root)));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:require(exact(result,json.loads(path.read_text())),'Saved receipt differs')
    print(json.dumps({k:result[k] for k in ('status','counts','pareto')},indent=2))
