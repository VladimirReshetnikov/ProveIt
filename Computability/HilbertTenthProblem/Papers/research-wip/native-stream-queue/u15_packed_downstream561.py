"""Complete U15 downstream arithmetic: raw363 / ordinary561.

Four reused power gates, factor-two tape equations, and fifteen positive
loader graph definitions. This is a zero-set bijection, not equality of
the full polynomials on an unchanged supplied tuple.
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
import subprocess
import sys

PARENT_FILE='u15_packed_centered_states611.py'
PARENT_SHA256='3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce'
PACKET_PINS={False: '3dfcd65c18e3dc74fb011a6712f34e4588baeb328a19a47f1a58e6643c7f2512', True: '4b824198e8fda2363343ea83a0e8bcb5de1f48efc19b930e71ed5e7d8e0939d9'}
DEFINITIONS={
 'input__q':'input__input_bound',
 'input__J':'input__geo__geometry_index_bound',
 'input__P':'input__repunit_P',
 'input__Ahat':'input__restored_Ahat',
 **{'input__geo__'+x:'input__geo__'+y for x,y in dict(a='R12',c='R10a',d='R14',k='R10b',s='geometry_odd').items()},
 **{'input__and__'+x:'input__and__'+y for x,y in dict(a='R12',c='R10a',d='R14',k='R10b',r='bs_packed',s='bs_odd').items()}}
EXTRA_PAIRS=(('input__repunit_P','input__P'),('input__input_bound','input__q'),
 ('input__congruence_left','input__congruence_right'),('input__geo__geometry_index_bound','input__J'))


def require(ok,message):
    if not ok:raise ValueError(message)


def flag(v,name):
    require(type(v) is bool,name+' must be an exact Boolean');return v


def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def typed(x):
    if type(x) is dict:
        require(all(type(k) is str for k in x),'String keys required')
        return ['dict',[[k,typed(x[k])] for k in sorted(x)]]
    if type(x) in (tuple,list):return [type(x).__name__,[typed(v) for v in x]]
    require(type(x) in (int,bool,str,type(None)),'Unsupported descriptor type')
    return [type(x).__name__,x]


def digest(x):return hashlib.sha256(json.dumps(typed(x),separators=(',',':')).encode()).hexdigest()


def _paths(root):
    here=Path(__file__).resolve().parent
    root=here if root is None else Path(root).resolve()
    path=here/PARENT_FILE if (here/PARENT_FILE).is_file() else root/PARENT_FILE
    require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA256,'Pinned611 source changed or missing')
    return root,path


def _load(path):
    spec=importlib.util.spec_from_file_location('_downstream561_parent',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod


def execute(rows,values):
    env=dict(values)
    for n,op,a,b in rows:
        x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
        env[n]=x+y if op=='+' else x-y if op=='-' else x*y
    return env


def at(env,x):return env[x] if type(x) is str else x


def _sort(rows,inputs):
    known=set(inputs);out=[]
    require(len({n for n,_,_,_ in rows})==len(rows),'Duplicate register')
    while rows:
        ready=[]
        for row in rows:
            n,op,a,b=row
            if all(type(v) is int or type(v) is str and v in known for v in (a,b)):
                require(n not in known and op in ('+','-','*'),'Bad source row')
                out.append(row);known.add(n);ready.append(row)
        require(bool(ready),'Cyclic or dangling graph definition')
        rows=[r for r in rows if r not in ready]
    return out


def _finish(p):
    rows=list(p['source']);squares=[]
    for i,(a,b) in enumerate(p['comparisons']):
        n=f'poly_res{i}';s=f'poly_sq{i}'
        rows.extend([(n,'-',a,b),(s,'*',n,n)]);squares.append(s)
    out=squares[0]
    for i,s in enumerate(squares[1:],1):
        name=f'poly_sum{i}';rows.append((name,'+',out,s));out=name
    known=set(p['parameters']+p['auxiliaries'])
    degree={n:0 if n in p['fixed_parameters'] else 1 for n in known}
    for n,op,a,b in rows:
        require(n not in known and all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Bad emitted source')
        da=degree[a] if type(a) is str else 0;db=degree[b] if type(b) is str else 0
        degree[n]=da+db if op=='*' else max(da,db);known.add(n)
    needed={out}
    for n,op,a,b in reversed(rows):
        if n in needed:needed.update(v for v in (a,b) if type(v) is str)
    require(all(n in needed for n,_,_,_ in rows),'Dead emitted gate')
    count=lambda rr:dict(operations=len(rr),M=sum(op=='*' for _,op,_,_ in rr),A=sum(op!='*' for _,op,_,_ in rr))
    p.update(polynomial_source=rows,output=out,ledger=dict(certificate=count(p['source']),polynomial=count(rows),
        equations=len(p['comparisons']),positive_witnesses=len(p['auxiliaries']),formal_degree_upper_bound=degree[out],exact_degree_claimed=False))
    return p


def _rewrite(old):
    p=deepcopy(old);ordinary=p['ordinary'];defs=dict(DEFINITIONS) if ordinary else {}
    original_rows={n:(op,a,b) for n,op,a,b in old['source']}
    expected={'v253':('*','v170','v170'),'v254':('*','v253','v34'),
      'v264':('*','v253','v253'),'v265':('*','v264','v264'),'v266':('*','v265','v34'),
      'v267':('*','v266','v266'),'v136':('*','v135',2),'v147':('*','v146',2),
      'v143':('*','v142','v31'),'v152':('*','v151','v31'),'v31':('*','v30',64)}
    require(all(original_rows[n]==v for n,v in expected.items()),'Frozen downstream rows changed')
    if ordinary:
        expected_loader={'input__quotient_product':('*','input__modulus','input__quotient_hat'),
          'input__congruence_left':('+','input__Ahat','input__Q'),
          'input__congruence_right0':('+','input__quotient_product','input__z'),
          'input__congruence_right':('+','input__congruence_right0',2)}
        require(all(original_rows[n]==v for n,v in expected_loader.items()),'Frozen congruence changed')
    replace=lambda v:defs.get(v,v) if type(v) is str else v
    rows=[]
    for n,op,a,b in old['source']:
        if n in ('v253','v264','v265','v266','v136','v147','input__congruence_left'):continue
        if n=='v254':a,b='v181','v170'
        if n=='v267':a,b='v192','v184'
        if n=='v143':rows.append(('tape_half_B','*',32,'v30'));a,b='tape_half_B','v142'
        if n=='v152':a,b='tape_half_B','v151'
        if n=='input__quotient_product':
            rows.append(('input__quotient_minus_one','-','input__quotient_hat',1));b='input__quotient_minus_one'
        if n=='input__congruence_right':n='input__restored_Ahat';b=1
        rows.append((n,op,replace(a),replace(b)))
    removed=set(tuple(x) for x in defs.items())|set(EXTRA_PAIRS if ordinary else ())
    pairs=[];mapping=[]
    for i,pair in enumerate(old['comparisons']):
        pair=tuple(pair)
        if pair in removed:
            mapping.append(dict(old_index=i,new_index=None,kind='deleted_definition',old_pair=pair));continue
        child=tuple({'v136':'v135','v147':'v146'}.get(replace(z),replace(z)) for z in pair)
        mapping.append(dict(old_index=i,new_index=len(pairs),kind='retained',factor=2 if pair[0] in ('v136','v147') else 1,old_pair=pair,child_pair=child))
        pairs.append(child)
    require(sum(m['new_index'] is None for m in mapping)==len(defs),'Definition count changed')
    p['auxiliaries']=[n for n in old['auxiliaries'] if n not in defs]
    p['source']=_sort(rows,p['parameters']+p['auxiliaries']);p['comparisons']=pairs
    if ordinary:p['loader_comparison_count']=old['loader_comparison_count']-len(defs)
    p.update(kind='downstream_power_tape_loader_projection',computed_loader_fields=defs,comparison_map=mapping,
      power_chain_identity={'v254':5,'v267':34},tape_residual_factor=2,
      canonical_parent={'file':PARENT_FILE,'sha256':PARENT_SHA256},
      source_lineage=dict(p['source_lineage'],**{PARENT_FILE:PARENT_SHA256}),
      parent_relation='Positive zero-set bijection via fifteen ordinary loader graph definitions; raw identity map. Parent SOS on restoration graph = child SOS +3 times the two child tape-residual squares.',
      scope='Complete fixed-arity ordinary valid-program first-halt relation inherited from611; all supplied-coordinate domains retained for nonremoved fields; no new87 bound.')
    return _finish(p)


def _power_form(packet,name):
    rows={n:(op,a,b) for n,op,a,b in packet['source']};memo={}
    def get(v):
        if type(v) is int:return {0:v} if v else {}
        if v==packet['registers']['P']:return {1:1}
        if v in memo:return memo[v]
        require(v in rows,'Power is not a polynomial in P')
        op,a,b=rows[v];a,b=get(a),get(b);r={}
        if op=='*':
            for i,c in a.items():
                for j,d in b.items():r[i+j]=r.get(i+j,0)+c*d
        else:
            r=dict(a)
            for i,c in b.items():r[i]=r.get(i,0)+(c if op=='+' else -c)
        memo[v]={i:c for i,c in r.items() if c};return memo[v]
    return get(name)


def _certificate(old,new):
    require(old['parameters']==new['parameters'] and old['fixed_parameters']==new['fixed_parameters'],'External input changed')
    for n,e in new['power_chain_identity'].items():
        require(_power_form(old,n)==_power_form(new,n)=={e:1},'Power identity failed')
    nodes={}
    def intern(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def opnode(op,a,b):
        if op in ('+','*') and b<a:a,b=b,a
        return intern((op,a,b))
    rows={n:(op,a,b) for n,op,a,b in new['source']};memo={}
    def get(v):
        if type(v) is int:return intern(('constant',v))
        if v in memo:return memo[v]
        if v not in rows:return intern(('variable',v))
        if v in new['power_chain_identity']:
            result=intern(('power',new['power_chain_identity'][v],get(new['registers']['P'])))
        else:
            op,a,b=rows[v];result=opnode(op,get(a),get(b))
        memo[v]=result;return result
    oldrows={n:(op,a,b) for n,op,a,b in old['source']};oldmemo={};defs=new['computed_loader_fields']
    def prior(v):
        if type(v) is int:return intern(('constant',v))
        if v in defs:return get(defs[v])
        if v in oldmemo:return oldmemo[v]
        if v not in oldrows:return intern(('variable',v))
        if v in new['power_chain_identity']:
            result=intern(('power',new['power_chain_identity'][v],prior(old['registers']['P'])))
        else:
            op,a,b=oldrows[v];result=opnode(op,prior(a),prior(b))
        oldmemo[v]=result;return result
    direct=deleted=scaled=affine=0
    for m in new['comparison_map']:
        a,b=m['old_pair']
        if m['new_index'] is None:
            if (a,b)==('input__congruence_left','input__congruence_right'):
                # Independently checked literal source: (Q-1)(h-1)+z+1+Q=(Q-1)h+z+2.
                require(rows['input__modulus']==('-', 'input__Q',1),'Wrong modulus')
                require(rows['input__quotient_minus_one']==('-', 'input__quotient_hat',1),'Wrong quotient shift')
                require(rows['input__quotient_product']==('*','input__modulus','input__quotient_minus_one'),'Wrong reconstructed product')
                require(rows['input__restored_Ahat']==('+','input__congruence_right0',1),'Wrong restored output')
                require(rows['input__congruence_right0']==('+','input__quotient_product','input__z'),'Wrong output addend')
                affine+=1
            else:require(prior(a)==prior(b),'A deleted definition is nonzero on graph');deleted+=1
        elif m['factor']==1:
            x,y=m['child_pair'];require((prior(a),prior(b))==(get(x),get(y)),'Changed retained comparison DAG');direct+=1
        else:
            x,y=m['child_pair'];require(oldrows[a]==('*',x,2),'Wrong tape left factor')
            require(prior(x)==get(x),'Tape left expression changed')
            _,rhs,B=oldrows[b];require(B=='v31' and oldrows[B]==('*','v30',64),'Wrong B')
            require(rows[y]==('*','tape_half_B',rhs) and rows['tape_half_B']==('*',32,'v30'),'Wrong half radix')
            require(prior(rhs)==get(rhs) and prior('v30')==get('v30'),'Tape right expression changed');scaled+=1
    require(scaled==2 and deleted+affine==len(defs),'Incomplete residual map')
    return dict(power_identities={n:e for n,e in new['power_chain_identity'].items()},unchanged_residual_DAGs=direct,
      zero_definition_DAGs=deleted,exact_affine_congruence_identities=affine,scaled_tape_residuals=scaled,
      exact_parent_graph_SOS_correction='parent(restore(v))=child(v)+3*(tape_left(v)^2+tape_right(v)^2)',expression_nodes=len(nodes))


def _degree(packet):
    result=[]
    for prime in (1000000007,1000000009):
        degrees={};leading={};dependencies={}
        for i,n in enumerate(packet['parameters']+packet['auxiliaries']):
            degrees[n]=0 if n in packet['fixed_parameters'] else 1;leading[n]=(i%7)+1
            dependencies[n]={n} if n in packet['fixed_parameters'] else set()
        for n,op,a,b in packet['polynomial_source']:
            da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0
            ca=leading[a] if type(a) is str else a;cb=leading[b] if type(b) is str else b
            dep_a=dependencies[a] if type(a) is str else set();dep_b=dependencies[b] if type(b) is str else set()
            if op=='*':degrees[n]=da+db;leading[n]=ca*cb%prime;dependencies[n]=dep_a|dep_b
            else:
                degrees[n]=max(da,db);leading[n]=((ca if da>=db else 0)+(cb if db>=da else 0)*(1 if op=='+' else -1))%prime
                dependencies[n]=(dep_a if da>=db else set())|(dep_b if db>=da else set())
        require(degrees[packet['output']]==1936 and leading[packet['output']]!=0,'Exact leading-degree certificate failed')
        require(not dependencies[packet['output']],'Leading coefficient depends on fixed program values')
        result.append(dict(prime=prime,degree=1936,leading_coefficient=leading[packet['output']],fixed_parameter_dependencies=[]))
    return dict(exact_degree=1936,method='Complete source formal upper bound and nonzero evaluated homogeneous coefficient at that degree',certificates=result)


@lru_cache(None)
def _bundle(root_text,path_text):
    root,path=_paths(root_text);require(str(path)==path_text,'Parent path changed')
    parent=_load(path);parents={};packets={};certs={};degrees={}
    for ordinary in (False,True):
        old=parent.build(ordinary,root=root)
        require(digest(old)==PACKET_PINS[ordinary],'Actual611 packet differs from pinned descriptor')
        p=_rewrite(old);parents[ordinary]=old;packets[ordinary]=p;certs[ordinary]=_certificate(old,p);degrees[ordinary]=_degree(p)
        require(p['ledger']['polynomial']['operations']==(561 if ordinary else 363),'Wrong complete operation count')
    return dict(parent=parent,parents=parents,packets=packets,certificates=certs,degrees=degrees)


def _context(root=None):
    root,path=_paths(root);bundle=_bundle(str(root),str(path))
    bundle['parent']._context(root)
    return bundle


def build(ordinary=False,*,root=None):return deepcopy(_context(root)['packets'][flag(ordinary,'ordinary')])


def canonical_parent(ordinary=False,*,root=None):return deepcopy(_context(root)['parents'][flag(ordinary,'ordinary')])


def checked(packet,*,root=None):
    require(type(packet) is dict,'Complete canonical packet required');ordinary=flag(packet.get('ordinary'),'ordinary')
    require(exact(packet,_context(root)['packets'][ordinary]),'Noncanonical downstream packet');return packet


def polynomial_source(packet,*,root=None):return deepcopy(checked(packet,root=root)['polynomial_source'])


def _assignment(packet,values,signed):
    flag(signed,'signed');names=packet['parameters']+packet['auxiliaries']
    require(type(values) is dict and set(values)==set(names),'Wrong coordinate set')
    for n,v in values.items():
        require(type(n) is str and type(v) is int,'Exact integer coordinates required')
        lower=0 if not packet['ordinary'] and n in ('L0','R0') else 1
        require(signed or v>=lower,'Coordinate outside declared domain')
    return dict(values)


def evaluate(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);v=_assignment(p,values,signed);return execute(p['polynomial_source'],v)[p['output']]


def restore_assignment(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);v=_assignment(p,values,signed);env=execute(p['source'],v)
    out=dict(v,**{n:env[r] for n,r in p['computed_loader_fields'].items()})
    return _assignment(_context(root)['parents'][p['ordinary']],out,signed)


def project_assignment(packet,values,*,signed=False,require_graph=True,root=None):
    p=checked(packet,root=root);flag(require_graph,'require_graph');old=_context(root)['parents'][p['ordinary']]
    v=_assignment(old,values,signed);out={n:v[n] for n in p['parameters']+p['auxiliaries']}
    if require_graph:require(restore_assignment(p,out,signed=signed,root=root)==v,'Parent tuple is outside definition graph')
    return out


def identity(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root);v=_assignment(p,values,signed);old=_context(root)['parents'][p['ordinary']]
    restored=restore_assignment(p,v,signed=signed,root=root);a=execute(p['polynomial_source'],v);b=execute(old['polynomial_source'],restored)
    rr=[at(a,x)-at(a,y) for x,y in p['comparisons']];ro=[at(b,x)-at(b,y) for x,y in old['comparisons']]
    correction=0
    for m in p['comparison_map']:
        if m['new_index'] is None:require(ro[m['old_index']]==0,'Deleted defining residual nonzero')
        else:
            r=rr[m['new_index']];require(ro[m['old_index']]==m['factor']*r,'Residual map failed')
            if m['factor']==2:correction+=3*r*r
    require(b[old['output']]==a[p['output']]+correction,'Complete SOS graph identity failed')
    return dict(parent_output=b[old['output']],child_output=a[p['output']],correction=correction,residuals=rr)



def _cold_import_cases(root):
    code=r"""
import importlib.util,pathlib,sys,types
path=pathlib.Path(sys.argv[1]);root=pathlib.Path(sys.argv[2]);mode=sys.argv[3]
fake=types.ModuleType('u15_raw_half_tape_loader')
if mode=='foreign':fake.__file__='/not/the/authenticated/loader.py'
fake.build=lambda *a,**k: {'poisoned':True}
sys.modules['u15_raw_half_tape_loader']=fake
spec=importlib.util.spec_from_file_location('_cold561',path)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
p=m.build(True,root=root)
assert m.digest(m.canonical_parent(True,root=root))==m.PACKET_PINS[True]
assert p['ledger']['polynomial']['operations']==561
print('PASS')
"""
    root,_=_paths(root)
    for mode in ('fake','foreign'):
        p=subprocess.run([sys.executable,'-c',code,str(Path(__file__).resolve()),str(root),mode],text=True,capture_output=True)
        require(p.returncode==0 and p.stdout.strip()=='PASS','Cold imported source authentication failed: '+p.stderr[-2000:])
    return 2


def verify(root=None):
    bundle=_context(root);rng=random.Random(561363);counts=Counter();forms=[]
    def reject(fn):
        try:fn()
        except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
        raise AssertionError('Malformed input accepted')
    for ordinary in (False,True):
        p=build(ordinary,root=root)
        for case in range(64):
            signed=case>=32
            v={n:rng.randrange(-3,4) if signed else rng.randrange(1,6) for n in p['parameters']+p['auxiliaries']}
            answer=identity(p,v,signed=signed,root=root)
            full=restore_assignment(p,v,signed=signed,root=root)
            require(project_assignment(p,full,signed=signed,root=root)==v,'Graph roundtrip failed')
            counts['whole_graph_identities']+=1;counts['individual_residual_maps']+=len(p['comparison_map']);counts['signed_cases']+=signed
            counts['positive_restorations']+=not signed
        v={n:1 for n in p['parameters']+p['auxiliaries']}
        for name in v:
            for bad in (True,1.0,None):
                w=dict(v);w[name]=bad;reject(lambda w=w:evaluate(p,w,root=root))
        for key in ('source','comparisons','auxiliaries','comparison_map','computed_loader_fields','ledger','parameters','registers'):
            bad=deepcopy(p)
            if type(bad[key]) is list:bad[key]=tuple(bad[key])
            elif type(bad[key]) is dict:bad[key]={**bad[key],'tamper':1}
            reject(lambda bad=bad:checked(bad,root=root))
        for i,row in enumerate(p['source']):
            bad=deepcopy(p);bad['source'][i]=(row[0],row[1],row[2],1.0);reject(lambda bad=bad:checked(bad,root=root))
        for badflag in (0,1,0.0,1.0,None,'yes'):
            reject(lambda badflag=badflag:build(badflag,root=root))
            reject(lambda badflag=badflag:evaluate(p,v,signed=badflag,root=root))
            reject(lambda badflag=badflag:project_assignment(p,restore_assignment(p,v,root=root),require_graph=badflag,root=root))
        bad=build(ordinary,root=root);bad['source'][0]=('bad','+',0,0)
        require(build(ordinary,root=root)==p,'Build cache leaked');counts['copy_checks']+=1
        old=canonical_parent(ordinary,root=root);old['source'][0]=('bad','+',0,0)
        require(canonical_parent(ordinary,root=root)==bundle['parents'][ordinary],'Parent cache leaked');counts['copy_checks']+=1
        rows=polynomial_source(p,root=root);rows[0]=('bad','+',0,0)
        require(polynomial_source(p,root=root)==p['polynomial_source'],'Source cache leaked');counts['copy_checks']+=1
        if ordinary:
            full=restore_assignment(p,v,root=root)
            for n in p['computed_loader_fields']:
                w=dict(full);w[n]+=1;reject(lambda w=w:project_assignment(p,w,root=root))
        forms.append(dict(ordinary=ordinary,ledger=p['ledger'],compiler=p,source_certificate=bundle['certificates'][ordinary],degree=bundle['degrees'][ordinary]))
    counts['cold_import_isolation_checks']=_cold_import_cases(root)
    require(not hasattr(sys.modules.get(__name__), 'context'),'Public mutable cache holder')
    counts['unexposed_cache_holder_checks']=1
    return dict(status='PASS_DOWNSTREAM561',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_source_sha256=PARENT_SHA256,
       parent_packet_pins={str(k):v for k,v in PACKET_PINS.items()},forms=forms,counts=dict(counts),
       scope='Complete same valid-program positive relation via explicit zero-set bijection; full SOS correction on restoration graph, not same-tuple polynomial identity. No87 improvement.')


if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path);a.add_argument('--write',action='store_true');args=a.parse_args()
    result=json.loads(json.dumps(verify(args.root)));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:require(exact(result,json.loads(path.read_text())),'Receipt mismatch')
    print(json.dumps(dict(status=result['status'],counts=result['counts'],ledgers=[f['ledger'] for f in result['forms']]),indent=2))
