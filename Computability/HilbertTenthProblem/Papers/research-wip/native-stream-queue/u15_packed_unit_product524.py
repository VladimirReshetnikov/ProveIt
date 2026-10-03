"""Unit finalization of complete U15:524 ordinary /336 raw operations.

Six norm factors exclude -1 modulo4; their product can also absorb the sole
loader checksum. Same full integer zero set, hence the same positive relation.
The generic rewrite accepts other source-authenticated U15 downstream edits
only after validating the entire incoming SOS and the literal native blocks.
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

PARENT_FILE='u15_packed_joint_affine536.py'
PARENT_SHA='eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330'
PACKET_PINS={False: 'c606d349e66b8a772910ad5dea57a9c159831353ddba67facc0420ceb3c54ce5', True: '5c17ee17d34f97469112378268751a06d172d280592e2caa5f403c67c5e2c3b1'}
FINALIZERS=('auto','sos','anchor')


def require(ok,message):
    if not ok:raise ValueError(message)


def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def typed(x):
    if type(x) is dict:
        require(all(type(k) is str for k in x),'String metadata keys required')
        return ['dict',[[k,typed(x[k])] for k in sorted(x)]]
    if type(x) in (tuple,list):return [type(x).__name__,[typed(v) for v in x]]
    require(type(x) in (str,int,bool,type(None)),'Unsupported metadata type')
    return [type(x).__name__,x]


def digest(x):return hashlib.sha256(json.dumps(typed(x),separators=(',',':')).encode()).hexdigest()


def flag(v,name):require(type(v) is bool,name+' must be Boolean');return v


def mode(v):require(type(v) is str and v in FINALIZERS,'Unknown finalizer');return v


def execute(source,values):
    env=dict(values)
    for n,op,a,b in source:
        x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
        env[n]=x+y if op=='+' else x-y if op=='-' else x*y
    return env


def at(env,v):return env[v] if type(v) is str else v


def _count(rows):return dict(operations=len(rows),M=sum(op=='*' for _,op,_,_ in rows),A=sum(op!='*' for _,op,_,_ in rows))


def _source_check(source,parameters,auxiliaries):
    require(type(source) is list and type(parameters) is list and type(auxiliaries) is list,'Exact source lists required')
    names=parameters+auxiliaries
    require(all(type(n) is str for n in names) and len(set(names))==len(names),'Invalid supplied coordinate names')
    known=set(names)
    for row in source:
        require(type(row) in (tuple,list) and len(row)==4,'Bad source row')
        n,op,a,b=row
        require(type(n) is str and n not in known and type(op) is str and op in ('+','-','*'),'Bad source register/operator')
        require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Dangling or inexact source operand')
        known.add(n)
    return known


def _sort(rows,names):
    out=[];known=set(names)
    while rows:
        ready=[]
        for row in rows:
            if all(type(v) is int or v in known for v in row[2:]):out.append(row);known.add(row[0]);ready.append(row)
        require(bool(ready),'Cyclic unit source');rows=[r for r in rows if r not in ready]
    return out


def _sos(source,pairs):
    rows=list(source);squares=[]
    for i,(a,b) in enumerate(pairs):
        n=f'poly_res{i}';s=f'poly_sq{i}';rows.extend([(n,'-',a,b),(s,'*',n,n)]);squares.append(s)
    require(bool(squares),'Empty SOS interface');out=squares[0]
    for i,s in enumerate(squares[1:],1):n=f'poly_sum{i}';rows.append((n,'+',out,s));out=n
    return rows,out


def _degrees(p,rows,out):
    d={n:0 if n in p['fixed_parameters'] else 1 for n in p['parameters']+p['auxiliaries']}
    for n,op,a,b in rows:
        da=d[a] if type(a) is str else 0;db=d[b] if type(b) is str else 0
        d[n]=da+db if op=='*' else max(da,db)
    return d[out],d


def _validate_parent(p):
    require(type(p) is dict,'Complete packet required');typed(p);flag(p.get('ordinary'),'ordinary')
    known=_source_check(p['source'],p['parameters'],p['auxiliaries'])
    require(type(p['fixed_parameters']) is list and all(type(n) is str and n in p['parameters'] for n in p['fixed_parameters']),'Invalid fixed parameters')
    require(type(p['comparisons']) is list and all(type(pair) in (tuple,list) and len(pair)==2 and all(type(v) is int or type(v) is str and v in known for v in pair) for pair in p['comparisons']),'Bad comparisons')
    expected,out=_sos([tuple(r) for r in p['source']],p['comparisons'])
    require([tuple(r) for r in p['polynomial_source']]==expected and p['output']==out,'Incoming finalizer is not the complete literal SOS')
    _source_check(p['polynomial_source'],p['parameters'],p['auxiliaries'])
    degree,_=_degrees(p,expected,out)
    ledger=dict(certificate=_count(p['source']),polynomial=_count(expected),equations=len(p['comparisons']),positive_witnesses=len(p['auxiliaries']),formal_degree_upper_bound=degree,exact_degree_claimed=False)
    require(exact(p['ledger'],ledger),'Incoming ledger mismatch')
    return {n:(op,a,b) for n,op,a,b in p['source']}


def _native_guard(rows,prefix):
    p=lambda n:prefix+n
    a=p('R12');c=p('R10a');d=p('R14')
    expected={p('a_square'):('*',a,a),p('a4'):('*',4,a),p('a4m5'):('+',p('a4'),3),
      p('A'):('+',p('a_square'),p('a4m5')),p('c2'):('*',c,c),p('Ac2'):('*',p('A'),p('c2')),
      p('L15'):('*',d,d),p('R15'):('+',p('Ac2'),1),p('ic2'):('*',p('i'),p('c2')),
      p('ic22'):('*',p('ic2'),p('ic2')),p('H2'):('*',p('H17'),p('H17')),
      p('aux_y2'):('*',p('y_aux'),p('y_aux')),p('aux_square_gap'):('-',p('H2'),p('aux_y2')),
      p('L17'):('*',p('ic22'),p('aux_square_gap')),p('P17'):('-',1,p('aux_y2')),
      p('cam2'):('*',c,a),p('D1'):('+',p('wn2'),p('cam2')),p('gam'):('*',p('ga'),p('a4m5')),
      p('R14'):('+',p('D1'),p('gam'))}
    require(all(rows.get(n)==r for n,r in expected.items()),'Literal native norm block changed: '+prefix)
    return expected


def _strings(x):
    if type(x) is str:yield x
    elif type(x) is dict:
        for v in x.values():yield from _strings(v)
    elif type(x) in (list,tuple):
        for v in x:yield from _strings(v)


def _finalize(p,chosen):
    pairs=p['comparisons'];unit=p['unit_product_register'];ordinary=pairs[:-1]
    require(tuple(pairs[-1])==(unit,1),'Missing final unit equation')
    if chosen=='sos':rows,out=_sos(p['source'],pairs)
    else:
        rows=list(p['source']);anchor=1
        for i,(a,b) in enumerate(ordinary):
            n=f'unit_res{i}';s=f'unit_sq{i}';t=f'unit_anchor{i}'
            rows.extend([(n,'-',a,b),(s,'*',n,n),(t,'+',anchor,s)]);anchor=t
        rows.extend([('unit_times_anchor','*',unit,anchor),('unit_polynomial','-','unit_times_anchor',1)]);out='unit_polynomial'
    _source_check(rows,p['parameters'],p['auxiliaries'])
    live={out}
    for n,_,a,b in reversed(rows):
        if n in live:live.update(v for v in (a,b) if type(v) is str)
    require(all(n in live for n,_,_,_ in rows),'Dead emitted unit gate')
    degree,_=_degrees(p,rows,out)
    p.update(polynomial_source=rows,output=out,finalizer=chosen,ledger=dict(certificate=_count(p['source']),polynomial=_count(rows),
        equations=len(pairs),positive_witnesses=len(p['auxiliaries']),formal_degree_upper_bound=degree,exact_degree_claimed=False))
    return p


def rewrite(packet,*,finalizer='auto'):
    """Full local source transfer; caller authenticates the incoming U15 scope."""
    mode(finalizer);rows=_validate_parent(packet);p=deepcopy(packet)
    prefixes=(['input__geo__','input__and__'] if p['ordinary'] else [])+['native__']
    edits={};merged=[];guarded={}
    for prefix in prefixes:
        guarded.update(_native_guard(rows,prefix))
        for tail,left,right,kind in [('R15','L15','Ac2','main'),('P17','L17','aux_y2','auxiliary')]:
            old=prefix+tail;new='unit_'+prefix+kind
            edits[old]=(new,'-' if kind=='main' else '+',prefix+left,prefix+right)
            pair=(prefix+left,old)
            require(sum(tuple(x)==pair for x in p['comparisons'])==1,'Missing native comparison')
            merged.append(dict(old_pair=pair,old_index=next(i for i,x in enumerate(p['comparisons']) if tuple(x)==pair),factor=new,residual_sign=1,kind=kind,prefix=prefix))
    if p['ordinary']:
        require(rows.get('input__and__bs_q')==('+','input__and__bs_Q',1),'Literal loader checksum changed')
        old='input__and__bs_q';new='unit_loader_checksum';pair=(old,'input__and__q')
        require(sum(tuple(x)==pair for x in p['comparisons'])==1,'Missing checksum comparison')
        edits[old]=(new,'-','input__and__q','input__and__bs_Q')
        merged.append(dict(old_pair=pair,old_index=next(i for i,x in enumerate(p['comparisons']) if tuple(x)==pair),factor=new,residual_sign=-1,kind='checksum'))
    protected=set(edits)
    require(not any(a in protected or b in protected for n,op,a,b in p['source']),'A private offset has a source consumer')
    for key,value in p.items():
        if key not in ('source','polynomial_source','comparisons','ancestor_comparison_map'):
            require(not protected.intersection(_strings(value)),'An offset has another metadata consumer: '+key)
    source=[edits[n] if n in edits else (n,op,a,b) for n,op,a,b in p['source']]
    source=_sort(source,p['parameters']+p['auxiliaries'])
    product=merged[0]['factor']
    for i,m in enumerate(merged[1:],1):n=f'unit_product{i}';source.append((n,'*',product,m['factor']));product=n
    indices={m['old_index'] for m in merged};pairs=[];mapping=[]
    for i,pair in enumerate(p['comparisons']):
        if i in indices:continue
        mapping.append(dict(old_index=i,new_index=len(pairs),pair=tuple(pair)));pairs.append(tuple(pair))
    pairs.append((product,1))
    historical=p.pop('ancestor_comparison_map',None)
    if historical is not None:p['pre_unit_ancestor_comparison_map']=historical
    if p['ordinary']:p['loader_comparison_count']=packet['loader_comparison_count']-5
    p.update(source=source,comparisons=pairs,kind='native_norm_unit_product',unit_prefixes=prefixes,
      unit_factors=merged,unit_retained_comparison_map=mapping,unit_product_register=product,
      unit_local_source_guard=guarded,unit_incoming_packet_digest=digest(packet),
      finalizer_requested=finalizer,parent_relation='Exactly the same full supplied integer zero set; identical coordinate interface. Unit finalizer is not an off-zero SOS identity.',
      scope='Same complete fixed-arity valid-program ordinary-input first-halt relation as the authenticated incoming U15 compiler; no new87 bound.')
    if finalizer=='auto':
        candidates=[_finalize(deepcopy(p),f) for f in ('sos','anchor')]
        p=min(candidates,key=lambda x:(x['ledger']['formal_degree_upper_bound'],x['finalizer']))
    else:p=_finalize(p,finalizer)
    expected_saving=12 if p['ordinary'] else 2
    require(packet['ledger']['polynomial']['operations']-p['ledger']['polynomial']['operations']==expected_saving,'Wrong unit saving')
    require(packet['ledger']['polynomial']['M']==p['ledger']['polynomial']['M'],'Unit multiplication total changed')
    return p



def _validate_degree_packet(packet):
    require(type(packet) is dict,'Complete unit packet required');typed(packet)
    flag(packet.get('ordinary'),'ordinary')
    require(type(packet.get('finalizer')) is str and packet['finalizer'] in ('sos','anchor'),'Unknown emitted finalizer')
    _source_check(packet['source'],packet['parameters'],packet['auxiliaries'])
    _source_check(packet['polynomial_source'],packet['parameters'],packet['auxiliaries'])
    require(type(packet['fixed_parameters']) is list and all(type(n) is str and n in packet['parameters'] for n in packet['fixed_parameters']),'Invalid fixed parameters')
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    prefixes=(['input__geo__','input__and__'] if packet['ordinary'] else [])+['native__']
    require(exact(packet['unit_prefixes'],prefixes),'Wrong native prefix list')
    expected=[];guard={}
    for prefix in prefixes:
        local=dict(rows)
        local[prefix+'R15']=('+',prefix+'Ac2',1)
        local[prefix+'P17']=('-',1,prefix+'aux_y2')
        guard.update(_native_guard(local,prefix))
        for kind,op,left,right in [('main','-','L15','Ac2'),('auxiliary','+','L17','aux_y2')]:
            name='unit_'+prefix+kind
            require(rows.get(name)==(op,prefix+left,prefix+right),'Actual unit norm differs from degree identity')
            expected.append((name,kind,prefix))
    factors=packet['unit_factors']
    require(type(factors) is list and all(type(m) is dict for m in factors),'Wrong factor metadata')
    actual=[(m.get('factor'),m.get('kind'),m.get('prefix')) for m in factors if m.get('kind')!='checksum']
    require(actual==expected and len(factors)==len(expected)+int(packet['ordinary']),'Wrong norm factor definitions')
    require(exact(packet['unit_local_source_guard'],guard),'Norm guard metadata differs from actual source')
    if packet['ordinary']:
        require(rows.get('unit_loader_checksum')==('-', 'input__and__q','input__and__bs_Q'),'Wrong checksum source')
        require(factors[-1].get('factor')=='unit_loader_checksum' and factors[-1].get('kind')=='checksum','Wrong checksum metadata')
    fresh=_finalize(deepcopy(packet),packet['finalizer'])
    require(exact(packet['polynomial_source'],fresh['polynomial_source']) and packet['output']==fresh['output'] and exact(packet['ledger'],fresh['ledger']),'Unit finalizer or ledger changed')


def degree_audit(packet):
    """Exact source norm identity removes its known leading cancellation."""
    _validate_degree_packet(packet)
    certificates=[]
    for prime in (1000000007,1000000009):
        env={}
        for i,n in enumerate(packet['parameters']+packet['auxiliaries']):
            env[n]=(0 if n in packet['fixed_parameters'] else 1,(i%7)+1,{n} if n in packet['fixed_parameters'] else set())
        def val(x):return env[x] if type(x) is str else (0,x%prime,set())
        def mul(x,y):return (x[0]+y[0],x[1]*y[1]%prime,x[2]|y[2])
        def add(x,y,sign=1):
            d=max(x[0],y[0]);return (d,((x[1] if x[0]==d else 0)+sign*(y[1] if y[0]==d else 0))%prime,(x[2] if x[0]==d else set())|(y[2] if y[0]==d else set()))
        main={m['factor']:m['prefix'] for m in packet['unit_factors'] if m['kind']=='main'}
        factor_degrees={}
        for n,op,a,b in packet['polynomial_source']:
            if n in main:
                prefix=main[n];A=val(prefix+'R12');C=val(prefix+'R10a');X=val(prefix+'wn2');H=val(prefix+'a4m5');G=val(prefix+'ga')
                V=add(X,mul(G,H))
                # (a*c+V)^2-(a^2+H)c^2 = 2*a*c*V+V^2-H*c^2.
                env[n]=add(add(mul(val(2),mul(mul(A,C),V)),mul(V,V)),mul(H,mul(C,C)),-1)
            else:env[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
            if n in {m['factor'] for m in packet['unit_factors']}:factor_degrees[n]=env[n][0]
        d,c,deps=env[packet['output']]
        require(c!=0,'Evaluated top homogeneous coefficient vanished')
        require(not deps,'Leading coefficient depends on fixed program numerals')
        certificates.append(dict(prime=prime,degree=d,leading_coefficient=c,fixed_parameter_dependencies=[],factor_degrees=factor_degrees))
    require(certificates[0]['degree']==certificates[1]['degree'],'Degree certificate disagreement')
    return dict(exact_degree=certificates[0]['degree'],certificates=certificates,
      source_identity='(a*c+X+ga*H)^2-(a^2+H)c^2=2*a*c*(X+ga*H)+(X+ga*H)^2-H*c^2, H=4a+3',
      scope='Guarded exact source cancellation, then complete evaluated highest homogeneous coefficient; independent of fixed program values.')


def _paths(root=None):
    here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve()
    path=here/PARENT_FILE if (here/PARENT_FILE).is_file() else root/PARENT_FILE
    require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA,'Pinned536 source changed or missing')
    return root,path


def _load(path):
    s=importlib.util.spec_from_file_location('_unit524_parent',path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


@lru_cache(None)
def _bundle(root_text,path_text):
    root,path=_paths(root_text);require(str(path)==path_text,'Parent path changed');parent=_load(path)
    parents={};packets={};degrees={}
    for ordinary in (False,True):
        old=parent.build(ordinary,root=root);require(digest(old)==PACKET_PINS[ordinary],'Actual536 descriptor changed');parents[ordinary]=old
        for finalizer in FINALIZERS:
            p=rewrite(old,finalizer=finalizer)
            p.update(canonical_parent={'file':PARENT_FILE,'sha256':PARENT_SHA},source_lineage=dict(p['source_lineage'],**{PARENT_FILE:PARENT_SHA}))
            packets[ordinary,finalizer]=p;degrees[ordinary,finalizer]=degree_audit(p)
    return dict(parent=parent,parents=parents,packets=packets,degrees=degrees)


def _context(root=None):
    root,path=_paths(root);b=_bundle(str(root),str(path));b['parent']._context(root);return b


def build(ordinary=False,*,finalizer='auto',root=None):
    flag(ordinary,'ordinary');mode(finalizer);return deepcopy(_context(root)['packets'][ordinary,finalizer])


def canonical_parent(ordinary=False,*,root=None):return deepcopy(_context(root)['parents'][flag(ordinary,'ordinary')])


def checked(p,*,root=None):
    require(type(p) is dict,'Complete canonical packet required');o=flag(p.get('ordinary'),'ordinary');f=mode(p.get('finalizer_requested'))
    require(exact(p,_context(root)['packets'][o,f]),'Noncanonical unit packet');return p


def polynomial_source(p,*,root=None):return deepcopy(checked(p,root=root)['polynomial_source'])


def _assignment(p,values,signed):
    flag(signed,'signed');require(type(values) is dict and set(values)==set(p['parameters']+p['auxiliaries']),'Wrong coordinate set')
    for n,v in values.items():
        require(type(n) is str and type(v) is int,'Exact integer values required')
        lower=0 if not p['ordinary'] and n in ('L0','R0') else 1
        require(signed or v>=lower,'Value outside declared domain')
    return dict(values)


def evaluate(p,values,*,signed=False,root=None):
    p=checked(p,root=root);return execute(p['polynomial_source'],_assignment(p,values,signed))[p['output']]


def identity(p,values,*,signed=False,root=None):
    p=checked(p,root=root);v=_assignment(p,values,signed);old=_context(root)['parents'][p['ordinary']]
    before=execute(old['polynomial_source'],v);after=execute(p['polynomial_source'],v)
    rr=[at(before,a)-at(before,b) for a,b in old['comparisons']]
    remaining=sum(rr[m['old_index']]**2 for m in p['unit_retained_comparison_map']);U=1
    for m in p['unit_factors']:
        factor=1+m['residual_sign']*rr[m['old_index']]
        require(after[m['factor']]==factor,'Literal unit factor identity failed');U*=factor
    require(U==after[p['unit_product_register']],'Unit product changed')
    for m in p['unit_retained_comparison_map']:
        a,b=p['comparisons'][m['new_index']];require(at(after,a)-at(after,b)==rr[m['old_index']],'Retained residual changed')
    expected=remaining+(U-1)**2 if p['finalizer']=='sos' else U*(1+remaining)-1
    require(expected==after[p['output']],'Complete finalizer identity failed')
    require(before[old['output']]==sum(r*r for r in rr),'Parent complete SOS changed')
    return dict(parent_output=before[old['output']],child_output=expected,unit_product=U,remaining_square_sum=remaining)


def verify(root=None):
    b=_context(root);counts=Counter();rng=random.Random(524336);forms=[]
    def reject(fn):
        try:fn()
        except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
        raise AssertionError('Malformed input accepted')
    for a in range(4):
        for c in range(4):
            for d in range(4):
                require((d*d-((a+2)**2-1)*c*c)%4!=3,'Main norm negative unit');counts['main_mod4_cases']+=1
    for t in range(4):
        for u in range(4):
            for y in range(4):
                require((t*t*(u*u-y*y)+y*y)%4!=3,'Auxiliary norm negative unit');counts['auxiliary_mod4_cases']+=1
    for ordinary in (False,True):
        for finalizer in ('sos','anchor'):
            p=build(ordinary,finalizer=finalizer,root=root)
            for case in range(32):
                signed=case>=16;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
                identity(p,v,signed=signed,root=root);counts['whole_output_identities']+=1;counts['signed_cases']+=signed
                counts['individual_parent_residuals']+=len(b['parents'][ordinary]['comparisons'])
            v={n:1 for n in p['parameters']+p['auxiliaries']}
            for n in v:
                for badvalue in (True,1.0,None):
                    bad=dict(v);bad[n]=badvalue;reject(lambda bad=bad:evaluate(p,bad,root=root))
            for key in ('source','polynomial_source','comparisons','auxiliaries','unit_factors','unit_retained_comparison_map'):
                bad=deepcopy(p);bad[key]=tuple(bad[key]);reject(lambda bad=bad:checked(bad,root=root))
            for f in (True,False,1,1.0,'other',None):reject(lambda f=f:build(ordinary,finalizer=f,root=root))
            for target in ('unit_native__main','native__R14'):
                bad=deepcopy(p);i=next(i for i,r in enumerate(bad['source']) if r[0]==target)
                row=bad['source'][i];bad['source'][i]=(row[0],'*',row[2],row[3])
                bad=_finalize(bad,bad['finalizer'])
                reject(lambda bad=bad:degree_audit(bad))
            bad=deepcopy(p);bad['polynomial_source'][-1]=(bad['output'],'+',0,0)
            reject(lambda bad=bad:degree_audit(bad))

            for badbool in (0,1,1.0,None):reject(lambda badbool=badbool:evaluate(p,v,signed=badbool,root=root))
            old=canonical_parent(ordinary,root=root)
            for n,op,a,c in old['source']:
                if n.endswith('a4m5'):
                    bad=deepcopy(old);i=next(i for i,r in enumerate(bad['source']) if r[0]==n);bad['source'][i]=(n,op,a,4)
                    # Rebuilding the parent finalizer cannot hide the wrong Delta.
                    bad['polynomial_source'],bad['output']=_sos(bad['source'],bad['comparisons']);reject(lambda bad=bad:rewrite(bad))
            clone=build(ordinary,finalizer=finalizer,root=root);clone['source'][0]=('bad','+',0,0)
            require(build(ordinary,finalizer=finalizer,root=root)==p,'Public build cache leaked');counts['copy_checks']+=1
            clone=canonical_parent(ordinary,root=root);clone['source'][0]=('bad','+',0,0)
            require(canonical_parent(ordinary,root=root)==b['parents'][ordinary],'Public parent cache leaked');counts['copy_checks']+=1
            forms.append(dict(ordinary=ordinary,finalizer=finalizer,compiler=p,degree=b['degrees'][ordinary,finalizer]))
    for ordinary in (False,True):
        p=build(ordinary,root=root);require(p['finalizer']==('anchor' if ordinary else 'sos'),'Unexpected default selection')
    return dict(status='PASS_U15_UNIT_PRODUCT524',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      parent_sha256=PARENT_SHA,parent_packet_pins={str(k):v for k,v in PACKET_PINS.items()},counts=dict(counts),forms=forms,
      scope='Exact full integer zero-set equivalence of authenticated actual U15 sources; complete unchanged positive-coordinate relation. No off-zero equality or87 improvement.')


if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path);a.add_argument('--write',action='store_true');args=a.parse_args()
    out=json.loads(json.dumps(verify(args.root)));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    else:require(exact(out,json.loads(path.read_text())),'Receipt mismatch')
    print(json.dumps(dict(status=out['status'],counts=out['counts'],forms=[dict(ordinary=f['ordinary'],finalizer=f['finalizer'],ledger=f['compiler']['ledger'],degree=f['degree']['exact_degree']) for f in out['forms']]),indent=2))
