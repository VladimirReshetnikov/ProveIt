#!/usr/bin/env python3
"""Independent executable API audit. No producer edits and no imported producer tests.
Run once normally and once with python -O; --module selects the producer file.
This is finite executable regression evidence, not a full-shift proof.
"""
import argparse, copy, hashlib, importlib.util, itertools, json, pathlib, random, sys, time, traceback

ap=argparse.ArgumentParser()
ap.add_argument('--module', default=str(pathlib.Path(__file__).resolve().parents[1]/'compiler'/'reversible_binary.py'))
ap.add_argument('--receipt', default='audit-receipt.json')
args=ap.parse_args()
module_path=pathlib.Path(args.module).resolve()
before=module_path.read_bytes()
spec=importlib.util.spec_from_file_location('audited_reversible_binary',module_path)
M=importlib.util.module_from_spec(spec);sys.modules[spec.name]=M;spec.loader.exec_module(M)
start=time.time();tests=[];counts={};failures=[]

def check(condition,message):
    if not condition: raise RuntimeError(message)

def same(a,b,message): check(a==b, f'{message}: got {a!r}, want {b!r}')

def rejects(fn, label):
    try: fn()
    except (TypeError,ValueError): return
    except Exception as exc: raise RuntimeError(f'{label}: wrong error {type(exc).__name__}: {exc}') from exc
    raise RuntimeError(f'{label}: invalid input was accepted')

def frozen_setattr(obj,name,value):
    try: setattr(obj,name,value)
    except (AttributeError,TypeError,ValueError): return
    raise RuntimeError(f'mutable attribute {type(obj).__name__}.{name}')

def test(name,fn):
    print('RUN',name,flush=True)
    t=time.time()
    try:
        fn();tests.append({'name':name,'status':'passed','seconds':round(time.time()-t,6)})
        print('PASS',name,flush=True)
    except Exception as e:
        trace=traceback.format_exc();failures.append({'name':name,'error':str(e),'traceback':trace})
        tests.append({'name':name,'status':'failed','seconds':round(time.time()-t,6)})
        print('FAIL',name,trace,flush=True)

TRUE={'op':'true'}
def eq(i,k):return {'op':'eq','counter':i,'value':k}
def gt(i,k):return {'op':'gt','counter':i,'value':k}
def neg(g):return {'op':'not','arg':g}
def both(*gs):return {'op':'and','args':list(gs)}
def either(*gs):return {'op':'or','args':list(gs)}
def row(name='e',source='s',target='h',side=-1,delta=1,guard=None):
    return dict(name=name,source=source,target=target,side=side,delta=delta,guard=copy.deepcopy(TRUE if guard is None else guard))
def source(rows=None,J=1,controls=None,start='s',halt='h'):
    return dict(schema='reversible-two-counter-v1',controls=['s','h'] if controls is None else list(controls),start=start,halt=halt,class_cut=J,branches=[row()] if rows is None else copy.deepcopy(rows))

def truth(g,c):
    op=g['op']
    if op=='true':return True
    if op=='eq':return c[g['counter']]==g['value']
    if op=='gt':return c[g['counter']]>g['value']
    if op=='and':return all(truth(a,c) for a in g['args'])
    if op=='or':return any(truth(a,c) for a in g['args'])
    if op=='not':return not truth(g['arg'],c)
    raise RuntimeError('oracle invalid AST')

def atoms(g):
    if g['op'] in ('eq','gt'):return [(g['counter'],g['value'])]
    if g['op'] in ('and','or'):return [a for x in g['args'] for a in atoms(x)]
    if g['op']=='not':return atoms(g['arg'])
    return []

def outgoing(data,q,c):return [r for r in data['branches'] if r['source']==q and truth(r['guard'],c)]
def incoming(data,q,c):
    ans=[]
    for r in data['branches']:
        old=list(c);old[0 if r['side']==-1 else 1]-=r['delta']
        if r['target']==q and min(old)>=0 and truth(r['guard'],old):ans.append(r)
    return ans

def semantically_valid(data):
    # Larger than compiler quotient representatives, with distant-tail samples.
    J=data['class_cut'];values=list(range(J+7))+[100,10000]
    for q in data['controls']:
        for c in itertools.product(values,repeat=2):
            out=outgoing(data,q,c)
            if len(out)>1 or len(incoming(data,q,c))>1:return False
            if any(c[0 if r['side']==-1 else 1]+r['delta']<0 for r in out):return False
    return True

def forward_home(C,data,q,c,sign):
    rs=outgoing(data,q,c) if sign=='+' else incoming(data,q,c)
    if not rs:return C.encode(q,*c,sign='-' if sign=='+' else '+')
    check(len(rs)==1,'oracle multiple incident branches')
    r=rs[0]
    if r['delta']==0:return C.encode(r['target'] if sign=='+' else r['source'],*c,sign=sign)
    mode=('O' if sign=='+' else 'I',r['name'])
    anchor=r['side']*C.S
    return frozenset([-C.Z-c[0],0,C.Z+c[1],anchor,anchor+C.gap[(mode,sign)]])

class IntSubclass(int):pass

def schema_rejections():
    cases=[]
    def root(field,vals):
        for val in vals:
            d=source();d[field]=val;cases.append((f'root {field}={val!r}',d))
    root('schema',[None,True,1,'wrong'])
    root('class_cut',[True,False,0.0,1.0,-1,'1',None,IntSubclass(1)])
    root('controls',[None,{},'sh',('s','h'),[],['s','s'],['s',1],['s',True]])
    root('start',[None,True,0,'missing'])
    root('halt',[None,True,0,'missing'])
    root('branches',[None,{},'rows',tuple()])
    for key in source():
        d=source();del d[key];cases.append((f'missing root {key}',d))
    d=source();d['extra']=0;cases.append(('extra root field',d))
    cases += [('root list',[]),('root none',None),('root int',1)]
    for field,vals in [('name',[None,1,True]),('source',[None,1,True,'missing']),('target',[None,1,True,'missing']),('side',[True,False,-1.0,1.0,0,2,'-1',IntSubclass(-1)]),('delta',[True,False,-1.0,0.0,1.0,2,-2,'1',IntSubclass(1)])]:
        for val in vals:
            d=source();d['branches'][0][field]=val;cases.append((f'row {field}={val!r}',d))
    for key in row():
        d=source();del d['branches'][0][key];cases.append((f'missing row {key}',d))
    d=source();d['branches'][0]['extra']=0;cases.append(('extra row field',d))
    d=source();d['branches']=[row(),row()];cases.append(('duplicate branch names',d))
    d=source();d['branches'][0]['source']='h';cases.append(('halt has exits',d))
    asts=[None,True,[],{}, {1:'true'}, {'op':'true',1:0}, {'op':'false'},{'op':1},{'op':'true','extra':0},{'op':'eq','counter':0}, {'op':'not'}, {'op':'and'}, {'op':'or','args':{}}, {'op':'and','args':(TRUE,)}, {'op':'not','arg':TRUE,'args':[]}, {'op':'eq','counter':0,'value':0,'extra':0}]
    for op in ('eq','gt'):
        asts.extend({'op':op,'counter':i,'value':0} for i in (True,False,0.0,1.0,-1,2,'0',None,IntSubclass(0)))
        asts.extend({'op':op,'counter':0,'value':k} for k in (True,False,0.0,1.0,-1,'0',None,IntSubclass(0)))
    asts += [both(TRUE,{'op':'bogus'}),either({'op':'eq','counter':False,'value':0},TRUE)]
    for a in asts:
        d=source();d['branches'][0]['guard']=a;cases.append((f'AST {a!r}',d))
    for label,d in cases:rejects(lambda d=d:M.compile_source(d),label)
    counts['schema_invalid_rejected']=len(cases)

def explicit_semantics():
    invalid=[
      source([row(guard=eq(0,0))],J=0),
      source([row(delta=-1)],J=0),
      source([row(delta=0,guard=eq(0,2))],J=1),
      source([row('a',target='a',delta=0),row('b',target='b',delta=0)],controls=['s','a','b','h']),
      source([row('a',source='s',delta=1),row('b',source='t',delta=0)],controls=['s','t','h']),
      source([row('a',source='s',delta=1,guard=eq(0,0)),row('b',source='t',delta=0,guard=eq(0,1))],controls=['s','t','h']),
    ]
    for i,d in enumerate(invalid):rejects(lambda d=d:M.compile_source(d),f'explicit semantic invalid {i}')
    valid=[
      source([],J=0,controls=['h'],start='h',halt='h'),
      source([],J=0),
      source([row(delta=0,target='s')],J=0),
      source([row(target='s')],J=0),
      source([row(delta=0,guard=both())],J=0),
      source([row(delta=-1,guard=either())],J=0),
      source([row(guard=neg(neg(TRUE)))],J=0),
      source([row(delta=-1,guard=gt(0,0))],J=0),
      source([row(guard=eq(1,0))],J=0),
      source([row(delta=0,guard=both(either(eq(0,0),gt(0,0)),neg(either())))],J=0),
      source([row('a',source='s',delta=1,guard=eq(0,0)),row('b',source='t',delta=1,guard=gt(0,0))],controls=['s','t','h'],J=1),
    ]
    sampled=0
    for d in valid:
        check(semantically_valid(d),'bad independent explicit fixture')
        C=M.compile_source(d)
        for q in d['controls']:
            for c in itertools.product((0,1,2,7),repeat=2):
                for sign in ('+','-'):
                    x=C.encode(q,*c,sign=sign);want=forward_home(C,d,q,c,sign);got=C.step(x,verify=True)
                    same(got,want,f'home semantics {d} q={q}, c={c}, sign={sign}')
                    same(C.step(got,inverse=True,verify=True),x,'home inverse consistency')
                    sampled+=1
    counts.update(explicit_semantic_invalid=len(invalid),explicit_semantic_valid=len(valid),home_semantic_checks=sampled)

def finite_class_oracle():
    rng=random.Random(104729);accepted=0;rejected=0;boundary=0
    for n in range(100):
        J=rng.randrange(3)
        gs=[TRUE,both(),either(),eq(0,0),gt(0,0),eq(1,0),gt(1,0),neg(eq(0,0))]
        if J:gs += [eq(0,J),gt(1,J),both(eq(0,J),neg(eq(1,0))),either(eq(0,0),eq(1,J))]
        rows=[]
        for r in range(rng.randrange(1,4)):
            rows.append(row(f'e{r}',source=rng.choice(['s','t']),target=rng.choice(['s','t','h']),side=rng.choice([-1,1]),delta=rng.choice([-1,0,1]),guard=rng.choice(gs)))
        d=source(rows,J,['s','t','h'])
        cutvalid=all(k<=J and k+(r['delta'] if i==(0 if r['side']==-1 else 1) else 0)<=J for r in rows for i,k in atoms(r['guard']))
        want=cutvalid and semantically_valid(d)
        try:C=M.compile_source(d)
        except (TypeError,ValueError):
            check(not want,f'valid oracle schema rejected: {d}')
            rejected+=1;continue
        check(want,f'invalid oracle schema accepted: {d}');accepted+=1
        for q in d['controls']:
            for c in itertools.product((0,J+1,J+2,17),repeat=2):
                for sign in ('+','-'):
                    same(C.step(C.encode(q,*c,sign=sign)),forward_home(C,d,q,c,sign),f'finite class home {d} {(q,c,sign)}')
                    boundary+=1
    counts.update(random_schema_total=100,random_schema_accepted=accepted,random_schema_rejected=rejected,random_home_semantic_checks=boundary)

def all_class_predicates():
    checks=0;accepted=0;rejected=0
    for J in range(3):
      for side in (-1,1):
       for delta in (-1,0,1):
        for counter in (0,1):
         for k in range(J+1):
          guards=[eq(counter,k),gt(counter,k),neg(eq(counter,k)),neg(gt(counter,k)),both(eq(counter,k),gt(1-counter,0)),either(eq(counter,k),eq(1-counter,0)),neg(both(gt(counter,k),eq(1-counter,0)))]
          for g in guards:
            d=source([row(side=side,delta=delta,guard=g)],J)
            cutvalid=all(t<=J and t+(delta if i==(0 if side==-1 else 1) else 0)<=J for i,t in atoms(g))
            valid=cutvalid and semantically_valid(d)
            try:C=M.compile_source(d)
            except (TypeError,ValueError):
                check(not valid,f'class predicate valid rejected {d}')
                rejected+=1;continue
            check(valid,f'class predicate invalid accepted {d}');accepted+=1
            b=C.branches[0]
            for c in itertools.product(tuple(range(J+4))+(10**30,),repeat=2):
                old=list(c);old[0 if side==-1 else 1]-=delta
                same(b.guard(*c),truth(g,c),f'exact source class predicate {d} {c}')
                same(b.image_guard(*c),min(old)>=0 and truth(g,old),f'exact image class predicate {d} {c}')
                checks+=2
    counts.update(class_predicate_schemas=accepted+rejected,class_predicate_accepted=accepted,class_predicate_rejected=rejected,class_predicate_point_checks=checks)

def finite_input_validation():
    C=M.compile_source(source())
    invalid=[None,[],[0],(0,),range(3),{}, {'x':1},'010',0,True,set([False]),set([True]),set([0.0]),set([1.0]),set(['1']),set([(0,)]),set([IntSubclass(1)])]
    for x in invalid:
        rejects(lambda x=x:C.step(x),f'step {x!r}')
        rejects(lambda x=x:C.step(x,inverse=True),f'inverse step {x!r}')
        if C.E:
            rejects(lambda x=x:C.E[0].apply(x),f'gate apply {x!r}')
            rejects(lambda x=x:C.E[0].raw(x),f'gate raw {x!r}')
    for field in ('inverse','verify'):
        for val in (0,1,None,'yes',[],IntSubclass(1)):
            rejects(lambda val=val,field=field:C.step(frozenset(),**{field:val}),f'flag {field}={val!r}')
    for q in (None,True,0,'unknown'):
        rejects(lambda q=q:C.encode(q,0,0),f'encode control {q!r}')
    for k in (-1,True,False,0.0,1.0,None,'0',IntSubclass(0)):
        rejects(lambda k=k:C.encode('s',k,0),f'encode c0 {k!r}')
        rejects(lambda k=k:C.encode('s',0,k),f'encode c1 {k!r}')
    for sign in (None,True,0,'x',''):
        rejects(lambda sign=sign:C.encode('s',0,0,sign=sign),f'encode sign {sign!r}')
    huge=10**100
    for x in (set(),frozenset(),{-huge,-1,0,huge},frozenset([-10,-5,-1]),set(C.encode('s',0,0))):
        snapshot=frozenset(x);got=C.step(x)
        same(frozenset(x),snapshot,'input set mutated')
        check(type(got) is frozenset,'step must return frozen configuration even for inert input')
        same(C.step(got,inverse=True),snapshot,'signed-large finite inverse')
    counts['finite_input_invalid_cases']=len(invalid)

def mutation_resistance():
    d=source([row(delta=0,guard=eq(0,0))],J=0)
    C=M.compile_source(d);x=C.encode('s',0,0);before_step=C.step(x);before_ledger=C.ledger()
    d['controls'].append('evil');d['controls'][0]='changed';d['branches'][0]['guard']['value']=99;d['branches'][0]['target']='s';d['class_cut']=999;d['branches'].append(row('new'))
    same(C.step(x),before_step,'source nested mutation changes compiled behavior')
    same(C.encode('s',0,0),x,'source controls alias')
    same(C.ledger(),before_ledger,'source alias changed ledger')
    for name in ('controls','branches','J','E','P','gap','modes','radius','start','halt','source_data'):
        if hasattr(C,name):frozen_setattr(C,name,None)
    for name in ('controls','branches','E','P','modes'):
        if hasattr(C,name):check(type(getattr(C,name)) is tuple,f'{name} not immutable tuple')
    try:C.gap[(('H','s'),'+')]=999
    except (TypeError,AttributeError):pass
    else:raise RuntimeError('gap mapping mutable')
    for gate in C.E+C.P:
        for name in ('P','Q','B','L','M','radius','guard','shapes','name'):
            if hasattr(gate,name):frozen_setattr(gate,name,None)
        if hasattr(gate,'guard'):
            check(not callable(gate.guard),'compiled gate exposes callable guard')
    for branch in C.branches:
        for name in ('source','target','side','delta','guard','name'):
            if hasattr(branch,name):frozen_setattr(branch,name,None)
        check(type(branch.domain_table) is tuple and all(type(r) is tuple for r in branch.domain_table),'branch domain table mutable')
        check(type(branch.image_table) is tuple and all(type(r) is tuple for r in branch.image_table),'branch image table mutable')
    # Recursively attempt ordinary mutation of any exposed source-data snapshot.
    def mutate_or_recurse(v):
        if isinstance(v,dict):
            v.clear();return
        if isinstance(v,list):v.clear();return
        if hasattr(v,'items'):
            vals=list(v.values())
            try:v['__mutation__']=True
            except (TypeError,AttributeError):pass
            else:raise RuntimeError('source snapshot mutable mapping')
            for value in vals:mutate_or_recurse(value)
        elif isinstance(v,tuple):
            for value in v:mutate_or_recurse(value)
    if hasattr(C,'source_data'):mutate_or_recurse(C.source_data)
    same(C.step(x),before_step,'exposed source_data mutation affects compiler')
    # ledger may be fresh mutable JSON; mutation must never alias compiled state.
    led=C.ledger();led['radius']=-1
    same(C.ledger(),before_ledger,'ledger result aliases state')
    counts['immutability_factors_checked']=len(C.E)+len(C.P)

def constructor_bypasses():
    from dataclasses import replace
    for name in ('Gate','Branch','Compiler','CompiledSource'):
        if not hasattr(M,name):continue
        cls=getattr(M,name)
        rejects(lambda cls=cls:cls(),f'{name} bare constructor')
        rejects(lambda cls=cls:cls('unsafe',{0,0,1},{0,2},3,lambda *a:True),f'{name} legacy callable constructor')
        rejects(lambda cls=cls:cls(P=[0,0,1],Q=[0,2,3],B=3),f'{name} duplicate shape before dedup')
        rejects(lambda cls=cls:cls(guard=lambda *a:True),f'{name} keyword callback')
    C=M.compile_source(source())
    rejects(lambda:replace(C), 'dataclasses.replace compiled constructor bypass')
    rejects(lambda:replace(C.E[0]), 'dataclasses.replace gate constructor bypass')
    rejects(lambda:replace(C.branches[0]), 'dataclasses.replace branch constructor bypass')
    for b in C.branches:
        for value in (-1,True,False,0.0,1.0,None,'1',IntSubclass(1)):
            for method in (b.guard,b.image_guard):
                rejects(lambda value=value,method=method:method(value,0),'branch predicate bad left counter')
                rejects(lambda value=value,method=method:method(0,value),'branch predicate bad right counter')
        for c in itertools.product((0,1,2,10000),repeat=2):
            same(b.guard(*c),truth(source()['branches'][0]['guard'],c),'source truth-table oracle')
            same(b.image_guard(*c),c[0]>=1,'exact image truth-table oracle')
    for g in C.E+C.P:
        check(type(g.P) is frozenset and type(g.Q) is frozenset,'gate support not frozen')
        same(len(g.P),len(g.Q),'gate equal mass')
        check(len(g.P)>=2,'gate mass >=2')
        check(all(type(z) is int and -g.B<=z<=g.B for z in g.P|g.Q),'signed gate coordinates/bounds')
        check({z-min(g.P) for z in g.P}!={z-min(g.Q) for z in g.Q},'translated supports accepted')
        if g.guard is not None:
            for name in ('J','Z','table'):frozen_setattr(g.guard,name,None)
            check(type(g.guard.table) is tuple and all(type(r) is tuple for r in g.guard.table),'gate table mutable')
        for value in (0,1,None,'yes'):
            rejects(lambda value=value,g=g:g.apply(frozenset(),verify=value),'gate verify non-Boolean')
    counts['constructor_bypass_probes']=19

def complex_boolean_asts():
    # Shared DAGs are ordinary JSON-shaped input snapshots and are not cycles.
    a=eq(0,0);g=both(either(a,neg(a)),both(),neg(either()))
    d=source([row(delta=0,guard=g)],0)
    C=M.compile_source(d)
    for c in itertools.product((0,1,9),repeat=2):same(C.branches[0].guard(*c),True,'shared nested AST')
    cycle={'op':'not'};cycle['arg']=cycle
    d=source();d['branches'][0]['guard']=cycle
    rejects(lambda:M.compile_source(d),'cyclic not AST')
    cycle={'op':'and','args':[]};cycle['args'].append(cycle)
    d=source();d['branches'][0]['guard']=cycle
    rejects(lambda:M.compile_source(d),'cyclic array AST')
    g=TRUE
    for _ in range(10000):g={'op':'not','arg':g}
    d=source();d['branches'][0]['guard']=g
    C=M.compile_source(d)
    same(C.branches[0].guard(0,0),True,'deep finite guard evaluation')
    counts['deep_boolean_nesting']=10000

def isolated_gate_reference():
    def oracle(g,x):
        raw={}
        if x:
            for u in range(min(x)-g.B,max(x)+g.B+1):
                window=frozenset(z-u for z in x if abs(z-u)<=g.B)
                if window==g.P:raw[u]=0
                if window==g.Q:
                    check(u not in raw,'oracle ambiguous raw key')
                    raw[u]=1
        active=[]
        for u,label in raw.items():
            shape=(g.P,g.Q)[label]
            if frozenset(z-u for z in x if abs(z-u)<=g.L)!=shape:continue
            if any(v!=u and abs(v-u)<=g.M for v in raw):continue
            if g.guard is not None:
                cs=[]
                for side in (-1,1):
                    seen=[k for k in range(g.guard.J+1) if u+side*(g.guard.Z+k) in x]
                    if len(seen)>1:break
                    cs.append(seen[0] if seen else g.guard.J+1)
                if len(cs)!=2 or not g.guard.table[cs[0]][cs[1]]:continue
            active.append((u,label))
        y=set(x)
        for u,label in active:
            y-=set(u+z for z in (g.P,g.Q)[label])
            y|=set(u+z for z in (g.Q,g.P)[label])
        return raw,frozenset(y)
    fixtures=[source(),source([row(side=1,delta=-1,guard=gt(1,0))],0),source([row(delta=0,guard=eq(1,0))],0)]
    total=0;active_outputs=0;selected_count=0
    for d in fixtures:
        C=M.compile_source(d)
        selected=[];seen=set()
        for g in C.E+C.P:
            category=g.name.split(':')[0]
            if category not in seen:
                selected.append(g);seen.add(category)
        selected_count+=len(selected)
        for g in selected:
            context=set()
            if g.guard is not None:
                entries=[(a,b) for a in range(C.J+2) for b in range(C.J+2) if g.guard.table[a][b]]
                if entries:
                    a,b=entries[0]
                    if a<=C.J:context.add(-C.Z-a)
                    if b<=C.J:context.add(C.Z+b)
            for shape in (g.P,g.Q):
                base=set(shape)|context
                variants=[base]
                for boundary in (g.B,g.L,g.M):
                    for offset in (-1,0,1):
                        for sign in (-1,1):variants.append(base|{sign*(boundary+offset)})
                for distance in (g.M-1,g.M,g.M+1,g.M+2*g.B+1):
                    for other in (g.P,g.Q):variants.append(base|set(z+distance for z in other))
                for x in variants:
                    x=frozenset(x);want_raw,want=oracle(g,x)
                    same(g.raw(x),want_raw,'raw keys versus independent bounded-window oracle')
                    got=g.apply(x,verify=True)
                    same(got,want,'factor versus independent isolated-swap oracle')
                    same(g.apply(got,verify=True),x,'isolation seam involution')
                    if got!=x:active_outputs+=1
                    total+=1
    counts.update(reference_gates_selected=selected_count,reference_gate_inputs=total,reference_gate_nonidentity_outputs=active_outputs)

def malformed_finite_states():
    rng=random.Random(202610030314);cases=0;gates=0;translation=0
    schemas=[source([],0,controls=['h'],start='h',halt='h'),source([row(delta=0,target='s')],0),source(),source([row(delta=-1,side=1,guard=gt(1,0))],0),source([row(guard=eq(1,0))],0)]
    for d in schemas:
        C=M.compile_source(d);xs=[frozenset()]
        for n in range(128):xs.append(frozenset(i-3 for i in range(7) if (n>>i)&1))
        base=C.encode(d['start'],0,1)
        xs += [base,frozenset(set(base)|{z+C.M if hasattr(C,'M') else z+2*C.B3 for z in base}),frozenset(range(-C.B3,C.B3+1))]
        for trial in range(35):
            x=set(base) if trial%3 else set()
            for _ in range(rng.randrange(1,12)):
                z=rng.randrange(-2*C.Z,2*C.Z+1)
                if z in x:x.remove(z)
                else:x.add(z)
            # Multiple counter read ones must be safe even though not admissible.
            if trial%4==0:x.update([-C.Z,-C.Z-1,C.Z,C.Z+1])
            if trial%7==0:x.update(z+3*C.B3 for z in base)
            xs.append(frozenset(x))
        for x in xs:
            y=C.step(x,verify=True)
            same(len(y),len(x),'malformed global particle conservation')
            same(C.step(y,inverse=True,verify=True),x,'malformed F^-1 F')
            z=C.step(x,inverse=True,verify=True)
            same(C.step(z,verify=True),x,'malformed F F^-1')
            cases+=1
        for x in xs[-10:]:
            shift=-12345
            same(C.step(frozenset(z+shift for z in x)),frozenset(z+shift for z in C.step(x)),'translation equivariance')
            translation+=1
        # Gate-local invariants on both endpoints, polluted endpoints, near keys.
        for g in C.E+C.P:
            for shape in (g.P,g.Q):
                for shift in (-2,0,71):
                    x=frozenset(z+shift for z in shape)
                    y=g.apply(x,verify=True)
                    same(len(y),len(x),'individual gate conservation')
                    same(g.apply(y,verify=True),x,'individual gate involution')
                    gates+=1
    counts.update(malformed_global_inputs=cases,gate_endpoint_involutions=gates,translation_checks=translation)

for name,fn in [('strict_schema_runtime_errors',schema_rejections),('explicit_edgecase_semantics',explicit_semantics),('independent_class_and_injectivity_oracle',finite_class_oracle),('exhaustive_small_class_source_image_predicates',all_class_predicates),('finite_input_validation',finite_input_validation),('immutable_snapshots',mutation_resistance),('public_constructor_bypasses',constructor_bypasses),('deep_nested_empty_cyclic_boolean_asts',complex_boolean_asts),('independent_isolated_gate_window_oracle',isolated_gate_reference),('malformed_finite_conservation_reversibility',malformed_finite_states)]:test(name,fn)
after=module_path.read_bytes()
if after!=before:failures.append({'name':'producer_changed_during_audit','error':'module bytes changed while audit ran'})
receipt=dict(status='failed' if failures else 'passed',optimized=not __debug__,python=sys.version,producer_file=module_path.name,producer_sha256=hashlib.sha256(before).hexdigest(),audit_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),counts=counts,tests=tests,failures=failures,seconds=round(time.time()-start,6),scope='Finite executable API audit; not a proof of full-shift properties.')
pathlib.Path(args.receipt).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
sys.exit(bool(failures))
