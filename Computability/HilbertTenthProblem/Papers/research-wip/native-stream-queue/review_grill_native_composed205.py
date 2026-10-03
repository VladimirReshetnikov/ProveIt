#!/usr/bin/env python3
"""Independent bounded complete-source audit of frozen Grill205."""
if not __debug__:
    raise RuntimeError('Run without -O')
import argparse, copy, hashlib, json, random, subprocess, sys, tempfile, types
from collections import Counter
from fractions import Fraction
from pathlib import Path
import sympy as sp
SOURCE_SHA='4084a58d5cf30694a8717c26d0abdf2aecc2fa6a7099d9815f35521005afab94'
PARENT_PINS={
 'grill_tag_native_weak_cone.py':'8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9',
 'grill_tag_native_phase_residual206.py':'b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1'}
RECEIPT_PINS={
 'weak':'855a973645e93f64d9e61998880bf270d0f048b8a13a4823ea756bf57092695a',
 'strong':'bc58e688fd9f47e2a6ad2414084d68cc4f4118c0234a7f72f949b2524e995908'}
NOTE_SHA='47416c75df576e3f13fd2ebd2a13ac8b7d1fa9d1049e79de5243833ed5751592'

def need(x,msg):
    if not x: raise ValueError(msg)
def exact(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
    if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def normalized(x):return json.loads(json.dumps(x))
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def pinned(path,h):
    data=Path(path).read_bytes();need(hashlib.sha256(data).hexdigest()==h,'Source/receipt pin '+str(path));return data

def execute(p,values):
    e=dict(values)
    def at(v):return e[v] if type(v)is str else v
    for n,o,a,b in p['polynomial_source']:
        x,y=at(a),at(b);e[n]={'*':lambda:x*y,'+':lambda:x+y,'-':lambda:x-y}[o]()
    return e,e[p['output']],[at(a)-at(b) for a,b in p['comparisons']]

def phase_node(p):
    c=p['comparisons'][3]
    rows=[r for r in p['polynomial_source'][len(p['source']):] if r[1]=='-' and r[2:]==c]
    need(len(rows)==1,'Unique actual phase residual subtraction');return rows[0][0]

def symbolic(p,atoms):
    definitions={r[0]:r[1:] for r in p['polynomial_source']};cache=dict(atoms)
    def f(x):
        if type(x)is int:return sp.Integer(x)
        if x in cache:return cache[x]
        need(x in definitions,'Missing symbolic atom '+x)
        o,a,b=definitions[x];a,b=f(a),f(b)
        cache[x]=sp.expand(a*b if o=='*' else a+b if o=='+' else a-b)
        return cache[x]
    return f

class Intern:
    def __init__(self):self.ids={}
    def token(self,t):
        if t not in self.ids:self.ids[t]=len(self.ids)
        return self.ids[t]
    def source(self,p,cuts):
        e={n:self.token(('input',n)) for n in p['parameters']+p['auxiliaries']}
        def at(x):return e[x] if type(x)is str else self.token(('integer',x))
        for n,o,a,b in p['polynomial_source']:
            if n in cuts:e[n]=self.token(('proved-cut',cuts[n]));continue
            x,y=at(a),at(b)
            if o in('+','*'):x,y=sorted((x,y))
            e[n]=self.token((o,x,y))
        return e,at

def proof_weak(old,new,counts):
    need(len(old['comparisons'])==len(new['comparisons']),'Same complete weak residual count')
    m=len(new['program']);B,q0=sp.symbols('B q0');h=sp.symbols('h:'+str(2*m))
    atoms={**{'Shat'+str(i):v for i,v in enumerate(h)},'phase_initial':q0}
    of=symbolic(old,dict(atoms,**{old['interfaces']['B']:B}));nf=symbolic(new,dict(atoms,**{new['interfaces']['B']:B}))
    J=sum(h)-2*m;T=sum((m-i)*(h[2*i]+h[2*i+1]-2) for i in range(1,m))
    formula=m*(h[0]+h[1])-(B-1)*T+q0-(J+3*m)
    for p,f in ((old,of),(new,nf)):
        need(sp.expand(f(phase_node(p))-formula)==0,'Expanded phase identity in original hats')
        need(sp.expand(f(p['interfaces']['J'])-J)==0,'Actual J definition')
        need(sp.expand(f(p['interfaces']['P'])-((B-1)*J+1))==0,'Actual P definition')
        counts['expanded_phase_J_P_identities']+=3
    if m==1:need(sp.expand(formula-(q0-1))==0,'One phase alias')
    inter=Intern();oe,oa=inter.source(old,{phase_node(old):'phase'});ne,na=inter.source(new,{phase_node(new):'phase'})
    need(oa(old['interfaces']['B'])==na(new['interfaces']['B']),'B equality before phase cut')
    for i,(oc,nc) in enumerate(zip(old['comparisons'],new['comparisons'])):
        if i!=3:need([oa(x) for x in oc]==[na(x) for x in nc],'Whole unchanged comparison operands')
        counts['complete_weak_residual_identities']+=1
    for k in set(old['interfaces']) & set(new['interfaces']):need(oa(old['interfaces'][k])==na(new['interfaces'][k]),'Retained weak interface '+k)
    need([oa(x) for x in old.get('unit_factors',[])]==[na(x) for x in new.get('unit_factors',[])],'All native factors weak')
    need(oa(old['output'])==na(new['output']),'Complete weak final polynomial')
    counts['complete_weak_DAG_identities']+=1

def proof_strong(old,new,counts):
    for key in ('source','polynomial_source'):
        rows=old[key];by={r[0]:r[1:] for r in rows};p0=old['interfaces']['P0']
        need(by['three_x__0']==['*','x',3] and by[p0]==['+','Z0','three_x__0'],'Literal strong width source')
        for name in ('three_x__0','Z0'):
            consumers=[n for n,o,a,b in rows if name in(a,b)]
            need(consumers==[p0],'Width source private '+name)
        expected=[([n,'+','Z0','x'] if n==p0 else [n,o,a,b]) for n,o,a,b in rows if n!='three_x__0']
        need(exact(expected,new[key]),'Literal independent width-after-phase whole source')
        counts['literal_width_after_phase_schedules']+=1
    for key in ('comparisons','interfaces','parameters','auxiliaries','maps','groups_U','groups_V','baselines','K','unit_factors','unit_register','root_coordinate','projection_aliases','scale_exponent','region_exponents','native_prefix','group_hat_registers'):
        need(exact(old.get(key),new.get(key)),'Normative diamond field '+key)
    x,z=sp.symbols('x Z');sf=symbolic(old,{'x':x,'Z0':z-2*x});nf=symbolic(new,{'x':x,'Z0':z})
    need(sp.expand(sf(old['interfaces']['P0'])-nf(new['interfaces']['P0']))==0,'Exact signed width identity')
    inter=Intern();oe,oa=inter.source(old,{old['interfaces']['P0']:'width'});ne,na=inter.source(new,{new['interfaces']['P0']:'width'})
    for oc,nc in zip(old['comparisons'],new['comparisons']):
        need([oa(x) for x in oc]==[na(x) for x in nc],'Complete signed comparison identity');counts['complete_strong_residual_identities']+=1
    for k in new['interfaces']:need(oa(old['interfaces'][k])==na(new['interfaces'][k]),'Signed whole interface '+k)
    need([oa(x) for x in old.get('unit_factors',[])]==[na(x) for x in new.get('unit_factors',[])],'Signed all native factors')
    need(oa(old['output'])==na(new['output']),'Complete strong final polynomial under substitution')
    counts['complete_signed_DAG_identities']+=1

def ledger(p,counts):
    rows=p['polynomial_source'];source=p['source'];need(rows[:len(source)]==source,'Whole source prefix')
    d={n:1 for n in p['parameters']+p['auxiliaries']};defs={};ops=Counter()
    def deg(x):return d[x] if type(x)is str else 0
    for n,o,a,b in rows:
        need(type(n)is str and n not in d and o in('+','-','*'),'SSA/operator')
        need(all(type(x)is int or (type(x)is str and x in d) for x in(a,b)),'Exact closed gate operands')
        d[n]=deg(a)+deg(b) if o=='*' else max(deg(a),deg(b));defs[n]=(a,b);ops['M' if o=='*' else 'A']+=1
    live=set();stack=[p['output']]
    while stack:
        n=stack.pop()
        if n in defs and n not in live:
            live.add(n);stack.extend(x for x in defs[n] if type(x)is str)
    need(live==set(defs),'Every paid gate live')
    r=dict(operations=len(rows),M=ops['M'],A=ops['A'],degree_upper=d[p['output']],witnesses=len(p['auxiliaries']),comparisons=len(p['comparisons']))
    need(exact(r,p['polynomial_ledger']),'Independent full paid ledger')
    need(p['exact_degree']is None and p['positive_witnesses']==len(p['auxiliaries']),'Domain and exact-degree boundary')
    need(p['operations']==len(source),'Certificate operations')
    need(p['multiplications']==sum(r[1]=='*' for r in source),'Certificate M')
    need(p['additions_subtractions']==sum(r[1]!='*' for r in source),'Certificate A')
    counts['full_live_gate_and_degree_audits']+=1;counts['paid_gates']+=len(rows)
    return r

def run(source,root,weak_receipt,strong_receipt,note=None):
    source,root=Path(source).resolve(),Path(root).resolve();data=pinned(source,SOURCE_SHA)
    for name,h in PARENT_PINS.items():
        path=source.parent/name if (source.parent/name).is_file() else root/name;pinned(path,h)
    receipts={}
    for key,path in (('weak',weak_receipt),('strong',strong_receipt)):
        r=json.loads(pinned(path,RECEIPT_PINS[key]));receipts[key]={(tuple(f['program']),f['unit_product']):f['compiler'] for f in r['forms']}
    if note is not None:pinned(note,NOTE_SHA)
    module=types.ModuleType('_independent_composed205_target');module.__file__=str(source);exec(compile(data,str(source),'exec'),module.__dict__)
    counts=Counter();rows=[];rng=random.Random(1205206)
    def reject(fn):
        try:fn()
        except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1;return
        raise ValueError('Malformed object accepted')
    for key in receipts['weak']:
        program,unit=key;actual=module.build(program,unit_product=unit,root=root);p=normalized(actual);w=receipts['weak'][key];s=receipts['strong'][key]
        need(exact(normalized(module.canonical_parent(actual,root=root)),w),'Complete saved weak descriptor')
        need(exact(normalized(module.canonical_strong(actual,root=root)),s),'Complete saved strong descriptor')
        counts['pinned_parent_descriptor_checks']+=2
        proof_weak(w,p,counts);proof_strong(s,p,counts);r=ledger(p,counts)
        need((w['polynomial_ledger']['M']-r['M'],w['polynomial_ledger']['A']-r['A'])==(1,2),'Whole cost delta weak')
        need((s['polynomial_ledger']['M']-r['M'],s['polynomial_ledger']['A']-r['A'])==(1,0),'Whole cost delta strong')
        need(p['input_cone']==w['input_cone'] and p['scope']==w['scope'],'Preserved weak scope')
        need(p['full_polynomial_identity']is True and p['polynomial_identity_parent']['file']=='grill_tag_native_weak_cone.py' and p['polynomial_identity_parent']['sha256']==PARENT_PINS['grill_tag_native_weak_cone.py'],'Explicit actual identity parent')
        need('weak_cone_rewrite' not in p and p['historical_weak_cone_rewrite']==w['weak_cone_rewrite'],'Archived earlier width provenance')
        need(p['phase_residual_rewrite']['parent_file']=='grill_tag_native_weak_cone.py','Current phase parent')
        need(p['phase_residual_rewrite']['source_rewriter']['sha256']==PARENT_PINS['grill_tag_native_phase_residual206.py'],'Current rewriter pin')
        need(p['composition']['identity_parent']=='weak208' and p['composition']['strong_reference']=='strong206','Distinct composition relations')
        need(p['input_cone']['positive_fiber_bijection']is False and p['input_cone']['width']=='x+Z0','No strong positive-bijection claim')
        removed=set(wr[0] for wr in w['source'])-set(nr[0] for nr in p['source']);removed.add('three_x__0')
        archive={'historical_weak_cone_rewrite','strong_parent_metadata','phase_residual_rewrite','proof_only_phase_formulas'}
        def scan(v):
            if type(v)is dict:
                for x in v.values():scan(x)
            elif type(v)in(tuple,list):
                for x in v:scan(x)
            elif type(v)is str:need(v not in removed,'Stale active register '+v)
        scan({k:v for k,v in p.items() if k not in archive});counts['current_vs_historical_metadata_audits']+=1
        names=p['parameters']+p['auxiliaries']
        for i in range(10):
            signed=i>=5;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in names};pull=dict(v);pull['Z0']-=2*pull['x']
            pe,pv,pr=execute(p,v);we,wv,wr=execute(w,v);se,sv,sr=execute(s,pull)
            need(pv==wv==sv and pr==wr==sr,'Independent full integer diamond')
            need(module.evaluate(actual,v,signed=signed,root=root)==pv,'Public actual output')
            need(module.identity(actual,v,signed=signed,root=root)['residuals']==pr,'Public weak residual proof')
            need(module.diamond_identity(actual,v,signed=signed,root=root)['output']==pv,'Public signed output proof')
            need(module.integer_pullback(actual,v,signed=signed,root=root)==pull,'Public signed map')
            counts['integer_diamonds']+=1;counts['signed_cases']+=signed;counts['numeric_residual_equalities']+=2*len(pr)
            if not signed:
                strong_v=dict(v);mapped=module.strong_to_weak_assignment(actual,strong_v,root=root);need(mapped['Z0']==v['Z0']+2*v['x'] and min(mapped.values())>0 and module.integer_pullback(actual,mapped,root=root)==v,'One-way positive map')
                need(execute(p,mapped)[1:]==execute(s,strong_v)[1:],'Full one-way positive identity');counts['positive_one_way_maps']+=1
        for i in range(2):
            v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in names};pull=dict(v);pull['Z0']-=2*pull['x']
            need(execute(p,v)[1:]==execute(w,v)[1:]==execute(s,pull)[1:],'Independent rational diamond');counts['rational_diamonds']+=1
        ones=dict.fromkeys(names,1);need(module.integer_pullback(actual,ones,root=root)['Z0']==-1,'Inverse not positive');need(execute(p,ones)[1]!=execute(s,ones)[1],'Not same-coordinate strong polynomial');counts['strong_same_coordinate_separations']+=1
        for field in ('source','comparisons','input_cone','phase_residual_rewrite','polynomial_identity_parent','composition','historical_weak_cone_rewrite'):
            bad=copy.deepcopy(actual);bad[field]=None;reject(lambda b=bad:module.checked(b,root=root))
        for typ in (float,bool):
            bad=copy.deepcopy(actual);i,j=next((i,j) for i,r in enumerate(bad['polynomial_source']) for j in(2,3) if type(r[j])is int and (typ is float or r[j]in(0,1)))
            row=list(bad['polynomial_source'][i]);row[j]=typ(row[j]);bad['polynomial_source'][i]=tuple(row)
            huge=dict(ones,x=10**400);reject(lambda b=bad:module.evaluate(b,huge,root=root))
        for name in ('x','Z0'):
            for badvalue in (0,-1,True,1.0,None):reject(lambda n=name,v=badvalue:module.evaluate(actual,dict(ones,**{n:v}),root=root))
        for flag in(0,1,None):reject(lambda f=flag:module.evaluate(actual,ones,signed=f,root=root))
        reject(lambda:module.evaluate(actual,dict(ones,unexpected=1),root=root));reject(lambda:module.evaluate(actual,{'x':1},root=root))
        old=module.canonical_parent(actual,root=root);need(exact(module.rewrite(old,root=root),actual),'Canonical rewrite result')
        old['interfaces']['P0']='x';reject(lambda:module.rewrite(old,root=root));reject(lambda:module.rewrite(module.canonical_strong(actual,root=root),root=root))
        class Foreign(str):pass
        bad=dict(ones);bad[Foreign('x')]=bad.pop('x');reject(lambda:module.evaluate(actual,bad,root=root))
        for getter in (lambda:module.build(program,unit_product=unit,root=root),lambda:module.canonical_parent(actual,root=root),lambda:module.canonical_strong(actual,root=root),lambda:module.polynomial_source(actual,root=root)):
            c=getter();clean=copy.deepcopy(c)
            if type(c)is dict:c['interfaces']['P0']='poison'
            else:c[0]=('poison','+',1,2)
            need(exact(getter(),clean),'Defensive nested copy');counts['copy_isolation_checks']+=1
        rows.append(dict(program=list(program),unit_product=unit,ledger=r))
    for v in ((),[0],(True,),(1.0,),(-1,),None):reject(lambda v=v:module.build(v,root=root))
    # Warm direct-source guards use fresh private copies. Ancestors remain pinned by
    # each parent's _context; the ancestor guard suites are inherited, not rerun.
    with tempfile.TemporaryDirectory(prefix='review205-') as directory:
        directory=Path(directory);child=directory/source.name;child.write_bytes(data)
        copies=[]
        for name,h in PARENT_PINS.items():
            path=source.parent/name if (source.parent/name).is_file() else root/name
            q=directory/name;q.write_bytes(path.read_bytes());copies.append(q)
        private=types.ModuleType('_independent205_private');private.__file__=str(child);exec(compile(data,str(child),'exec'),private.__dict__)
        clean=private.build((0,),root=root)
        for path in copies:
            original=path.read_bytes()
            try:
                path.write_bytes(original+b'\n# independent warm pin probe\n');reject(lambda:private.build((0,),root=root));counts['private_warm_direct_pin_rejections']+=1
            finally:path.write_bytes(original)
            need(exact(private.build((0,),root=root),clean),'Recovered pinned source')
    proc=subprocess.run([sys.executable,'-O',str(source),'--root',str(root)],capture_output=True,text=True,timeout=30)
    need(proc.returncode!=0 and 'Run without -O' in proc.stderr,'Explicit optimized-execution rejection');counts['optimized_mode_rejections']+=1
    return dict(status='PASS_INDEPENDENT_GRILL_COMPOSED205',source_sha256=SOURCE_SHA,parent_source_pins=PARENT_PINS,parent_receipt_pins=RECEIPT_PINS,companion_note_sha256=NOTE_SHA,counts=dict(counts),forms=rows,
      scope='Eight complete frozen forms: exact polynomial identity to weak208, literal width-after-phase commuting schedules, signed substitution to strong206. Strict positive API, all paid gates and upper degrees; no exact-degree or universal-program claim. Parent native/halting theorems and ancestor pin suites are inherited, not re-proved or rerun.')

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--source',required=True,type=Path);a.add_argument('--root',required=True,type=Path);a.add_argument('--weak-receipt',required=True,type=Path);a.add_argument('--strong-receipt',required=True,type=Path);a.add_argument('--note',type=Path);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);a=a.parse_args()
    result=run(a.source,a.root,a.weak_receipt,a.strong_receipt,a.note)
    if a.expect:need(exact(result,json.loads(a.expect.read_text())),'Exact saved independent receipt mismatch')
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
