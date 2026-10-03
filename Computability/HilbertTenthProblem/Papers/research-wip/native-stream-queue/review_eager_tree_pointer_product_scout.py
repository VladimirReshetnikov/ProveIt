"""Independent bounded audit of the natural pointer-product Tree projection."""
import argparse, copy, hashlib, json, math, random, subprocess, sys, tempfile, types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:
    raise RuntimeError('Run without -O')
PINS = {
 'eager_tree_pointer_product_scout.py': '35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd',
 'eager_tree_pointer_product_scout.json': '9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc',
 'eager_tree_pointer_product_scout.md': 'c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3',
 'eager_tree_coded_lookup_scout.py': 'b2769ca2c8b8754f5b5c9d65c0ad97a5f590c5b6ebc5712a2964ac1d1a1d0e73',
 'eager_tree_coded_lookup_scout.json': 'acfcbd04609e49150a0e9089c7937ca0fcd20b852a337a3e39248a4e582d01c6',
 'eager_tree_coded_lookup_scout.md': '81d9be0663b212039802c1c841dd200e82baedc02ecf1005957e8f90beef457b',
}
def check(ok, msg):
    if not ok: raise AssertionError(msg)
def exact(a,b):
    return type(a) is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a) is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a) in (list,tuple) else a==b)
def sha(b): return hashlib.sha256(b).hexdigest()
def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def evaluate(rows, values):
    e=dict(values)
    for n,op,a,b in rows:
        a=e[a] if type(a) is str else a; b=e[b] if type(b) is str else b
        e[n] = {'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
    return e

def ancestors(rows, ports):
    definitions={r[0]:r[2:] for r in rows}; used=set(); stack=list(ports)
    while stack:
        n=stack.pop()
        if type(n) is str and n not in used:
            used.add(n); stack.extend(definitions.get(n,()))
    return used

def reconstruct(parent):
    n=parent['N']; rows=parent['source']; defs={r[0]:r for r in rows}
    removed=set(8*i+j for i in range(n) for j in (5,6,7))|set(range(8*n+3,11*n+3))
    keep=[i for i in range(len(parent['residuals'])) if i not in removed]
    residuals=[parent['residuals'][i] for i in keep]; new=[]; slots=[]; active=[]
    for i in range(n):
        a=defs[parent['residuals'][8*i+5]][3]
        check(defs[a][1:]==['+',f'r{i}_t3',f'r{i}_t4'], 'actual shared active port')
        check(defs[parent['residuals'][8*i+6]][3]==a and defs[parent['residuals'][8*i+7]][3]==f'r{i}_t3','three active ports')
        active.extend([a,a,f'r{i}_t3'])
    counter=0
    def emit(op,a,b):
        nonlocal counter
        name=f'pointer_product_{counter}'; counter+=1; new.append([name,op,a,b]); return name
    for k,m in enumerate(parent['lookup_map']):
        i,s=divmod(k,3); check((m['row'],m['slot'])==(i,s),'ordered complete slot map')
        ds=[emit('-',parent['row_code_ports'][str(j)],m['target_port']) for j in range(i+1,n)]
        if ds:
            acc=ds[0]
            for d in ds[1:]: acc=emit('*',acc,d)
            port=emit('*',active[k],acc)
        else: port=active[k]
        residuals.append(port)
        slots.append(dict(row=i,slot=s,parent_lookup_port=m['child_port'],child_port=port,active_port=active[k],target_port=m['target_port'] if ds else None,difference_ports=ds))
    needed=ancestors(rows+new,residuals)
    core=[r for r in rows+new if r[0] in needed]
    final=copy.deepcopy(core)
    for i,r in enumerate(residuals): final.append([f'product_square_{i}','*',r,r])
    out='product_square_0'
    for i in range(1,len(residuals)):
        nxt=f'product_sum_{i}';final.append([nxt,'+',out,f'product_square_{i}']);out=nxt
    pointers=[f'r{i}_p{s}_{j}' for i in range(n) for s in range(3) for j in range(i+1,n)]
    vacuous=[f'r{n-1}_u',f'r{n-1}_v']; free=[x for x in parent['free'] if x not in pointers+vacuous]
    return dict(source=core,polynomial_source=final,output=out,residuals=residuals,free=free,slot_map=slots,removed_pointer_coordinates=pointers,removed_vacuous_coordinates=vacuous,retained_parent_residual_indices=keep,removed_parent_residual_indices=sorted(removed))

def ledger(rows,free,outputs):
    degrees=dict.fromkeys(free,1); count=Counter()
    for row in rows:
        check(type(row) is list and len(row)==4,'binary source rows')
        name,op,a,b=row;check(type(name) is str and name not in degrees and op in ('+','-','*'),'fresh paid register')
        for x in (a,b):check(type(x) is int or type(x) is str and x in degrees,'exact closed operands')
        da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0
        degrees[name]=da+db if op=='*' else max(da,db);count[op]+=1
    live=ancestors(rows,outputs); check(set(degrees)<=live,'all supplied registers and paid gates live')
    return dict(M=count['*'],A=count['+']+count['-'],operations=len(rows),degree_upper_bound=max(degrees[o] for o in outputs),all_live=True)

# Sparse coefficient algebra is used for the bounded degree-five code cones.
def plus(a,b,sgn=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sgn*c
    return {m:c for m,c in r.items() if c}
def times(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items() if c}
def atom(x):return {(x,):1} if type(x) is str else ({():x} if x else {})
def expand(rows,free):
    env={x:atom(x) for x in free}
    for n,o,a,b in rows:
        a=env[a] if type(a) is str else atom(a);b=env[b] if type(b) is str else atom(b)
        env[n]=times(a,b) if o=='*' else plus(a,b,1 if o=='+' else -1)
    return env
def pair(a,b):s=plus(a,b);return plus(times(s,s),a)
def triple(x,y,z):return pair(z,pair(x,y))
def homogeneous(p,d):return {m:c for m,c in p.items() if len(m)==d}
def power(a,k):
    p={():1}
    for _ in range(k):p=times(p,a)
    return p

def univariate(rows,free):
    env={x:[0,1] for x in free}
    for name,op,a,b in rows:
        a=env[a] if type(a) is str else [a];b=env[b] if type(b) is str else [b]
        r=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
        if op=='*':
            for i,x in enumerate(a):
                for j,y in enumerate(b):r[i+j]+=x*y
        else:
            for i,x in enumerate(a):r[i]+=x
            for i,x in enumerate(b):r[i]+=x if op=='+' else -x
        while len(r)>1 and r[-1]==0:r.pop()
        env[name]=r
    return env

# Independent eager Tree evaluation from the five source equations.
def F(a,b):return (a+b)*(a+b+1)+2*b+2
def parse(x):
    if x==0:return (0,)
    if x%2:return (1,(x-1)//2)
    q=(x-2)//2;s=(math.isqrt(8*q+1)-1)//2;b=q-s*(s+1)//2
    return (2,s-b,b)
def derivation(x,y):
    records={};running=set()
    def go(x,y):
        if (x,y) in records:return records[x,y]['z']
        check((x,y) not in running and len(records)+len(running)<100,'finite fixture')
        running.add((x,y));a=b=c=u=v=0;children=[];code=parse(x)
        if code[0]==0:tag=0;z=2*y+1
        elif code[0]==1:tag=1;a=code[1];z=F(a,y)
        else:
            g,b=code[1:];inner=parse(g)
            if inner[0]==0:tag=2;z=b
            elif inner[0]==1:
                tag=3;a=inner[1];u=go(b,y);v=go(a,y);z=go(u,v);children=[(b,y),(a,y),(u,v)]
            else:
                tag=4;a,b0=inner[1:];c=b;b=b0;u=go(y,a);z=go(u,b);children=[(y,a),(u,b)]
        records[x,y]=dict(x=x,y=y,z=z,a=a,b=b,c=c,u=u,v=v,tag=tag,children=children);running.remove((x,y));return z
    z=go(x,y);post=[];seen=set()
    def dfs(key):
        if key in seen:return
        seen.add(key)
        for sub in records[key]['children']:dfs(sub)
        post.append(key)
    dfs((x,y));return z,records,list(reversed(post))
def parent_assignment(parent,records,keys,external):
    lookup={k:i for i,k in enumerate(keys) if k is not None};e={}
    for i,k in enumerate(keys):
        r=records[k] if k is not None else dict(x=0,y=0,z=1,a=0,b=0,c=0,u=0,v=0,tag=0,children=[])
        for f in ('x','y','z','a','b','c','u','v'):e[f'r{i}_{f}']=r[f]
        for t in range(5):e[f'r{i}_t{t}']=int(t==r['tag'])
        for s in range(3):
            for j in range(i+1,len(keys)):e[f'r{i}_p{s}_{j}']=int(s<len(r['children']) and lookup[r['children'][s]]==j)
    e.update(zip(('program','argument','output'),external));return {k:e[k] for k in parent['free']}
def chosen_lift(old,child,v):
    out=dict(v);out.update({x:0 for x in child['removed_pointer_coordinates']+child['removed_vacuous_coordinates']});env=evaluate(old['source'],out)
    for m in old['lookup_map']:
        i,s=m['row'],m['slot'];active=out[f'r{i}_t3']+(out[f'r{i}_t4'] if s<2 else 0)
        check(active in (0,1),'natural onehot active')
        if active:
            choices=[j for j in range(i+1,old['N']) if env[old['row_code_ports'][str(j)]]==env[m['target_port']]]
            check(choices,'active product has a natural target');out[f'r{i}_p{s}_{choices[0]}']=1
    return out

def verify(source,root):
    source=Path(source).resolve();root=Path(root).resolve();data={}
    for name,pin in PINS.items():
        path=source.parent/name if name.startswith('eager_tree_pointer_product_scout.') else root/name
        b=path.read_bytes();check(sha(b)==pin,'authenticate before execute: '+name);data[name]=b
    check(source.name=='eager_tree_pointer_product_scout.py','named source interface')
    mod=types.ModuleType('reviewed_pointer_product');mod.__file__=str(source);exec(compile(data[source.name],str(source),'exec'),mod.__dict__)
    parent_saved=json.loads(data['eager_tree_coded_lookup_scout.json']);saved=json.loads(data['eager_tree_pointer_product_scout.json'])
    olds={(p['N'],p['cleanup']):p for p in parent_saved['selected_full_packets'] if p['mode']=='gated' and p['algebra'] and p['order']==[2,0,1]}
    check(set(olds)=={(n,c) for n in range(1,9) for c in (False,True)},'all sixteen actual parents')
    stored={(f['packet']['N'],f['packet']['cleanup']):f for f in saved['forms']};check(set(stored)==set(olds),'all sixteen saved child forms')
    counts=Counter();forms=[];packets={};rng=random.Random(47013)
    for key,old in sorted(olds.items()):
        n,c=key;p=mod.build(n,cleanup=c,root=root);packets[key]=p;expected=reconstruct(old)
        check(exact(p,stored[key]['packet']),'public packet agrees with saved full source')
        for field,value in expected.items():check(exact(p[field],value),'independent full reconstruction: '+field)
        for name,rows,outs in [('certificate_ledger',p['source'],p['residuals']),('polynomial_ledger',p['polynomial_source'],[p['output']])]:check(exact(ledger(rows,p['free'],outs),p[name]),'independent complete live paid ledger')
        M=(3*n*n+81*n-24)//2;A=(3*n*n+(131-2*int(c))*n-38)//2
        check((p['polynomial_ledger']['M'],p['polynomial_ledger']['A'])==(M,A),'general paid formula')
        check(old['polynomial_ledger']['M']-M==3*n+13 and old['polynomial_ledger']['A']-A==3*n*(n+1)//2+26,'independent old/new saving decomposition')
        check(p['witnesses']==len(p['free'])-3==13*n-2 and p['residual_count']==len(p['residuals'])==8*n+3,'witness/residual formulas')
        check(p['full_polynomial_identity'] is False and p['natural_existential_projection'] is True and p['zero_fiber_bijection'] is False,'current semantic metadata')
        check(exact(p['parent_pins'],{k:v for k,v in PINS.items() if k.startswith('eager_tree_coded')}),'authentic current parent metadata')
        common=[old['residuals'][i] for i in p['retained_parent_residual_indices']]
        check(not(set(p['removed_pointer_coordinates']+p['removed_vacuous_coordinates'])&ancestors(old['source'],common)),'all deleted fields absent from common residual cones')
        ep=expand(old['source'],old['free'])
        for j,port in old['row_code_ports'].items():
            fields=[atom(f'r{j}_{k}') for k in ('x','y','z')];check(ep[port]==triple(*fields),'actual row code polynomial');counts['row_code_polynomials']+=1
        for m in old['lookup_map']:
            i,s=m['row'],m['slot'];a,b,y,u,v,z=[atom(f'r{i}_{k}') for k in ('a','b','y','u','v','z')];t3=atom(f'r{i}_t3');t4=atom(f'r{i}_t4')
            targets=[plus(times(t3,triple(b,y,u)),times(t4,triple(y,a,u))),plus(times(t3,triple(a,y,v)),times(t4,triple(u,b,z))),times(t3,triple(u,v,z))]
            check(ep[m['target_port']]==targets[s],'actual paid target code polynomial');counts['target_code_polynomials']+=1
        # Leading form of root slot2: C_j is degree4; its target is degree5.
        if n>1:
            port=old['lookup_map'][2]['target_port'];want=times(atom('r0_t3'),power(plus(atom('r0_u'),atom('r0_v')),4))
            check(homogeneous(ep[port],5)==want,'exact nonzero root third target leader')
        else:check(ep[old['residuals'][1]].get(tuple(sorted(['r0_t4']+['r0_a']*4)))==-1,'N1 unchanged degree5 input leader')
        uni=univariate(p['polynomial_source'],p['free'])[p['output']];degree=max(10,10*n-8)
        check(len(uni)-1==degree==p['exact_degree'] and uni[-1]>0,'full exact attained degree')
        check(stored[key]['degree_specialization']['coefficient_sha256']==sha(canonical(uni)),'saved degree coefficients independently reproduced')
        for case in range(8):
            v={x:rng.randrange(-3,5) for x in old['free']}
            if case>=6:v={x:Fraction(a,3) for x,a in v.items()};counts['rational_full_corrections']+=1
            nv={x:v[x] for x in p['free']};before=evaluate(old['polynomial_source'],v);after=evaluate(p['polynomial_source'],nv)
            correction=sum(after[m['child_port']]**2 for m in p['slot_map'])-sum(before[old['residuals'][i]]**2 for i in p['removed_parent_residual_indices'])
            check(after[p['output']]-before[old['output']]==correction,'whole offzero correction with arbitrary removed coordinates')
            check(all(before[r]==after[r] for r in common),'all retained residual values');counts['retained_residual_values']+=len(common);counts['whole_corrections']+=1
        counts['complete_sources']+=1;counts['paid_gates']+=len(p['polynomial_source']);counts['complete_finalizers']+=1;counts['exact_degrees']+=1
        forms.append(dict(N=n,cleanup=c,M=M,A=A,witnesses=p['witnesses'],residuals=p['residual_count'],degree=degree,full_source_sha256=sha(canonical(p['polynomial_source'])),univariate_sha256=sha(canonical(uni)),leading_coefficient=uni[-1]))
    fixtures=[];tags=set();last_valid=None
    for x,y in [(0,0),(0,3),(1,2),(3,1),(2,5),(F(0,3),1),(4,0),(8,0),(10,0),(12,0),(18,1),(20,2)]:
        z,records,keys=derivation(x,y);tags.add(records[x,y]['tag'])
        for n in sorted(set([len(keys),len(keys)+1,8])):
            if n>8:continue
            padded=keys+[None]*(n-len(keys))
            for c in (False,True):
                old=olds[n,c];p=packets[n,c];v=parent_assignment(old,records,padded,(x,y,z));check(evaluate(old['polynomial_source'],v)[old['output']]==0,'own true parent fixture')
                nv={k:v[k] for k in p['free']};check(evaluate(p['polynomial_source'],nv)[p['output']]==0,'own complete projection')
                lift=chosen_lift(old,p,nv);check(evaluate(old['polynomial_source'],lift)[old['output']]==0,'own complete chosen lift')
                check(exact(mod.project_zero(p,v,root=root),nv) and exact(mod.restore_zero(p,nv,root=root),lift),'public maps agree with independent maps')
                check({k:lift[k] for k in p['free']}==nv,'right inverse on child zeros');counts['genuine_zero_projections']+=1;counts['genuine_zero_lifts']+=1
                last_valid=(p,nv,old,v)
            fixtures.append(dict(program=x,argument=y,output=z,N=n,root_tag=records[x,y]['tag']))
    check(tags==set(range(5)),'own genuine fixtures cover all five source rules')
    nf=saved['nonunique_zero_fixture'];n=nf['N'];old=olds[n,True];p=packets[n,True];v,w=nf['first_parent'],nf['second_parent']
    check(v!=w and all(evaluate(old['polynomial_source'],a)[old['output']]==0 for a in (v,w)),'literal two different natural parent zeros')
    nv={k:v[k] for k in p['free']};check(nv=={k:w[k] for k in p['free']}==nf['child'],'same retained tuple for distinct pointer witnesses');counts['nonunique_parent_examples']+=1
    changed=dict(v);changed[f'r{n-1}_u']=29;changed[f'r{n-1}_v']=41
    check(evaluate(old['polynomial_source'],changed)[old['output']]==0 and {k:changed[k] for k in p['free']}==nv,'independent last-port nonuniqueness');counts['nonunique_parent_examples']+=1
    def reject(fn):
        try:fn()
        except (ValueError,KeyError,TypeError):counts['rejected_calls']+=1
        else:raise AssertionError('malformed public call accepted')
    for bad in (True,False,0,-1,9,1.0,'2',None):reject(lambda bad=bad:mod.build(bad,root=root))
    for bad in (0,1,False if False else None,'true'):reject(lambda bad=bad:mod.build(1,cleanup=bad,root=root))
    p,nv,old,v=last_valid
    for key in p:
        bad=copy.deepcopy(p);bad.pop(key);reject(lambda bad=bad:mod.checked(bad,root=root))
    for field in ('cleanup','witnesses','full_polynomial_identity','natural_existential_projection','zero_fiber_bijection'):
        bad=copy.deepcopy(p);bad[field]=int(bad[field]) if type(bad[field]) is bool else True;reject(lambda bad=bad:mod.checked(bad,root=root))
    for fn,values in ((mod.restore_zero,nv),(mod.project_zero,v)):
        for badval in (True,1.0,Fraction(1),-1):
            bad=dict(values);bad['program']=badval;reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
        bad=dict(values);bad.pop('program');reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
        bad=dict(values);bad['foreign']=0;reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
        bad=dict(values);bad['output']+=1;reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
    for key,value in p.items():
        if type(value) in (list,dict):
            returned=mod.build(p['N'],cleanup=p['cleanup'],root=root);returned[key].clear();check(exact(mod.build(p['N'],cleanup=p['cleanup'],root=root),p),'fresh copies include all mutable metadata: '+key);counts['returned_mutable_copy_checks']+=1
    returned=mod.build(p['N'],cleanup=p['cleanup'],root=root);returned['parent_pins']['eager_tree_coded_lookup_scout.py']='forged';check(exact(mod.checked(p,root=root),p),'nested pin metadata must not alias executable state');counts['returned_mutable_copy_checks']+=1
    for fn,values in ((mod.restore_zero,nv),(mod.project_zero,v)):
        before=copy.deepcopy(values);result=fn(p,values,root=root);result['program']+=100;check(values==before,'map returns distinct assignment copy');counts['map_copy_checks']+=1
    with tempfile.TemporaryDirectory(prefix='independent_tree_product_pins_') as d:
        d=Path(d)
        for name,b in data.items():
            if name.startswith('eager_tree_coded'):(d/name).write_bytes(b)
        check(exact(mod.build(2,root=d),packets[2,True]),'portable parent copy')
        for name in [k for k in PINS if k.startswith('eager_tree_coded')]:
            b=(d/name).read_bytes();(d/name).write_bytes(b+b' ')
            for fn in (lambda:mod.build(2,root=d),lambda:mod.checked(p,root=d),lambda:mod.restore_zero(p,nv,root=d),lambda:mod.project_zero(p,v,root=d)):reject(fn);counts['warm_pin_rejections']+=1
            (d/name).write_bytes(b)
    proc=subprocess.run([sys.executable,'-O',str(source)],capture_output=True,text=True,timeout=20);check(proc.returncode!=0 and 'Run without -O' in proc.stderr,'explicit optimized Python rejection');counts['optimized_rejections']+=1
    # Exact recursive receipt equality is essential: bool/int aliases do not pass.
    check(not exact({'x':1},{'x':True}) and not exact([1],[1.0]),'review receipt typed equality')
    return dict(status='PASS_INDEPENDENT_TREE_POINTER_PRODUCT',pins=PINS,counts=dict(sorted(counts.items())),forms=forms,genuine_fixtures=fixtures,scope='Independent literal complete-source reconstruction and bounded16-form audit, with general natural existential-projection/count/degree proof in companion note. No author verifier or historical source executed; no signed zero-equivalence or fixed-arity universality claim.')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',required=True,type=Path);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();result=verify(a.source,a.root)
    if a.expect:check(exact(result,json.loads(a.expect.read_text())),'full exact typed review receipt')
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(result['status'],result['counts'])
if __name__=='__main__':main()
