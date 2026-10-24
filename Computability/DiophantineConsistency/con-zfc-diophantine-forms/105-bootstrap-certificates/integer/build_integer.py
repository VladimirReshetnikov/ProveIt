#!/usr/bin/env python3
"""Generate finite sign-propagation and quartic-domain-conversion certificates.

All identities are independently checked by verify_integer.py. No search for
solutions or assumed consistency is used. Python standard library only.
"""
from pathlib import Path
from collections import Counter
import sys,json,copy
import projection as elim

def need(ok,message):
    if not ok: raise ValueError(message)

def deps(p):
    return set(v for m,c in p.items() for v,n in Counter(m).items() if n%2)

def rules_for(e):
    rules=[]; pairs=[]
    for ri,r in enumerate(e['residuals']):
        p=elim.normalize(r['terms'])
        singles=[m[0] for m in p if len(m)==1 and abs(p[m])==1]
        for v in singles:
            f=elim.candidate(p,v,True)
            if f is not None:
                rules.append({'kind':'nonnegative_polynomial','row':ri,'out':[v],
                    'dependencies':sorted(deps(f)),'polynomial':elim.as_terms(f)})
        for i,x in enumerate(singles):
            for y in singles[i+1:]:
                if p[(x,)]!=p[(y,)]:continue
                f={m:-c*p[(x,)] for m,c in p.items() if m not in [(x,),(y,)]}
                if any(x in m or y in m for m in f):continue
                if any(c<0 for m,c in f.items() if m) or f.get((),0)<-1:continue
                pairs.append({'kind':'centered_pair','row':ri,'out':[x,y],
                    'dependencies':sorted(deps(f)),'sum_polynomial':elim.as_terms(f)})
    rules += quotient_rules(e)
    rules += frame_rules(e)
    return rules,pairs

def frame_rules(e):
    from functools import lru_cache
    rows=[elim.normalize(r['terms']) for r in e['residuals']]
    names={v['name']:i for i,v in enumerate(e['variables'])}
    labels={r['label']:i for i,r in enumerate(e['residuals']) if r['label'] not in ['addition','multiplication']}
    defs={}
    for ri,r in enumerate(e['residuals']):
        if r['label'] not in ['addition','multiplication']:continue
        for m,c in rows[ri].items():
            if len(m)!=1 or c!=1:continue
            v=m[0]
            if e['variables'][v]['kind']!='gate':continue
            f=elim.candidate(rows[ri],v,True)
            if f is not None and all(x<v for mon in f for x in mon):defs[v]=(ri,f)
    def add(p,q,k=1):
        z=dict(p)
        for m,c in q.items():z[m]=z.get(m,0)+k*c
        return {m:c for m,c in z.items() if c}
    def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
    def unfold(p,mode='all',allowed=frozenset()):
        z={}
        for m,c in p.items():
            w={():c}
            for v in m:w=elim.multiply(w,atom(v,mode,allowed))
            z=add(z,w)
            if len(z)>10000:raise ValueError('unfold too large')
        return z
    @lru_cache(None)
    def leaves(v):
        if v not in defs:return frozenset([v])
        return frozenset().union(*(leaves(x) for m in defs[v][1] for x in m))
    @lru_cache(None)
    def atom(v,mode='all',allowed=frozenset()):
        if v not in defs:return {(v,):1}
        f=defs[v][1]
        if mode=='apart' and A not in leaves(v) and elim.degree(f)>1:return {(v,):1}
        if mode=='stop' and v in allowed:return {(v,):1}
        if mode=='affine' and elim.degree(f)>1 and not leaves(v)<=allowed:return {(v,):1}
        return unfold(f,mode,allowed)
    A,W,z=[names['shared.'+s] for s in ['A','W','Zminus1']]
    norm_id=labels['shared.last_norm'];frame_id=labels['shared.frame_definition']
    norm=unfold(rows[norm_id])
    expected=add({(A,A):1,():-1},elim.multiply({(W,W,W,W):1,(W,W,W):2},elim.multiply({(z,):1,():1},{(z,):1,():1})),-1)
    need(norm == expected, 'frame norm mismatch')
    bases=[]
    for label,ri in labels.items():
        if not label.startswith('base') or not label.endswith('.T_definition'):continue
        T=names[label.split('.')[0]+'.T'];p=unfold(rows[ri],'apart')
        n={tuple(x for x in m if x!=A):c//2 for m,c in p.items() if A in m}
        need(all((m.count(A) == 1 and c % 2 == 0 for m, c in p.items() if A in m)), 'sign certificate construction invariant')
        allowed=frozenset(x for m in n for x in m)
        p=unfold(rows[ri],'stop',allowed)
        need(p == add(add(elim.multiply({(A,): 2}, n), {(T,): 1, (): 1}, -1), elim.multiply(n, n), -1), 'sign certificate construction invariant')
        need(all((c >= 0 for c in n.values())), 'sign certificate construction invariant')
        F=unfold(rows[frame_id],'affine')
        need(F.get((W,)) == 1, 'sign certificate construction invariant')
        rhs={m:-c for m,c in F.items() if m!=(W,)}
        need(W not in {x for m in rhs for x in m}, 'sign certificate construction invariant')
        need(all((c >= 0 for c in rhs.values())) and rhs.get((), 0) >= 2, 'sign certificate construction invariant')
        margin=add(rhs,n,-1)
        need(all((c >= 0 for c in margin.values())), ('frame margin', label, margin))
        bases.append((ri,T,n,rhs,margin,allowed))
    result=[]
    for label,ri in labels.items():
        if not label.startswith('pow') or not label.endswith('.power_congruence'):continue
        tag=label.split('.')[0];m=names[tag+'.output'];h=names[tag+'.quotient']
        for br,T,n,rhs,margin,allowed in bases:
            P=unfold(rows[ri],'stop',allowed|frozenset(x for _,_,nn,_,_,_ in bases for mm in nn for x in mm))
            xs=[v for v in names.values() if e['variables'][v]['name'].startswith('index') and e['variables'][v]['name'].endswith('.X') and P.get((v,))==1]
            if len(xs)!=1:continue
            X=xs[0];Y=names[e['variables'][X]['name'][:-1]+'Y']
            expected=add(add(add({(X,):1},elim.multiply({(Y,):1},n)),{tuple(sorted((Y,A))):1,(m,):1},-1),{tuple(sorted((T,h))):1},-1)
            if P!=expected:continue
            dd=deps(rhs)|deps(n)|{A,z,Y,m,T,h}
            need(X not in dd, 'sign certificate construction invariant')
            result.append({'kind':'frame_root_orientation','out':[X],'dependencies':sorted(dd),
              'rows':[norm_id,frame_id,br,ri],'A_index':A,'W_index':W,'z_index':z,
              'Y_index':Y,'m_index':m,'T_index':T,'quotient_index':h,
              'base':elim.as_terms(n),'frame_rhs':elim.as_terms(rhs),
              'frame_margin':elim.as_terms(margin),'unfold_allowed':sorted(allowed)})
    print('frame orientation rules',len(result),flush=True)
    return result

def quotient_rules(e):
    rows=[elim.normalize(r['terms']) for r in e['residuals']]
    defs={}
    for ri,r in enumerate(e['residuals']):
        if r['label'] not in ['addition','multiplication']:continue
        for m,c in rows[ri].items():
            if len(m)!=1 or c!=1:continue
            v=m[0]
            if e['variables'][v]['kind']!='gate':continue
            f=elim.candidate(rows[ri],v,True)
            if f is not None and all(x<v for mon in f for x in mon):defs[v]=(ri,f)
    from functools import lru_cache
    @lru_cache(None)
    def atom(v):
        if v not in defs:return {(v,):1}
        return unfold(defs[v][1])
    def add(p,q,k=1):
        z=dict(p)
        for m,c in q.items():z[m]=z.get(m,0)+k*c
        return {m:c for m,c in z.items() if c}
    def unfold(p):
        z={}
        for m,c in p.items():
            w={():c}
            for v in m:w=elim.multiply(w,atom(v))
            z=add(z,w)
            if len(z)>20000:raise ValueError('unfold too large')
        return z
    labels={r['label']:i for i,r in enumerate(e['residuals']) if r['label'] not in ['addition','multiplication']}
    names={v['name']:i for i,v in enumerate(e['variables'])}
    result=[]
    for label,ri in labels.items():
        if not label.endswith('.digit_division'):continue
        tag=label.split('.')[0]
        h,r,s,o,t=[names[tag+'.'+s] for s in ['high','remainder','rslack','output','oslack']]
        rd,rb=labels[tag+'.remainder_bound'],labels[tag+'.digit_bound']
        D=add(unfold(rows[rd]),{(r,):1,(s,):1,():1})
        Q=add(unfold(rows[rb]),{(o,):1,(t,):1,():1})
        N=add(add(unfold(rows[ri]),elim.multiply(D,add(elim.multiply(Q,{(h,):1}),{(o,):1}))),{(r,):1})
        A=elim.multiply(D,Q);B=add(add(N,elim.multiply(D,{(t,):1})),{(s,):1,():1})
        identity=add(elim.multiply(A,{(h,):1,():1}),B,-1)
        combination=add(add({m:-c for m,c in unfold(rows[ri]).items()},elim.multiply(D,unfold(rows[rb]))),unfold(rows[rd]))
        need(identity == combination, 'sign certificate construction invariant')
        need(all((c >= 0 for c in A.values())) and all((c >= 0 for c in B.values())) and (B.get((), 0) >= 1), 'sign certificate construction invariant')
        dd=deps(A)|deps(B);need(h not in dd, 'sign certificate construction invariant')
        result.append({'kind':'positive_shifted_product','subkind':'binomial_high','out':[h],
          'dependencies':sorted(dd),'rows':[ri,rd,rb],
          'A':elim.as_terms(A),'B':elim.as_terms(B)})
    if 'moduli_product.division' in labels:
        ri=labels['moduli_product.division'];rb=labels['moduli_product.remainder_bound']
        q,d,o,s=[names['moduli_product.'+x] for x in ['quotient','modulus','output','slack']]
        N=add(add(unfold(rows[ri]),{tuple(sorted((d,q))):1}),{(o,):1})
        A={(d,):1};B=add(N,{(s,):1,():1})
        identity=add(elim.multiply(A,{(q,):1,():1}),B,-1)
        need(identity == add({m: -c for m, c in unfold(rows[ri]).items()}, unfold(rows[rb])), 'sign certificate construction invariant')
        need(all((c >= 0 for c in B.values())) and B.get((), 0) >= 1, 'sign certificate construction invariant')
        result.append({'kind':'positive_shifted_product','subkind':'division_quotient','out':[q],
          'dependencies':sorted(deps(A)|deps(B)),'rows':[ri,rb],
          'A':elim.as_terms(A),'B':elim.as_terms(B)})
    print('quotient rules',len(result),flush=True)
    return result

def close(seeds,rules,goal=None):
    known=set(seeds);proof=[]
    while True:
        before=len(known)
        for r in rules:
            if not set(r['out'])<=known and set(r['dependencies'])<=known:
                known.update(r['out']);proof.append(r)
        if len(known)==before or goal is not None and goal<=known:break
    return known,proof

def select(e):
    rules,pairs=rules_for(e)
    allvars=set(range(len(e['variables'])))
    seeds={i for i,v in enumerate(e['variables']) if v['kind']!='gate'}
    need(close(seeds,rules)[0]==allvars,'initial sign closure')
    removed=[]
    # Use a fixed deterministic order; reverse improves preservation of source inputs.
    for v in sorted(seeds,reverse=True):
        k,_=close(seeds-{v},rules)
        if k==allvars:seeds.remove(v);removed.append(v)
    chosen=[]
    for p in sorted(pairs,key=lambda p:(p['row'],p['out'])):
        xs=set(p['out'])
        if not xs<=seeds:continue
        current=rules+chosen
        known,_=close(seeds-xs,current)
        if not set(p['dependencies'])<=known:continue
        known,_=close(seeds-xs,current+[p])
        if known!=allvars:continue
        seeds-=xs;chosen.append(p)
    known,proof=close(seeds,rules+chosen)
    need(known==allvars,'final sign closure')
    print('nongates',sum(v['kind']!='gate' for v in e['variables']),
          'seeds',len(seeds),'pairguards',len(chosen),'guards',len(seeds)+len(chosen),
          'removed',len(removed),'proof',len(proof))
    print('pairnames',[(e['variables'][x]['name'],e['variables'][y]['name']) for p in chosen for x,y in [p['out']]])
    return seeds,chosen,proof

def guarded(e,seeds,pairs,proof):
    g=copy.deepcopy(e);g['domain']='unrestricted integers';g.pop('metrics',None)
    for v in sorted(seeds):
        a,b,c=range(len(g['variables']),len(g['variables'])+3)
        g['variables'] += [{'name':f'sign.{v}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
        g['residuals'].append({'label':f'nonnegative.{v}',
          'terms':elim.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    for p in pairs:
        x,y=p['out'];a,b,c=range(len(g['variables']),len(g['variables'])+3)
        g['variables'] += [{'name':f'pair.{x}.{y}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
        g['residuals'].append({'label':f'nonnegative_pair.{x}.{y}',
          'terms':elim.as_terms({tuple(sorted((x,y))):2,(x,):1,(y,):1,
                               (a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    return g

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--cap',type=int,default=16)
    ar=ap.parse_args();e=json.loads(ar.input.read_text());seeds,pairs,proof=select(e)
    g=guarded(e,seeds,pairs,proof);ar.output.mkdir(parents=True,exist_ok=True)
    (ar.output/'guarded.json').write_bytes(elim.canonical_bytes(g))
    (ar.output/'sign_certificate.json').write_bytes(elim.canonical_bytes({'seeds':sorted(seeds),'pairs':pairs,'proof':proof}))
    z,c,m=elim.optimize(g,max_support=ar.cap)
    v=elim.verify(g,z,c)
    m.update(v)
    for n,obj in [('equation',z),('projection',c),('polynomial',elim.expand(z)),('metrics',m|v)]:
        (ar.output/(n+'.json')).write_bytes(elim.canonical_bytes(obj))
    print(json.dumps(m|v,indent=2))
