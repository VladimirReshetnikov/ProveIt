#!/usr/bin/env python3
"""Finite grammar synthesis modulo register-disjoint atom commutation.

Every production is checked in a trace monoid.  The literal emitted grammar
still concatenates actual source words, so this does not change TM execution
semantics silently.  Changed-source correspondence and binary checks are
separate obligations.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import Bounds,LinearConstraint,milp,linprog
from scipy.sparse import coo_matrix,vstack
from trace_dictionary import load,automaton


def run(args):
    started=time.monotonic();m=load(args.package);fp=m['footprints']
    @cache
    def canonical(w):
        last={};pred=[];children=[[]for _ in w];available=[]
        for i,c in enumerate(w):
            pp={last[r]for r in fp[c]if r in last}
            pred.append(len(pp))
            if not pp:available.append(i)
            for j in pp:children[j].append(i)
            for r in fp[c]:last[r]=i
        out=[]
        while available:
            i=min(available,key=lambda i:(w[i],i));available.remove(i);out.append(w[i])
            for j in children[i]:
                pred[j]-=1
                if pred[j]==0:available.append(j)
        assert len(out)==len(w)
        return ''.join(out)
    @cache
    def prop_ast(i):
        a=m['ast'][i]
        return (0,0,0)if a[0]=='L'else join(prop_ast(a[1]),prop_ast(a[2]))
    def join(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1
    by_ast={int(i):m['names'][int(q)]for q,i in m['source']['sequence_ast_roots'].items()}
    def props(grammar,override):
        @cache
        def pa(i):
            if i in by_ast:return pw(override.get(by_ast[i],by_ast[i]))
            a=m['ast'][i]
            return (0,0,0)if a[0]=='L'else join(pa(a[1]),pa(a[2]))
        @cache
        def pw(w):
            return pa(m['source']['atoms'][m['symbols'][w]]['ast'])if len(w)==1 else join(*(pw(v)for v in grammar.get(w,m['old'].get(w))))
        return pa(m['source']['original_ast']),pw
    original_props,wp=props(m['grammar'],{})
    source_word=m['ax']
    if args.modified_source:
        d=json.loads(args.modified_source.read_text())
        if args.variant:d=(d.get('variants',{})|d.get('anchored_variants',{}))[args.variant]
        source_word=d.get('modified_AX_word',d.get('raw_AX_word'))
    word=m['expand'](source_word);target=canonical(word)
    assert all(m['closed'][c]and m['halt_free'][c]for c in word)
    lines=(args.package/'inputs/semantic.txt').read_text().splitlines()
    n,nr,na=map(int,lines[0].split());allowed={c:int(mask)for c,mask in map(str.split,lines[1+n+nr:])}
    dictionary={}
    def dic_add(f,spelling,mask,prop):
        if prop[1]>args.zero:return
        t=canonical(f)
        for bit in (0,1):
            if mask&(1<<bit):
                key=t,bit
                if key not in dictionary or (prop,len(spelling),spelling)<(dictionary[key][1],len(dictionary[key][0]),dictionary[key][0]):
                    dictionary[key]=(spelling,prop)
    for c,f in m['atoms'].items():dic_add(f,c,allowed[c],wp(c))
    for w in m['fixed']:dic_add(m['expand'](w),w,3,wp(w))
    initial={canonical(m['expand'](w))for w in m['grammar']if w not in m['fixed']}
    vocabulary={t for t,b in dictionary}|initial|{target}
    # Enumerate every factor of length <= length along the ideal automaton.
    levels,edges,preds=automaton(word,fp,args.cap)
    freq=Counter()
    for done in edges:
        frontier={done}
        for length in range(1,args.length+1):
            frontier={v for s in frontier for v,i in edges.get(s,{}).values()}
            if not frontier:break
            if length>1:
                for out in frontier:
                    bits=out^done
                    ss=[]
                    while bits:
                        bit=bits&-bits;ss.append(word[bit.bit_length()-1]);bits^=bit
                    freq[canonical(''.join(ss))]+=1
    vocabulary|={w for w,n in freq.items()if n>=2}
    if args.complements:
        for w in list(initial):
            vocabulary.update(canonical(w[:i])for i in range(1,len(w)))
            vocabulary.update(canonical(w[i:])for i in range(1,len(w)))
    def free(w,bit):return(w,bit)in dictionary
    def needed(w):return len(w)>1 and not(free(w,0)and free(w,1))
    choices={}
    for w in vocabulary:
        if not needed(w):continue
        lev,es,pr=automaton(w,fp,args.cap)
        rows=set()
        for layer in lev[1:-1]:
            for done in layer:
                a=canonical(''.join(c for i,c in enumerate(w)if(done>>i)&1))
                b=canonical(''.join(c for i,c in enumerate(w)if not(done>>i)&1))
                if a in vocabulary and b in vocabulary and(free(a,0)or needed(a))and(free(b,1)or needed(b)):
                    rows.add((w,a,b))
        choices[w]=sorted(rows)
    while True:
        bad={w for w,rows in choices.items()if not rows}
        if not bad:break
        for w in bad:del choices[w]
        for w in choices:choices[w]=[r for r in choices[w]if all(free(v,b)or v in choices for b,v in enumerate(r[1:]))]
    assert target in choices
    words=sorted(choices,key=lambda w:(len(w),w));wi={w:i for i,w in enumerate(words)}
    rules=[r for w in words for r in choices[w]];ri={r:len(words)+i for i,r in enumerate(rules)}
    rankoffset=len(words)+len(rules);nvars=rankoffset+len(words)
    objective=np.zeros(nvars);objective[:len(words)]=1
    low=np.zeros(nvars);high=np.ones(nvars);high[rankoffset:]=args.zero
    low[wi[target]]=1;high[rankoffset+wi[target]]=wp(m['ax'])[0]
    integrality=np.zeros(nvars);integrality[:rankoffset]=1
    rr=[];cc=[];vv=[];lb=[];ub=[]
    def add(terms,l,u):
        i=len(lb)
        for j,value in terms:rr.append(i);cc.append(j);vv.append(value)
        lb.append(l);ub.append(u)
    for w in words:add([(wi[w],-1)]+[(ri[r],1)for r in choices[w]],0,0)
    big=args.zero+1
    for r in rules:
        w,a,b=r
        for bit,ch in enumerate((a,b)):
            if not free(ch,bit):add([(ri[r],1),(wi[ch],-1)],-np.inf,0)
        terms=[(rankoffset+wi[w],1),(ri[r],-big)];lower=1-big
        if free(a,0):lower+=dictionary[a,0][1][0]
        else:terms.append((rankoffset+wi[a],-1))
        add(terms,lower,np.inf)
    # Save the unrestricted objective model before adding a target cutoff.
    objective_row_count=len(lb)
    if args.lp_certificate:
        base_matrix=coo_matrix((vv,(rr,cc)),shape=(len(lb),nvars)).tocsr()
        equal=[i for i,(l,u)in enumerate(zip(lb,ub))if l==u]
        upper=[i for i,(l,u)in enumerate(zip(lb,ub))if l!=u and np.isfinite(u)]
        lower=[i for i,(l,u)in enumerate(zip(lb,ub))if l!=u and np.isfinite(l)]
        lp=linprog(objective,A_ub=vstack([base_matrix[upper],-base_matrix[lower]]).tocsr(),
                   b_ub=np.array([ub[i]for i in upper]+[-lb[i]for i in lower]),
                   A_eq=base_matrix[equal],b_eq=np.array([lb[i]for i in equal]),
                   bounds=list(zip(low,high)),method='highs')
        print('LP',lp.status,lp.fun,lp.message,flush=True)
        if lp.status==0:
            denominator=10**9;dual=[]
            for i,value in zip(equal,lp.eqlin.marginals):
                numerator=round(float(value)*denominator)
                if numerator:dual.append([i,'E',numerator])
            for j,(i,side)in enumerate([(i,'U')for i in upper]+[(i,'L')for i in lower]):
                value=float(lp.ineqlin.marginals[j])*(1 if side=='U'else -1)
                numerator=round(value*denominator)
                if numerator:dual.append([i,side,numerator])
            rows=[[]for _ in lb]
            for i,j,value in zip(rr,cc,vv):rows[i].append([j,int(value)])
            model=dict(columns=nvars,objective=[int(x)for x in objective],
                       low=[int(x)for x in low],high=[int(x)for x in high],
                       rows=rows,lower=[int(x)if np.isfinite(x)else None for x in lb],
                       upper=[int(x)if np.isfinite(x)else None for x in ub],
                       fixed_states=len(m['fixed']),words=words,rules=rules,
                       dictionary=[dict(trace=t,bit=b,spelling=s,properties=p)for(t,b),(s,p)in sorted(dictionary.items())],
                       target=target,zero=args.zero,
                       scope='This explicitly serialized finite trace-grammar universe, fixed dictionary and fixed51 grammar rows')
            residual=[denominator*x for x in model['objective']];bound=0
            for i,side,numerator in dual:
                assert side=='E'or(side=='U'and numerator<=0)or(side=='L'and numerator>=0)
                rhs=model['upper'][i]if side=='U'else model['lower'][i]
                bound+=numerator*rhs
                for j,value in rows[i]:residual[j]-=numerator*value
            bound+=sum(r*(l if r>=0 else h)for r,l,h in zip(residual,model['low'],model['high']))
            certificate=dict(denominator=denominator,dual=dual,lower_bound_numerator=bound,
                             lower_bound_decimal=bound/denominator,
                             integer_private_lower_bound=-((-bound)//denominator),
                             grammar_lower_bound=len(m['fixed'])-((-bound)//denominator))
            import gzip,hashlib
            blob=json.dumps(model,separators=(',',':')).encode()
            modelpath=args.output.with_suffix('.lp_model.json.gz')
            modelpath.write_bytes(gzip.compress(blob,mtime=0))
            certificate['model_uncompressed_sha256']=hashlib.sha256(blob).hexdigest()
            args.output.with_suffix('.lp_certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
            print('EXACT_BOUND',certificate['lower_bound_decimal'],certificate['grammar_lower_bound'],flush=True)
        if args.lp_only:return
    add([(wi[w],1)for w in words],-np.inf,args.target-len(m['fixed']))
    matrix=coo_matrix((vv,(rr,cc)),shape=(len(lb),nvars)).tocsc()
    report=dict(status='START',trace_ideals=sum(map(len,levels)),target_grammar=args.target,
                words=len(words),productions=len(rules),variables=nvars,constraints=len(lb),
                fixed_states=len(m['fixed']),dictionary_semantic_entries=len({t for t,b in dictionary}),
                factor_limit=args.length,variant=args.variant,setup_seconds=time.monotonic()-started)
    print(json.dumps(report),flush=True)
    result=milp(c=objective,integrality=integrality,bounds=Bounds(low,high),
                constraints=LinearConstraint(matrix,np.array(lb),np.array(ub)),
                options={'time_limit':args.seconds,'mip_rel_gap':0})
    report.update(status=int(result.status),message=result.message,elapsed_seconds=time.monotonic()-started)
    for key in('fun','mip_gap','mip_node_count','mip_dual_bound'):
        value=getattr(result,key,None)
        if value is not None:report[key]=float(value)
    if result.x is not None:
        selected={w:(a,b)for w,a,b in rules if result.x[ri[w,a,b]]>.5}
        emitted={w:m['grammar'][w]for w in m['fixed']}
        semantic_certificate=[]
        @cache
        def emit(t):
            a,b=selected[t]
            x=dictionary[a,0][0]if free(a,0)else emit(a)
            y=dictionary[b,1][0]if free(b,1)else emit(b)
            w=x+y
            assert canonical(m['expand'](w))==t
            if w in emitted:assert emitted[w]==(x,y)
            emitted[w]=(x,y);semantic_certificate.append(dict(trace=t,actual_fine=m['expand'](w),coarse=w,left=x,right=y))
            return w
        newax=emit(target);pr,_=props(emitted,{m['ax']:newax})
        report.update(candidate_rules=len(emitted),coarse_calls=len(newax),properties=pr,
                      exact_fine_word_equality=m['expand'](newax)==word,
                      exact_trace_equality=canonical(m['expand'](newax))==canonical(word))
        out=dict(m['seed']);out.update(status='TRACE_EQUIVALENT_SOURCE_GRAMMAR_ONLY',
              rules_count=len(emitted),rules=[[w,*emitted[w]]for w in sorted(emitted)],
              roots=sorted((set(m['seed']['roots'])-{m['ax']})|{newax}),
              properties=pr,modified_AX_word=newax,original_AX_word=m['ax'],
              desired_AX_word=source_word,short_scan=True,framework_states=117,
              trace_certificate=semantic_certificate,search_report=report,
              no_machine_claim=True)
        args.output.write_text(json.dumps(out,indent=2)+'\n')
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--length',type=int,default=20);p.add_argument('--target',type=int,default=127)
    p.add_argument('--zero',type=int,default=6);p.add_argument('--seconds',type=float,default=120)
    p.add_argument('--cap',type=int,default=1000000);p.add_argument('--complements',action='store_true')
    p.add_argument('--modified-source',type=Path);p.add_argument('--variant',default='')
    p.add_argument('--lp-certificate',action='store_true');p.add_argument('--lp-only',action='store_true')
    assert __debug__;run(p.parse_args())
