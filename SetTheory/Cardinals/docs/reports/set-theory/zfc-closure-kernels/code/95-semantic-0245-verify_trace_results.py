#!/usr/bin/env python3
"""Standard-library audit of source reorderings and exact LP certificates.

No optimizer, floating-point decision, or third-party Python package is used.
The source endpoint asserted is a closed-atom trace equivalence.  There is no
new binary-machine endpoint in this verifier.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import gzip
import hashlib
import json
from pathlib import Path
from trace_dictionary import load


def projections(w,footprints):
    return tuple(''.join(c for c in w if r in footprints[c])for r in range(9))


def canonical(w,footprints):
    # Independent implementation: each register carries its own occurrence queue.
    queues=[[i for i,c in enumerate(w)if r in footprints[c]]for r in range(9)]
    positions=[0]*9;done=set();out=[]
    while len(done)<len(w):
        candidates={q[positions[r]]for r,q in enumerate(queues)if positions[r]<len(q)}
        available=[i for i in candidates if all(queues[r][positions[r]]==i for r in footprints[w[i]])]
        assert available
        i=min(available,key=lambda j:(w[j],j));done.add(i);out.append(w[i])
        for r in footprints[w[i]]:positions[r]+=1
    return ''.join(out)


def split_ideals(w,footprints):
    # This directly enumerates order ideals by a bitset closure condition.
    predecessors=[];last={}
    for i,c in enumerate(w):
        pp={last[r]for r in footprints[c]if r in last}
        predecessors.append(sum(1<<j for j in pp))
        for r in footprints[c]:last[r]=i
    active={0};finish=(1<<len(w))-1
    while active:
        nxt=set()
        for done in active:
            if done not in(0,finish):yield done
            # The least unread position of every register suffices.
            seen_regs=set();candidates=[]
            for i,c in enumerate(w):
                if done>>i&1:continue
                if any(r not in seen_regs for r in footprints[c]):candidates.append(i)
                seen_regs.update(footprints[c])
                if len(seen_regs)==9:break
            for i in candidates:
                if predecessors[i]&done==predecessors[i]:nxt.add(done|(1<<i))
        active=nxt


def source_properties(m,grammar=None,overrides=None):
    ast=m['ast'];by_ast={int(i):m['names'][int(q)]for q,i in m['source']['sequence_ast_roots'].items()}
    grammar=m['grammar']if grammar is None else grammar
    overrides={}if overrides is None else overrides
    def join(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1
    @cache
    def pa(i):
        if i in by_ast:return pw(overrides.get(by_ast[i],by_ast[i]))
        a=ast[i]
        return(0,0,0)if a[0]=='L'else join(pa(a[1]),pa(a[2]))
    @cache
    def pw(w):
        return pa(m['source']['atoms'][m['symbols'][w]]['ast'])if len(w)==1 else join(*(pw(c)for c in grammar.get(w,m['old'].get(w))))
    return pw


def independent_graph(word,footprints):
    queues=[[i for i,c in enumerate(word)if r in footprints[c]]for r in range(9)]
    # A state records the number of completed occurrences on each register.
    initial=(0,)*9;positions={initial:0};pending=[initial];graph={};levels={0:[0]}
    while pending:
        state=pending.pop();done=positions[state]
        candidates={q[state[r]]for r,q in enumerate(queues)if state[r]<len(q)}
        edges={}
        for i in candidates:
            c=word[i]
            if not all(queues[r][state[r]]==i for r in footprints[c]):continue
            target=tuple(v+int(r in footprints[c])for r,v in enumerate(state))
            out=done|(1<<i);assert c not in edges;edges[c]=(out,i)
            if target not in positions:
                positions[target]=out;pending.append(target);levels.setdefault(out.bit_count(),[]).append(out)
            else:assert positions[target]==out
        graph[done]=edges
    assert graph[(1<<len(word))-1]=={}
    return graph,levels


def check_source_reordering(path,m):
    r=json.loads(path.read_text());old=r['source_AX_fine_word'];fp=m['footprints']
    assert old==m['expand'](r['source_AX_coarse_word'])
    assert all(m['closed'][c]and m['halt_free'][c]and fp[c]for c in old)
    graph,levels=independent_graph(old,fp);finish=(1<<len(old))-1
    counts={0:1}
    for k in range(len(old)):
        for state in levels[k]:
            for target,i in graph[state].values():counts[target]=counts.get(target,0)+counts[state]
    results=[]
    for name,record in r['results'].items():
        new=record['fine_word'];order=record['occurrence_order']
        assert sorted(order)==list(range(len(old)))
        assert new==''.join(old[i]for i in order)
        assert Counter(old)==Counter(new)and projections(old,fp)==projections(new,fp)
        assert m['expand'](record['coarse_word'])==new
        assert ''.join(chunk['word']for chunk in record['chunks'])==new
        assert len(record['chunks'])==record['dictionary_calls']
        potentials={int(s,16):v for s,v in record['distance_certificate'].items()}
        assert set(potentials)==set(graph)and potentials[finish]==0
        assert potentials[0]==record['dictionary_calls']
        dictionary=set(m['atoms'].values())
        if name=='fixed_core_dictionary':dictionary|={m['expand'](w)for w in m['fixed']}
        else:assert name=='coarse_atoms'
        assert all(chunk['word']in dictionary for chunk in record['chunks'])
        assert all(m['expand'](chunk['spelling'])==chunk['word']for chunk in record['chunks'])
        inequalities=0
        for state,edges in graph.items():
            for token in dictionary:
                target=state
                for c in token:
                    if c not in graph[target]:break
                    target=graph[target][c][0]
                else:
                    assert potentials[state]<=1+potentials[target]
                    inequalities+=1
        assert len(graph)==record['ideals']
        results.append(dict(name=name,calls=record['dictionary_calls'],trace_equivalence=True,
                            exact_minimum_verified=True,potential_inequalities=inequalities))
    return dict(status='SOURCE_TRACE_CERTIFICATES_PASS',results=results,
                independently_recounted_ideals=len(graph),edges=sum(map(len,graph.values())),
                distinct_linearizations=str(counts[finish]))


def check_positive_control(path,m,modelpath=None):
    """Audit a source grammar upper bound without claiming a binary TM theorem."""
    data=json.loads(path.read_text());rules={w:(a,b)for w,a,b in data['rules']}
    assert len(rules)==len(data['rules'])==data['rules_count']==128
    assert all(rules[w]==m['grammar'][w]for w in m['fixed'])
    lines=(m['package']/'inputs/semantic.txt').read_text().splitlines()
    n,nr,na=map(int,lines[0].split());allowed={c:int(mask)for c,mask in map(str.split,lines[1+n+nr:])}
    for w,(a,b)in rules.items():
        assert w==a+b and a and b
        for bit,c in enumerate((a,b)):
            assert c in rules if len(c)>1 else c in m['symbols']and allowed[c]&(1<<bit)
    newax=data['modified_AX_word'];assert data['original_AX_word']==m['ax']
    assert m['expand'](newax)==m['expand'](m['ax'])
    assert set(data['roots'])==(set(m['seed']['roots'])-{m['ax']})|{newax}
    assert data['routes']==m['seed']['routes']
    pw=source_properties(m,rules,{m['ax']:newax})
    assert all(pw(w)[1]<=6 for w in rules)
    assert pw(newax)[0]<=source_properties(m)(m['ax'])[0]
    assert tuple(data['properties'])==pw(m['names'][96])==(3,6,51)
    # The model counts one selected production per nonfree semantic word.
    # Match every private concrete rule back to that exact serialized model.
    if modelpath is not None:
        model=json.loads(gzip.decompress(modelpath.read_bytes()))
        productions={tuple(row)for row in model['rules']};dictionary={(d['trace'],d['bit'])for d in model['dictionary']}
        private={w:ab for w,ab in rules.items()if w not in m['fixed']};assert len(private)==77
        semantic={canonical(m['expand'](w),m['footprints']):w for w in private}
        assert len(semantic)==77
        for t,w in semantic.items():
            a,b=rules[w];ta,tb=(canonical(m['expand'](c),m['footprints'])for c in(a,b))
            assert(t,ta,tb)in productions
            assert all((v,bit)in dictionary or v in semantic for bit,v in enumerate((ta,tb)))
        assert canonical(m['expand'](newax),m['footprints'])==model['target']
    return dict(status='SOURCE_GRAMMAR_POSITIVE_CONTROL_PASS',grammar_rules=128,
                fixed_rules=51,private_rules=77,AX_coarse_calls=len(newax),
                AX_fine_atoms=len(m['expand'](newax)),exact_original_fine_word=True,
                maximum_zero_run=max(pw(w)[1]for w in rules),
                root_properties=list(pw(m['names'][96])),
                belongs_to_serialized_model=modelpath is not None,
                scope='Finite source grammar upper bound; no new binary-machine or bootstrap claim')


def check_lp(modelpath,certpath,m,complete_productions=False):
    blob=gzip.decompress(modelpath.read_bytes());model=json.loads(blob);cert=json.loads(certpath.read_text())
    assert hashlib.sha256(blob).hexdigest()==cert['model_uncompressed_sha256']
    words=model['words'];rules=[tuple(r)for r in model['rules']];n=len(words);nr=len(rules)
    assert words==sorted(set(words),key=lambda w:(len(w),w))
    assert len(set(rules))==len(rules)
    fp=m['footprints'];pw=source_properties(m)
    lines=(m['package']/'inputs/semantic.txt').read_text().splitlines()
    nc,nt,na=map(int,lines[0].split());allowed={c:int(mask)for c,mask in map(str.split,lines[1+nc+nt:])}
    dictionary={}
    for d in model['dictionary']:
        t,b,s,p=d['trace'],d['bit'],d['spelling'],tuple(d['properties'])
        assert b in(0,1)and(t,b)not in dictionary
        assert projections(t,fp)==projections(m['expand'](s),fp)
        assert p==pw(s)and p[1]<=model['zero']
        assert(s in m['fixed'])or(len(s)==1 and allowed[s]&(1<<b))
        dictionary[t,b]=(s,p)
    assert model['target']==canonical(m['expand'](m['ax']),fp)
    assert model['fixed_states']==len(m['fixed'])==51
    wi={w:i for i,w in enumerate(words)};ri={r:n+i for i,r in enumerate(rules)}
    for w in words:
        assert len(w)>1 and canonical(w,fp)==w
        assert not((w,0)in dictionary and(w,1)in dictionary)
    by_word={w:[]for w in words}
    for r in rules:
        w,a,b=r
        assert w in wi and len(a)<len(w)and len(b)<len(w)
        assert Counter(w)==Counter(a+b)and projections(w,fp)==projections(a+b,fp)
        assert all((c,k)in dictionary or c in wi for k,c in enumerate((a,b)))
        by_word[w].append(r)
    assert all(by_word.values())
    if complete_productions:
        for w in words:
            expected=set()
            for done in split_ideals(w,fp):
                a=canonical(''.join(c for i,c in enumerate(w)if done>>i&1),fp)
                b=canonical(''.join(c for i,c in enumerate(w)if not(done>>i&1)),fp)
                if((a,0)in dictionary or a in wi)and((b,1)in dictionary or b in wi):expected.add((w,a,b))
            assert set(by_word[w])==expected,('Missing or extra semantic production',w)
    rows=[];lower=[];upper=[];rankoffset=n+nr;columns=rankoffset+n
    def add(row,l,u):rows.append([[j,int(v)]for j,v in row]);lower.append(l);upper.append(u)
    for w in words:add([(wi[w],-1)]+[(ri[r],1)for r in by_word[w]],0,0)
    big=model['zero']+1
    for r in rules:
        w,a,b=r
        for bit,ch in enumerate((a,b)):
            if(ch,bit)not in dictionary:add([(ri[r],1),(wi[ch],-1)],None,0)
        row=[(rankoffset+wi[w],1),(ri[r],-big)];rhs=1-big
        if(a,0)in dictionary:rhs+=dictionary[a,0][1][0]
        else:row.append((rankoffset+wi[a],-1))
        add(row,rhs,None)
    objective=[1]*n+[0]*(nr+n)
    lo=[0]*columns;hi=[1]*(n+nr)+[model['zero']]*n
    lo[wi[model['target']]]=1;hi[rankoffset+wi[model['target']]]=pw(m['ax'])[0]
    assert rows==model['rows']and lower==model['lower']and upper==model['upper']
    assert columns==model['columns']and objective==model['objective']and lo==model['low']and hi==model['high']
    D=cert['denominator'];assert type(D)is int and D>0
    residual=[D*c for c in objective];bound=0
    for i,side,num in cert['dual']:
        assert type(i)is int and 0<=i<len(rows)and type(num)is int
        if side=='E':assert lower[i]==upper[i]and lower[i]is not None;rhs=lower[i]
        elif side=='U':assert num<=0 and upper[i]is not None;rhs=upper[i]
        elif side=='L':assert num>=0 and lower[i]is not None;rhs=lower[i]
        else:raise AssertionError(side)
        bound+=num*rhs
        for j,a in rows[i]:residual[j]-=num*a
    bound+=sum(r*(a if r>=0 else b)for r,a,b in zip(residual,lo,hi))
    assert bound==cert['lower_bound_numerator']
    ceil=-((-bound)//D)
    assert ceil==cert['integer_private_lower_bound']and ceil+51==cert['grammar_lower_bound']
    return dict(status='EXACT_INTEGER_DUAL_PASS',words=n,productions=nr,rows=len(rows),
                nonzero_dual_rows=len(cert['dual']),private_lower_bound=[bound,D],
                grammar_lower_bound=ceil+51,production_completeness_checked=complete_productions,
                scope=model['scope'])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,required=True);p.add_argument('--reordering',type=Path)
    p.add_argument('--model',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--positive-control',type=Path)
    p.add_argument('--complete-productions',action='store_true');p.add_argument('--output',type=Path)
    a=p.parse_args();m=load(a.package);m['package']=a.package;out=[]
    if a.reordering:out.append(check_source_reordering(a.reordering,m))
    if a.model:out.append(check_lp(a.model,a.certificate,m,a.complete_productions))
    if a.positive_control:out.append(check_positive_control(a.positive_control,m,a.model))
    text=json.dumps(out,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text)


if __name__=='__main__':
    assert __debug__
    main()
