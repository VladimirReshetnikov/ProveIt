#!/usr/bin/env python3
"""Complete constructor-tag permutations of the K220 register source.

Membership stays tag 1, hence false stays code 1.  The other three tags are
permuted among implication, universal quantification, and equality.  This
includes the GEN and MP command constructors, not only the axiom emitter.

The exact 81 arithmetic constructor occurrences are identified before any
editing.  Full control-flow graph correspondence is checked independently
of the macro semantics; insertion/deletion changes only the constant tag.
Compilation remains exploratory until an actual runtime screen/proof runs.
"""
from pathlib import Path
from functools import cache
import collections,itertools,json,sys
import additive_binder as z

ROOT=z.ROOT
OUT=ROOT/'research_calculus/generated/tag_permutations'
F=z.flat(z.TREE); CORE=z.q(90); CF=z.flat(CORE); INC=('CI',1)
HITS=[]
for i in range(len(F)-len(CF)+1):
    if F[i:i+len(CF)]!=CF: continue
    j=i+len(CF)
    while j<len(F) and F[j]==INC:j+=1
    HITS.append((i,i+len(CF),j,j-i-len(CF)))
assert len(HITS)==81
assert collections.Counter(x[3] for x in HITS)=={0:41,1:12,2:22,3:6}

def incs(n,shape):
    assert n>0
    if n==1:return INC
    if shape=='left':
        a=INC
        for _ in range(n-1):a=(a,INC)
        return a
    return z.serial([INC]*n)

def constructors(tags,policy='delta',shape='right'):
    """Return changed source and its exact primitive edit manifest."""
    # Key is original source interval.  Replacement programs are all closed.
    replacements={};deletes=set();events=[]
    for lo,core_end,hi,old in HITS:
        new=tags[old]
        if new==old:continue
        if policy=='rebuild':
            replacement=CORE if new==0 else (CORE,incs(new,shape))
            replacements[lo,core_end]=replacement
            deletes.update(range(core_end,hi))
        elif policy=='delta':
            if new>old:replacements[lo,core_end]=(CORE,incs(new-old,shape))
            else:deletes.update(range(core_end+new,hi))
        elif policy=='last':
            if new>old:
                if old==0:replacements[lo,core_end]=(CORE,incs(new,shape))
                else:replacements[hi-1,hi]=incs(1+new-old,shape)
            else:deletes.update(range(core_end+new,hi))
        else:raise ValueError(policy)
        events.append(dict(start=lo,core_end=core_end,end=hi,old_tag=old,new_tag=new))
    consumed=set()
    def edit(t,i=0):
        j=i+len(z.flat(t))
        if (i,j) in replacements:
            consumed.add((i,j));assert z.s.boundary(t)==(0,0,False)
            r=replacements[i,j];assert z.s.boundary(r)==(0,0,False)
            return r
        if z.s.leaf(t):return None if i in deletes else t
        a=edit(t[0],i);b=edit(t[1],i+len(z.flat(t[0])))
        return b if a is None else a if b is None else (a,b)
    tree=edit(z.TREE)
    assert consumed==set(replacements)
    # Independently assemble the expected primitive sequence and position map.
    by_start={a:(b,p) for (a,b),p in replacements.items()}
    expected=[];old_to_new={};i=0
    while i<len(F):
        old_to_new[i]=len(expected)
        if i in by_start:
            j,p=by_start[i];ff=z.flat(p)
            # These replacements preserve an old primitive prefix (core or CI).
            assert ff[:j-i]==F[i:j]
            for k in range(i,j):old_to_new[k]=len(expected)+(k-i)
            expected.extend(ff);i=j
        elif i in deletes:i+=1
        else:expected.append(F[i]);i+=1
    old_to_new[len(F)]=len(expected)
    assert z.flat(tree)==tuple(expected)
    sites=z.s.sites(tree)
    graph=z.s.graph_arithmetic(sites)[0]
    assert graph==z.s.graph_intervals(sites)
    oldgraph=z.s.graph_arithmetic(z.ROWS)[0]
    # Contract tags are increment-only chains.  Map original nondeleted core
    # instructions to new instructions; compare their guarded successors after
    # skipping the original tag and the corresponding new tag chains.
    old_tags={k for _,ce,hi,_ in HITS for k in range(ce,hi)}
    new_tags=set()
    newF=tuple(expected)
    for lo,ce,hi,old in HITS:
        start=old_to_new[lo]+len(CF)
        new_tags.update(range(start,start+tags[old]))
    def skip(g,p,excluded):
        seen=set()
        while p in excluded:
            assert p not in seen;seen.add(p)
            ef,to=g[p];assert tuple(ef)==('increment',1) and len(to)==1
            p=to[0]
        return p
    count=0
    for i,(eff,targets) in enumerate(oldgraph):
        if i in old_tags:continue
        ni=old_to_new[i];ne,nt=graph[ni]
        assert eff==ne,(i,ni,eff,ne)
        want=tuple(old_to_new[skip(oldgraph,p,old_tags)] for p in targets)
        got=tuple(skip(graph,p,new_tags) for p in nt)
        assert got==want,(i,ni,want,got)
        count+=1
    return tree,dict(events=events,unchanged_primitive_effects_and_guarded_targets=count,
                     old_constructor_histogram=dict(collections.Counter(x[3] for x in HITS)),
                     original_source_leaves=len(F),new_source_leaves=len(expected),
                     GEN_changed=tags[2]!=2,MP_changed=tags[0]!=0)

def main():
    OUT.mkdir(parents=True,exist_ok=True);summaries=[]
    for imp,all_,eq in itertools.permutations([0,2,3]):
        tags={0:imp,1:1,2:all_,3:eq}
        for policy,shape in itertools.product(['delta','last','rebuild'],['right','left']):
            name=f'I{imp}Q{all_}E{eq}_{policy}_{shape}'
            try:
                tree,manifest=constructors(tags,policy,shape)
                d=OUT/name;d.mkdir(exist_ok=True)
                sites=z.s.sites(tree);(d/'sites.json').write_bytes(z.s.compact(sites))
                result=dict(name=name,tags=tags,source_metrics=z.s.metrics(tree),
                            manifest=manifest,policy=policy,tag_parenthesization=shape)
                try:
                    table,met=z.compile_tree(z.T,z.TREE,tree)
                    result['compiler']=met;(d/'candidate.tm').write_bytes(z.b.table_bytes(table))
                except Exception as e:result['compile_error']=repr(e)
                (d/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
                summary={k:v for k,v in result.items() if k!='manifest'}
            except Exception as e:summary=dict(name=name,error=repr(e))
            summaries.append(summary);print(json.dumps(summary),flush=True)
    (OUT/'summary.json').write_text(json.dumps(summaries,indent=2)+'\n')

if __name__=='__main__':main()
