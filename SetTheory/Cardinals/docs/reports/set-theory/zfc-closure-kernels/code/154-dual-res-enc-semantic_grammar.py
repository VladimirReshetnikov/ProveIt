#!/usr/bin/env python3
"""Explore source grammar reuse modulo proven zero-register stuttering.

At each source occurrence a closed tree is split into closed atoms.  An atom
can be inserted or deleted only when its exact source execution, assuming a
recorded set of registers are zero, is a finite identity path to its exit.
Other atoms must match literally.  Thus successful matches are semantic
lemmas under the supplied inductive register facts, not finite-run guesses.

Candidate binary tables still require their own runtime proof.
"""
import json, sys, time
from collections import defaultdict
from functools import cache
from pathlib import Path
import encoding_support as x
s,b,z,W=x.s,x.b,x.z,x.W


@cache
def atoms(n):
    if not s.leaf(n) and s.boundary(n[0])==s.boundary(n[1])==(0,0,False):
        return atoms(n[0])+atoms(n[1])
    return (n,)


@cache
def nop_requirement(n):
    if s.boundary(n)!=(0,0,False):return None
    # An explicit exit sentinel distinguishes ordinary exit from a loop to
    # ordinal zero, which a standalone circular source graph would conflate.
    rr=s.sites((n,('CH',None)));gg=s.graph_arithmetic(rr)[0]
    assert gg==s.graph_intervals(rr)
    stop=len(rr)-1;at=0;seen=set();req=0;trace=[]
    while at!=stop:
        if at in seen:return None
        seen.add(at);trace.append(at)
        _,op,arg=rr[at]
        if op=='CD':req|=1<<arg;at=gg[at][1][0]
        elif op in ('CB','CC'):at=gg[at][1][0]
        else:return None
    return req,tuple(trace)


@cache
def dag(n):
    return frozenset((n,)) if s.leaf(n) else dag(n[0])|dag(n[1])|{n}


def replace_all(n,old,new):
    @cache
    def go(n):
        if n==old:return new
        return n if s.leaf(n) else (go(n[0]),go(n[1]))
    return go(n)


def match(oldatoms,newatoms,zero_masks):
    @cache
    def go(i,j):
        if i==len(oldatoms) and j==len(newatoms):return ()
        if i<len(oldatoms) and j<len(newatoms) and oldatoms[i]==newatoms[j]:
            out=go(i+1,j+1)
            if out is not None:return (('keep',i,j),)+out
        if j<len(newatoms):
            np=nop_requirement(newatoms[j])
            if np is not None and not np[0]&~zero_masks[i]:
                out=go(i,j+1)
                if out is not None:return (('insert',i,j),)+out
        if i<len(oldatoms):
            np=nop_requirement(oldatoms[i])
            if np is not None and not np[0]&~zero_masks[i]:
                out=go(i+1,j)
                if out is not None:return (('delete',i,j),)+out
        return None
    try:return go(0,0)
    except RecursionError:return None


def search(base_name,sp,tp,fp,limit,single=False):
    rr=json.loads(sp.read_text());old=s.tree(rr);T=b.read_table(tp.read_bytes())
    facts=json.loads(fp.read_text())['facts']
    zeros=[sum((1<<r)for r,v in enumerate(f)if v==1) if f else 0 for f in facts]
    occurrences=defaultdict(list)
    def walk(n,p='',lo=0):
        hi=lo+len(x.flat(n))
        if s.boundary(n)==(0,0,False):occurrences[n].append((p,lo,hi))
        if not s.leaf(n):
            walk(n[0],p+'0',lo);walk(n[1],p+'1',lo+len(x.flat(n[0])))
    walk(old)
    nodes=list(occurrences);ns={n:i for i,n in enumerate(nodes)}
    vectors={}
    for n,occs in occurrences.items():
        vec=[]
        aa=atoms(n)
        for p,lo,hi in occs:
            cursor=lo;vv=[]
            for a in aa:
                vv.append(zeros[cursor]);cursor+=len(x.flat(a))
            assert cursor==hi;vv.append(zeros[hi%len(rr)]);vec.append(tuple(vv))
        vectors[n]=vec
    outdir=W/'semantic_grammar'/(base_name+('_single' if single else ''));outdir.mkdir(parents=True,exist_ok=True)
    results=[];total=0;matches=0;best=999
    start=time.time()
    for i,n in enumerate(nodes):
        for j,m in enumerate(nodes):
            if n==m:continue
            total+=1
            proof=[];good=[]
            for vv in dict.fromkeys(vectors[n]):
                certificate=match(atoms(n),atoms(m),vv)
                if certificate is None:
                    if single:continue
                    break
                item={'zero_masks':vv,'atom_alignment':certificate}
                proof.append(item)
                if single:
                    for occ,v in zip(occurrences[n],vectors[n]):
                        if v==vv:good.append((occ,item))
            else:
                if not single:good=[(None,proof)]
            for occ,certificate in good:
                matches+=1
                new=s.replace(old,occ[0],m) if single else replace_all(old,n,m)
                count=len(dag(new))
                if count>limit:continue
                result={'base':base_name,'old_node':i,'new_node':j,
                        'occurrences':[occ] if single else occurrences[n],
                        'all_occurrences_matched':not single,
                        'old_atoms':len(atoms(n)),'new_atoms':len(atoms(m)),
                        'metrics':s.metrics(new),'alignment_certificates':certificate,
                        'status':'SEMANTIC_SOURCE_MATCH; BINARY_RUNTIME_NOT_PROVED'}
                dd=outdir/(f'n{i}_m{j}'+(f'_i{occ[1]}' if single else ''));dd.mkdir(exist_ok=True)
                (dd/'sites.json').write_bytes(s.compact(s.sites(new)))
                try:
                    U,info=z.compile_tree(T,old,new);result['compiler']=info
                    (dd/'candidate.tm').write_bytes(b.table_bytes(U))
                except Exception as exc:result['error']=repr(exc)
                (dd/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
                results.append({k:v for k,v in result.items()if k!='alignment_certificates'})
                if count<best:
                    best=count;print(json.dumps({'best':best,**results[-1]}),flush=True)
        if i%20==0:print(json.dumps({'base':base_name,'node':i,'nodes':len(nodes),'pairs':total,'matches':matches,'saved':len(results),'seconds':round(time.time()-start,1)}),flush=True)
    rec={'base':base_name,'pairs':total,'matched_pairs':matches,'saved':results,
         'elapsed_seconds':time.time()-start,'smallest_source_DAG':best}
    (outdir/'summary.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items()if k!='saved'}),flush=True)


if __name__=='__main__':
    sys.setrecursionlimit(10000)
    base=W/'K220_Construction_2026-10-20/machine'
    single='--single' in sys.argv
    search('original',base/'sites220.json',base/'k220.native.tm',W.parent/'root_work/source_facts.json',208,single)
    base=W.parent/'latest220/K220_Alternatives_2026-10-20/exploratory/six_leaf_zero_nop'
    search('zero_nop',base/'sites.json',base/'candidate.tm',base/'source_facts/facts.json',208,single)
