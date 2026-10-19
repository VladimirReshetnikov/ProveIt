#!/usr/bin/env python3
"""Independently rebuild and verify the single shared association rotation.

This program reads the complete original Prog254.v tree, reconstructs the
rotation at nine original node occurrences, and checks all guarded source
successors with direct Boolean-list program-counter operations. It does
not use the searcher's hash-consed graph or its bisect decoder.

The literal source program is Mira-Cult's, verified by Jeff Ketchersid;
the compiler framework is Andrew James Wade's. The rotation is a new
optimization of the supplied source. Binary verification is separate.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import json
import re

SOURCE_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
PIVOTS=(363,1400,1995,2710,2977,4313,4364,4416,4879)

def parse(raw):
    s=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    token=r'(?:CN|CI|CD|CB|CC) \d+|CH'
    regex=r'\(('+token+r'),\s*('+token+r')\)'
    assert re.sub(r'[;\s]','',re.sub(regex,'',s))==''
    def edge(s):
        op,*n=s.split();return (op,int(n[0]) if n else None)
    nodes=[tuple(edge(e) for e in pair) for pair in re.findall(regex,s)]
    assert len(nodes)==6459
    return nodes

def leaves_of(nodes):
    leaves=[];seen=set();node_paths={}
    def edge(e,p):
        if e[0]=='CN':visit(e[1],p)
        else:leaves.append((p,*e))
    def visit(n,p):
        assert 0<=n<len(nodes) and n not in seen
        seen.add(n);node_paths[n]=p
        for b,e in enumerate(nodes[n]):edge(e,p+str(b))
    visit(0,'')
    assert len(seen)==len(nodes) and len(leaves)==len(nodes)+1
    return leaves,node_paths

def source_successor(path,op,n,positive):
    bits=[b=='1' for b in path]
    if op=='CH':return None
    if op=='CC' or op=='CB' or (op=='CD' and not positive):
        wanted=op=='CC'; count=n if op in ('CC','CB') else 1
        while count and bits:
            bit=bits.pop()
            if bit==wanted:count-=1
        if op=='CC':return ''.join('1' if b else '0' for b in bits)
    for i in range(len(bits)-1,-1,-1):
        if not bits[i]:bits[i]=True;break
        bits[i]=False
    return ''.join('1' if b else '0' for b in bits)

def decoder(nodes,lookup,pc):
    if pc is None:return None
    n=0;depth=0;p=''
    for _ in range(len(nodes)+1):
        bit=pc[depth] if depth<len(pc) else '0'
        p+=bit;depth+=1
        op,value=nodes[n][int(bit)]
        if op=='CN':n=value
        else:
            assert '1' not in pc[depth:]
            return lookup[p]
    raise AssertionError('tree decode did not terminate')

def unique_subtrees(nodes):
    ids={}; groups=defaultdict(list)
    def intern(value):
        if value not in ids:ids[value]=len(ids)
        return ids[value]
    def edge(e):
        return visit(e[1]) if e[0]=='CN' else intern(e)
    def visit(n):
        key=('pair',edge(nodes[n][0]),edge(nodes[n][1]))
        i=intern(key);groups[i].append(n);return i
    root=visit(0)
    return groups,root

def transform(nodes):
    out=[]
    def edge(e):return ('CN',visit(e[1])) if e[0]=='CN' else e
    def visit(n):
        new_n=len(out);out.append(None)
        left,right=nodes[n]
        if n in PIVOTS:
            assert right[0]=='CN'
            middle,last=nodes[right[1]]
            new_left=len(out);out.append(None)
            aa=edge(left);bb=edge(middle);cc=edge(last)
            out[new_left]=(aa,bb)
            out[new_n]=( ('CN',new_left),cc )
        else:out[new_n]=(edge(left),edge(right))
        return new_n
    assert visit(0)==0 and len(out)==6459
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    fallback=Path(__file__).resolve().parents[1]/'sources/context246/zfc-context246/sources/Prog254.v'
    parser.add_argument('--source',type=Path,default=fallback)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    raw=args.source.read_bytes();assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA
    old=parse(raw);oldleaves,oldpaths=leaves_of(old)
    new=transform(old);newleaves,newpaths=leaves_of(new)
    assert len(oldleaves)==len(newleaves)==6460
    assert [(op,n) for p,op,n in oldleaves]==[(op,n) for p,op,n in newleaves]
    old_lookup={p:i for i,(p,_,_) in enumerate(oldleaves)}
    new_lookup={p:i for i,(p,_,_) in enumerate(newleaves)}
    oldgroups,_=unique_subtrees(old);newgroups,_=unique_subtrees(new)
    assert len(oldgroups)==203 and len(newgroups)==202
    assert sorted(next(v for v in oldgroups.values() if 363 in v))==list(PIVOTS)
    obsolete=sorted(next(v for v in oldgroups.values() if 382 in v))
    assert obsolete==sorted(old[n][1][1] for n in PIVOTS)
    case_records=[]
    for i,((p,op,n),(q,op2,n2)) in enumerate(zip(oldleaves,newleaves)):
        for positive in ([False,True] if op=='CD' else [None]):
            old_pc=source_successor(p,op,n,positive)
            new_pc=source_successor(q,op,n,positive)
            old_target=decoder(old,old_lookup,old_pc)
            new_target=decoder(new,new_lookup,new_pc)
            assert old_target==new_target, (i,p,q,op,n,positive,old_target,new_target)
            case_records.append([i,positive,old_target])
    assert len(case_records)==8391
    assert decoder(old,old_lookup,'')==decoder(new,new_lookup,'')==0
    # Independently confirm the intended three-block rotation using original
    # structural identities, rather than only counting nodes after the change.
    class_of={n:k for k,v in oldgroups.items() for n in v}
    assert class_of[364]==class_of[76]
    assert class_of[383]==class_of[94]
    assert old[75]==(('CN',76),('CN',94))
    assert old[363]==(('CN',364),('CN',382))
    assert old[382]==(('CN',383),('CN',389))

    pivots=[{'node':n,'path':oldpaths[n],'left':old[n][0],
             'obsolete_right_node':old[n][1][1],
             'middle':old[old[n][1][1]][0],
             'last':old[old[n][1][1]][1]} for n in PIVOTS]
    result={'status':'PASS exact all-register source-control equivalence',
            'source_sha256':SOURCE_SHA,'pivots':pivots,
            'original_unique_pairs':203,'rotated_unique_pairs':202,
            'literal_nodes':6459,'instruction_leaves':6460,'guards_compared':8391,
            'all_register_effects_identical':True,'all_successor_leaf_indices_identical':True,
            'initial_leaf_identical':True,'no_unreachable_case_exemption':True,
            'maximum_old_zero_run':max(max(map(len,p.split('1'))) for p,_,_ in oldleaves),
            'maximum_new_zero_run':max(max(map(len,p.split('1'))) for p,_,_ in newleaves),
            'maximum_old_depth':max(len(p) for p,_,_ in oldleaves),
            'maximum_new_depth':max(len(p) for p,_,_ in newleaves),
            'leaf_map':[{'old_path':p,'new_path':q,'op':op,'arg':n}
                        for (p,op,n),(q,_,_) in zip(oldleaves,newleaves)],
            'guarded_successors':case_records,
            'proof_boundary':'Ordinary source proof with exhaustive finite control certificate; binary simulation and blank boot are separate.'}
    args.output_dir.mkdir(parents=True,exist_ok=True)
    (args.output_dir/'rotation245_source_certificate.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    (args.output_dir/'rotation245_program_tree.json').write_text(json.dumps({'nodes':new,'root':0},separators=(',',':'))+'\n')
    print(json.dumps({k:result[k] for k in ['status','source_sha256','original_unique_pairs',
          'rotated_unique_pairs','literal_nodes','instruction_leaves','guards_compared',
          'maximum_old_zero_run','maximum_new_zero_run','maximum_old_depth','maximum_new_depth']},indent=2))

if __name__=='__main__':main()
