"""Check report 51's linear size argument on the maintained batch engines."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import random
import sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from fastunknot.compressed_words import WordArena
from fastunknot.elimination_batch import apply_batch
from fastunknot.elimination_batch_verify import replay_compressed_batch


def path(a,root,g):
    count,pos,_=a.occurrence(root,g);assert count==1
    result=[]
    while root:
        result.append(root);rule=a.rules[root]
        if rule[0]=='t':break
        left,right=rule[1:]
        if pos<a.lengths[left]:root=left
        else:pos-=a.lengths[left];root=right
    return set(result)


def main(output):
    rng=random.Random(261008525);rows=[]
    for case in range(400):
        rank=rng.randrange(3,11);words=[];images={1:[1],-1:[-1],2:[2],-2:[-2]};selected=[]
        for g in range(3,rank+1):
            rest=[rng.choice((-1,1))*rng.randrange(1,g) for _ in range(rng.randrange(5))]
            sign=rng.choice((-1,1));cut=rng.randrange(len(rest)+1)
            # Donor U g^sign V has defining context V U.
            word=rest[:cut]+[sign*g]+rest[cut:];context=rest[cut:]+rest[:cut]
            value=[y for x in context for y in images[x]]
            if sign>0:value=[-x for x in reversed(value)]
            images[g]=value;images[-g]=[-x for x in reversed(value)]
            selected.append(dict(relation=len(words),generator=g));words.append(word)
        for _ in range(4):words.append([rng.choice((-1,1))*rng.randrange(1,rank+1) for _ in range(rng.randrange(12))])
        rng.shuffle(selected);expected=[[] if i<rank-2 else [y for x in w for y in images[x]] for i,w in enumerate(words)]
        record={}
        for label,checker in (('producer',False),('checker',True)):
            a=WordArena(max_work=10000000);roots=[a.from_word(w) for w in words];alive=set(range(1,rank+1))
            M=len(a._reachable(roots));N=len(a.rules)-1;holes=set();hole_total=0
            for entry in selected:
                h=path(a,roots[entry['relation']],entry['generator']);assert not holes&h
                holes|=h;hole_total+=len(h)
            assert hole_total<=M
            if checker:assert replay_compressed_batch(a,roots,alive,dict(kind='elimination_batch',entries=selected))
            else:apply_batch(a,roots,alive,selected)
            assert alive=={1,2} and [a.expand(root,limit=1000000) for root in roots]==expected
            reachable=len(a._reachable(roots));allocated=len(a.rules)-1-N
            assert reachable<=4*M and allocated<=7*M
            record[label]=dict(source_nodes=M,hole_nodes=hole_total,output_nodes=reachable,new_nodes=allocated)
        rows.append(record)
    paths=[Path(__file__)]+list((ROOT/'fastunknot').rglob('*.py'))
    result=dict(seed=261008525,cases=len(rows),native_updates=2*len(rows),literal_agreement=True,
        disjoint_paths=True,reachable_bound='4*M',allocation_bound='7*M',rows=rows,
        source_sha256={str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths},
        scope='Random acyclic raw singleton definitions with two noncommuting survivors, both donor signs, mixed contexts, empty images, shuffled witnesses and untouched relator slots. Algebraic presentations, not diagram discovery. Checks support the proof; finite samples do not prove the bound.')
    output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('rows','source_sha256')},indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);main(p.parse_args().output)
