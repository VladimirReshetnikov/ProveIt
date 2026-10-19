#!/usr/bin/env python3
"""Audit unchanged late rotation templates by exact whole-source subtrees.

This does not reject alternative source transformations or prove a lower bound.
Inputs and outputs are relative to the package unless explicitly selected.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json, sys
from build_h229 import tree_of_sites, sites_of_tree, is_leaf, require

ROOT = Path(__file__).resolve().parents[1]

def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            require((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'), 'Malformed old table')
            rows[q,b]=(w,1 if d=='R' else -1,z)
    require(len(rows)==2*len({q for q,b in rows}), 'Partial old table')
    return rows

def source_mapping(root, rows, entry):
    seen=defaultdict(set); inverse=defaultdict(set)
    def visit(node,q):
        if is_leaf(node) or q in seen[node]:return
        seen[node].add(q);inverse[q].add(node)
        for b in (0,1):
            w,d,z=rows[q,b]
            if (w,d)==(b,1):visit(node[b],z)
    visit(root,entry)
    return seen,inverse

def count(root, pattern):
    return int(root==pattern)+(0 if is_leaf(root) else count(root[0],pattern)+count(root[1],pattern))

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package-root',type=Path,default=ROOT)
    p.add_argument('--output',type=Path,default=ROOT/'reproduced/later_templates.json')
    a=p.parse_args();base=a.package_root
    ksites=base/'source/sites_logical.json';ktable=base/'machine/k228_oldlabels.tm'
    kroot=tree_of_sites(json.loads(ksites.read_text()));km,ki=source_mapping(kroot,table(ktable),84)
    records=[]
    for name,folder,fn,q,c in [
        ('237_to_236','candidate-composed237','zfc_composed237_old.tm',177,185),
        ('236_to_235','candidate-rotated236','zfc236_old.tm',138,211)]:
        tp=base/'upstream/proveit'/folder/fn;sp=tp.with_name('sites_logical.json')
        old=tree_of_sites(json.loads(sp.read_text()));om,oi=source_mapping(old,table(tp),96)
        require(len(oi[q])==len(oi[c])==1,'Reference source role is ambiguous')
        outer,inner=next(iter(oi[q])),next(iter(oi[c]))
        records.append({'template':name,'reference_outer':q,'reference_inner':c,
                        'reference_outer_leaves':len(sites_of_tree(outer)),
                        'outer_occurrences_anywhere_in_K':count(kroot,outer),
                        'inner_occurrences_anywhere_in_K':count(kroot,inner),
                        'exposed_K_outer_labels':sorted(km.get(outer,())),
                        'exposed_K_inner_labels':sorted(km.get(inner,())),
                        'old_table_sha256':sha(tp),'old_source_sha256':sha(sp)})
    require([r['reference_outer_leaves'] for r in records]==[537,837],'Wrong reference templates')
    require(all(r['outer_occurrences_anywhere_in_K']==0 for r in records),'A supposedly absent source template is present')
    require(records[0]['inner_occurrences_anywhere_in_K']==1 and records[1]['inner_occurrences_anywhere_in_K']==0,'Unexpected inner subtree census')
    result={'status':'UNCHANGED_LATE_SOURCE_TEMPLATES_ABSENT','k_source_sha256':sha(ksites),
            'k_table_sha256':sha(ktable),'templates':records,
            'scope':'Exact absence of the initial subtrees of the specified old certificates. Alternative K-specific rotations and semantic folds remain possible.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
