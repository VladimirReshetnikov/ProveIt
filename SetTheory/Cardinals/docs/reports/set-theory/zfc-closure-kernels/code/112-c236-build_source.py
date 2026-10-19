#!/usr/bin/env python3
"""Reconstruct the exact closed source reassociation and prove its finite graph.

The instruction and guard graph equality quantifies over all register values.
This program does not infer correctness of the binary decoder.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, json, sys

ROOT = Path(__file__).resolve().parent
BASE_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
NEW_SHA = '1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f'
PREFIX = '1110100100110110101010011100001'
sys.path.insert(0, str(ROOT/'upstream/zfc237/verification'))
import check_source_graph as g

def require(c, msg):
    if not c: raise ValueError(msg)

def tree(rows):
    trie = {}
    for p, op, arg in rows:
        t = trie
        for b in p: t = t.setdefault(b, {})
        t['leaf'] = (op, arg)
    def rec(t):
        return t['leaf'] if 'leaf' in t else (rec(t['0']), rec(t['1']))
    return rec(trie)

@cache
def boundary(t):
    if isinstance(t[0], str):
        o, r = t
        return (1,0,False) if o=='CD' else (r,0,False) if o=='CB' else (0,r,False) if o=='CC' else (0,0,o=='CH')
    a,b=map(boundary,t)
    return max(max(a[0]-1,0),b[0]), max(a[1],max(b[1]-1,0)), a[2] or b[2]

def score(rows):
    unique=set()
    def visit(t):
        unique.add(t)
        if not isinstance(t[0],str):
            visit(t[0]);visit(t[1])
    visit(tree(rows))
    return {'dag_nodes':len(unique),'maximum_depth':max(len(x[0]) for x in rows),
            'maximum_zero_run':max(len(z) for p,_,_ in rows for z in p.split('1'))}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input',type=Path,default=ROOT/'upstream/zfc237/inputs/sites_logical.json')
    ap.add_argument('--output-dir',type=Path,default=ROOT/'source')
    a=ap.parse_args(); raw=a.input.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==BASE_SHA,'Wrong pinned source')
    old=json.loads(raw); new=[]; chunk_counts=[]; chunk_bounds=[]
    for suffix in ('0','10','11'):
        pref=PREFIX+suffix
        part=[(p[len(pref):],o,r) for p,o,r in old if p.startswith(pref)]
        chunk_counts.append(len(part));chunk_bounds.append(boundary(tree(part)))
    require(chunk_counts==[245,160,132],'Wrong source chunks')
    require(chunk_bounds==[(0,0,False)]*3,'A source chunk has escaping control')
    for p,o,r in old:
        if p.startswith(PREFIX):
            s=p[len(PREFIX):]
            if s.startswith('0'): p=PREFIX+'00'+s[1:]
            elif s.startswith('10'): p=PREFIX+'01'+s[2:]
            elif s.startswith('11'): p=PREFIX+'1'+s[2:]
            else: raise ValueError('Malformed rotated subtree')
        new.append([p,o,r])
    bo,bg,bi,_=g.graph(old);co,cg,ci,_=g.graph(new)
    require([x[1:] for x in bo]==[x[1:] for x in co],'Ordered instructions changed')
    require(bg==cg and bi==ci,'A source guard edge changed')
    require(len(bg)==6455 and sum(x[0]=='HALT' for x in bg)==1,'Wrong source census')
    data=(json.dumps(new,indent=2)+'\n').encode()
    require(hashlib.sha256(data).hexdigest()==NEW_SHA,'Unexpected rotated source bytes')
    receipt={'status':'PASS_CLOSED_REASSOCIATION_AND_ALL_SOURCE_GUARDS',
             'baseline_sha256':BASE_SHA,'source_sha256':NEW_SHA,'prefix':PREFIX,
             'substitution':{'0u':'00u','10u':'01u','11u':'1u'},
             'chunk_leaf_counts':chunk_counts,'chunk_boundaries':chunk_bounds,
             'changed_paths':sum(a[0]!=b[0] for a,b in zip(old,new)),
             'ordered_instructions_identical':True,'all_guard_edges_identical':True,
             'leaf_occurrences':len(bg),'guarded_cases':sum(2 if x[0]=='DEC' else 1 for x in bg),
             'before':score(old),'after':score(new),
             'scope':'All source configurations over natural registers; no binary runtime claim.'}
    a.output_dir.mkdir(parents=True,exist_ok=True)
    (a.output_dir/'sites_logical.json').write_bytes(data)
    (a.output_dir/'source_certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
