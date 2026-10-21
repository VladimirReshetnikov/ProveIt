#!/usr/bin/env python3
"""Separate reader for the new positive-trie artifact, with corruption controls.

Only JSON and literal Coq certificate data are read. No received program runs.
This is an exact-data audit, not the generalized semantic soundness theorem.
"""
from pathlib import Path
import copy,json,os,re,sys
if sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('OPTIMIZED_MODE_REJECTED: run without -O, -OO, or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parent
old=ROOT/'incoming/K215_Certificate_Refinements_2026-10-21/balanced_lookup/Cert215Compact.v'
rows=[tuple(map(int,r)) for r in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',old.read_text())]
def ensure(x,label):
    if not x:raise ValueError(label)
def validate(a):
    ensure(a['initial']==1 and a['entry_count']==len(rows)==2240,'root and count')
    seen={}; todo=[(a['tree'],())]
    while todo:
        node,path=todo.pop()
        if node is None:continue
        ensure(isinstance(node,dict) and set(node)=={'e','l','r'},'shape')
        key=2**len(path)+sum(int(b)*2**i for i,b in enumerate(path))
        ensure(key not in seen and 1<=key<=len(rows),'key')
        e=node['e']; ensure(isinstance(e,list) and len(e)==4 and all(type(x)is int and x>0 for x in e),'entry data')
        x,y,j,k=rows[key-1]
        ensure(e==[x,y,j+1,k+1],'exact reindexed entry')
        seen[key]=e
        todo.extend([(node['l'],path+(False,)),(node['r'],path+(True,))])
    ensure(set(seen)==set(range(1,len(rows)+1)),'complete key set')
    def get(key):
        node=a['tree']; depth=0
        while node is not None:
            depth+=1
            if key==1:return node['e'],depth
            node=node['r' if key%2 else 'l'];key//=2
        return None,depth
    for key in range(1,16384):
        value,_=get(key); ensure(value==seen.get(key),'exhaustive independent lookup')
    return {'nodes':len(seen),'initial':1,'exhaustive_keys':16383,'exact_reindexing':True}

def main():
    a=json.loads((ROOT/'positive_trie_certificate.json').read_text())
    result=validate(a); rejected=[]
    def test(name,change):
        b=copy.deepcopy(a); change(b)
        try:validate(b)
        except (ValueError,KeyError,TypeError):rejected.append(name);return
        raise ValueError('negative control accepted: '+name)
    test('wrong initial key',lambda b:b.update(initial=2))
    test('omit root subtree',lambda b:b['tree'].update(l=None))
    test('swap root children',lambda b:b['tree'].update(l=b['tree']['r'],r=b['tree']['l']))
    test('old zero-based successor',lambda b:b['tree']['e'].__setitem__(2,b['tree']['e'][2]-1))
    test('wrong source path',lambda b:b['tree']['e'].__setitem__(0,3))
    test('out-of-range target',lambda b:b['tree']['e'].__setitem__(3,8192))
    test('nonpositive address',lambda b:b['tree']['e'].__setitem__(2,0))
    result.update(rejected_controls=rejected,proof_assistant_run=False)
    (ROOT/'POSITIVE_TRIE_INDEPENDENT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
