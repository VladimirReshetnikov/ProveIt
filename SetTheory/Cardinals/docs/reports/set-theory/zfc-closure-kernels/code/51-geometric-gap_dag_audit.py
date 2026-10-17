#!/usr/bin/env python3
"""Audit the literal source cost and root-carry discipline of the gap-clock shell.

This uses the actual frozen Prog254.v. LOAD is a custom control operation,
charged as one decoder leaf; this script does not charge or validate its
separate binary transducer. Counts here are unique source decision pairs,
not Turing-machine working-state counts.

Example:
 python3 gap_dag_audit.py --source path/to/Prog254.v --output gap-dag-audit.json
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

EXPECTED_SHA256 = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
UPSTREAM_SHA = '297ab8df7e5de329605c3875b4934643b371a5e3'
PROVEIT_SHA = '85633fd2f57b5dca16f87667699134d1b500ebc0'

def read_nodes(raw):
    body=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    textpairs=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    def parse(s):
        op,*arg=s.split()
        return (op[1:],int(arg[0])) if arg else (op[1:],)
    pairs=[tuple(map(parse,p)) for p in textpairs]
    assert len(pairs)==6459
    return pairs

def source_tree(nodes,q=0):
    @lru_cache(None)
    def walk(e):
        return ('N',walk(nodes[e[1]][0]),walk(nodes[e[1]][1])) if e[0]=='N' else e
    return walk(('N',q))

def intern(tree):
    pool={};nodes=[]
    def go(e):
        if e[0]!='N':return e
        pair=go(e[1]),go(e[2])
        if pair not in pool:pool[pair]=len(nodes);nodes.append(pair)
        return ('N',pool[pair])
    root=go(tree)[1]
    return nodes,root

def leaves(tree,prefix=''):
    if tree[0]=='N':
        yield from leaves(tree[1],prefix+'0')
        yield from leaves(tree[2],prefix+'1')
    else:yield prefix,tree

@lru_cache(None)
def bounds(tree):
    if tree[0]=='N':
        h0,b0,c0=bounds(tree[1]);h1,b1,c1=bounds(tree[2])
        return 1+max(h0,h1),max(b0-1,b1,0),max(c0,c1-1,0)
    k=tree[0];v=tree[1] if len(tree)>1 else 0
    return 0,(v if k=='B' else 1 if k=='D' else 0),(v if k=='C' else 0)

def strip(path,bit,count):
    while count and path:
        count-=path[-1]==bit
        path=path[:-1]
    return path

def inc(path):
    """None means the binary implementation carries through the left marker."""
    index=path.rfind('0')
    if index<0:return None
    return (path[:index]+'1'+'0'*(len(path)-index-1)).rstrip('0')

def audit_tree(tree):
    nodes,root=intern(tree);ls=list(leaves(tree));overflow=[];custom=[];cases=0
    for path,e in ls:
        op=e[0];arg=e[1] if len(e)>1 else None
        for zero in ((True,False) if op=='D' else (None,)):
            cases+=1
            if op=='LOAD':
                # LOAD is entered at the one-bit PC 1. The literal transducer
                # clears that bit and returns to the empty source PC; it does
                # not invoke the ordinary increment/carry protocol.
                custom.append({'path':path,'operation':op,'returns_to':''})
                continue
            if op=='I' or op=='D' and not zero:out=inc(path)
            elif op=='D':out=inc(strip(path,'0',1))
            elif op=='B':out=inc(strip(path,'0',arg))
            elif op=='C':out=strip(path,'1',arg)
            elif op=='H':continue
            else:raise AssertionError(op)
            if out is None:overflow.append({'path':path,'operation':op,'argument':arg,'zero':zero})
    return {'unique_decision_pairs':len(nodes),'unfolded_leaves':len(ls),
            'guarded_cases':cases,'maximum_leaf_depth':max(map(lambda p:len(p[0]),ls)),
            'bounds':dict(zip(('height','escaping_breaks','escaping_continues'),bounds(tree))),
            'primitive_histogram':dict(Counter(e[0] for p,e in ls)),
            'overflow_cases':overflow,'custom_control_cases':custom,'nodes':nodes,'root':root}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--loader-stride',type=int,choices=(1,2),default=1,
                        help='Custom LOAD gap increment; both variants set L to input gap+1.')
    args=parser.parse_args()
    raw=args.source.read_bytes();assert hashlib.sha256(raw).hexdigest()==EXPECTED_SHA256
    rows=read_nodes(raw);assert rows[0]==(('N',1),('N',10))
    original=source_tree(rows);body=source_tree(rows,10)
    # The current post-fetch body neither reads nor writes the NP register 0.
    assert all(not(e[0] in ('I','D') and e[1]==0) for p,e in leaves(body))
    assert bounds(body)[1:]==(0,0)
    shell=('N',('N',('D',8),('N',body,('C',2))),('LOAD',))
    oa,ba,sa=map(audit_tree,(original,body,shell))
    assert oa['unique_decision_pairs']==203 and ba['unique_decision_pairs']==194
    assert sa['unique_decision_pairs']==197
    assert oa['maximum_leaf_depth']==34 and sa['maximum_leaf_depth']==36
    assert sa['bounds']['escaping_breaks']==sa['bounds']['escaping_continues']==0
    assert sa['overflow_cases']==[]
    assert sa['custom_control_cases']==[{'path':'1','operation':'LOAD','returns_to':''}]
    # The continuation immediately following a normally-returning body repeats
    # the inner loop: 011 --strip two ones--> 0, whose next zero-padded leaf is 00.
    assert strip('011','1',2)=='0'
    # A zero tail exits the loop to LOAD without an ordinary root carry.
    assert inc(strip('00','0',1))=='1'
    output={'scope':__doc__,'provenance':{'ProveIt_commit':PROVEIT_SHA,
        'imported_upstream_commit':UPSTREAM_SHA,'path':'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v',
        'sha256':EXPECTED_SHA256,'attribution':'Mira-Cult source program, Jeff verification, Wade path compiler; ProveIt source snapshot.'},
        'original':oa,'post_fetch_body':ba,'custom_loader_shell':sa,
        'NP_accesses_in_body':0,'decision_pair_saving_with_custom_loader':6,
        'loader_stride':args.loader_stride,
        'semantic_loader_contract':f'At PC1, gap g and first physical register L=0: preserve all other registers; set L=g+1, gap=g+{args.loader_stride}; return to empty PC.',
        'attempt_schedule':f'For initially empty L and gap g0, candidate codes are g0 + {args.loader_stride}*k for k=0,1,2,... . Internal commands use tail-1.',
        'command_boundary_observation':('The physical gap equals the legacy next-candidate register; LOAD and the following positive CD L are internal to the first command segment.' if args.loader_stride==1 else 'Compare to the stride-two enumerator EnumParity254; the physical gap stores the next candidate code after loading.'),
        'relation_to_GapClock_lean':('GapClock.eager_halts_iff is the final unit-stride command-level comparison; it does not itself prove the binary-loader contract.' if args.loader_stride==1 else 'EnumParity254 supplies the separate stride-two completeness comparison, using cofinal parity candidates.'),
        'separate_obligations':['literal LOAD universal transducer proof','eight-logical-register layout with at least nine physical blocks','blank bootstrap','whole binary simulation'],
        'state_count_claim':False}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:{n:a[n] for n in ('unique_decision_pairs','unfolded_leaves','guarded_cases','maximum_leaf_depth','overflow_cases')}
                     for k,a in [('original',oa),('post_fetch_body',ba),('custom_loader_shell',sa)]},indent=2))

if __name__=='__main__':main()
