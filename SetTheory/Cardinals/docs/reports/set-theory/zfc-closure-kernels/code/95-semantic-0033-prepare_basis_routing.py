#!/usr/bin/env python3
"""Prepare a genuinely changed AX program for the existing routed framework.

This is a separate experiment, not an exception to the production checker:
production rightly requires original-program equivalence.  Here equivalence
is instead to the new emitted basis program and needs its own logic/program
bridge.  The generic grammar search may read these inputs without modification.
"""
from functools import cache
import json
from pathlib import Path
import random
import sys

import basis_experiment as b

P = b.OUT / 'vendor/route245'
O = b.OUT
SOURCE = json.loads((P/'inputs/closed-sequence-grammar-next22.json').read_text())
SYMBOLS = json.loads((P/'inputs/semantic-symbols.json').read_text())
ENCODE = {name: char for char,name in SYMBOLS.items()}
DATA = json.loads((P/'grammar.json').read_text())
RULES = {w:(a,c) for w,a,c in DATA['rules']}
NAMES = {int(q):''.join(ENCODE[x] for x in row)
         for q,row in SOURCE['flattened_semantic_words'].items()}
OLD_AX = NAMES[76]
BY_AST = {int(i):NAMES[int(q)] for q,i in SOURCE['sequence_ast_roots'].items()}
PERMIT = {ch:int(mask) for ch,mask in map(str.split,
          (P/'inputs/semantic.txt').read_text().splitlines()[-len(SYMBOLS):])}

def join(a,c):
    return 1+a[0], max(1+a[0],a[1],c[1]), 1+max(a[2],c[2])

@cache
def prop_ast(i):
    if i in BY_AST:
        return prop_word(BY_AST[i])
    r = SOURCE['ast_dag'][i]
    return (0,0,0) if r[0]=='L' else join(prop_ast(r[1]),prop_ast(r[2]))

@cache
def prop_word(w):
    return prop_ast(SOURCE['atoms'][SYMBOLS[w]]['ast']) if len(w)==1 else join(*(prop_word(x) for x in RULES[w]))

def needed(roots, rules=RULES):
    result=set()
    def visit(w):
        if len(w)==1 or w in result:return
        result.add(w)
        for c in rules[w]:visit(c)
    for r in roots:visit(r)
    return result

BASE_ROOTS = [w for w in DATA['roots'] if w!=OLD_AX]+[x['word'] for x in DATA['routes']]
BASE_NEEDED = needed(BASE_ROOTS)
CANDIDATES = list(RULES)+list(SYMBOLS)
EXPANDED = {w:b.expansion(w) for w in CANDIDATES}
ADDED = {w:len(needed([w])-BASE_NEEDED) if len(w)>1 else 0 for w in CANDIDATES}

def segment(raw, penalty=0.0):
    target=b.expansion(raw)
    n=len(target)
    choice=[None]*(n+1)
    choice[-1]=(0.,[])
    for i in range(n-1,-1,-1):
        for w,x in EXPANDED.items():
            j=i+len(x)
            if j>n or choice[j] is None or target[i:j]!=x:continue
            if j<n and prop_word(w)[0]>=6:continue
            score=1+penalty*ADDED[w]+choice[j][0]
            if choice[i] is None or score<choice[i][0]:
                choice[i]=(score,[w]+choice[j][1])
    if choice[0] is None:raise ValueError('No legal segmentation')
    chunks=choice[0][1]
    assert b.expansion(''.join(chunks))==target
    return chunks

def assemble(chunks):
    # Optimize depth over binary parenthesizations, retaining every old node.
    @cache
    def build(lo,hi):
        w=''.join(chunks[lo:hi])
        if hi==lo+1:return prop_word(w),w,{}
        if w in RULES:return prop_word(w),w,{}
        best=None
        for k in range(lo+1,hi):
            left=build(lo,k)
            right=build(k,hi)
            if left is None or right is None:continue
            a,l,gl=left
            c,r,gr=right
            if (len(l)==1 and not PERMIT[l]&1) or (len(r)==1 and not PERMIT[r]&2):continue
            p=join(a,c)
            if p[1]>6 or p[2]>64:continue
            g={**gl,**gr,w:(l,r)}
            value=(len(g),p[2],p[0])
            if best is None or value<best[0]:best=(value,p,w,g)
        return None if best is None else best[1:]
    result=build(0,len(chunks))
    if result is None:raise ValueError('No six-zero binary assembly')
    props,root,new=result
    rules={**RULES,**new}
    def properties(w):
        if len(w)==1:return prop_word(w)
        return join(*(properties(c) for c in rules[w]))
    # The external path adds one leading zero before entering AX. Rotate only
    # the new AX root to preserve the inherited global six-zero condition.
    while properties(root)[0]>5:
        left,right=rules[root]
        if len(left)==1:raise ValueError('AX leading-zero repair reached an atom')
        aa,bb=rules[left]
        tail=bb+right
        rules[tail]=(bb,right)
        rules[root]=(aa,tail)
    props=properties(root)
    active=needed(BASE_ROOTS+[root],rules)
    return root,{w:rules[w] for w in active},props

def write_inputs(label, root, rules, props):
    folder=O/('routing_'+label)
    folder.mkdir(exist_ok=True)
    roots=[root if w==OLD_AX else w for w in DATA['roots']]
    lines=[f'{len(rules)} {len(roots)} {len(SYMBOLS)}']
    lines += [f'{len(a)} {w} {i}' for i,(w,(a,c)) in enumerate(sorted(rules.items()))]
    lines+=roots+[f'{ch} {mask}' for ch,mask in sorted(PERMIT.items())]
    (folder/'grammar.txt').write_text('\n'.join(lines)+'\n')
    text=(P/'inputs/state_reduction/route-constraints.txt').read_text()
    assert ('W '+OLD_AX+'\n') in text
    (folder/'constraints.txt').write_text(text.replace('W '+OLD_AX+'\n','W '+root+'\n'))
    # New source does not change the startup's retained projection witnesses.
    boot=(P/'inputs/state_reduction/bootstrap-lock54.txt').read_text()
    assert OLD_AX not in boot
    (folder/'boot.txt').write_text(boot)
    resume=[str(len(rules))]+[f'{len(a)} {w}' for w,(a,c) in sorted(rules.items())]
    resume += [str(len(DATA['routes']))]+[x['word'] for x in DATA['routes']]
    (folder/'resume.txt').write_text('\n'.join(resume)+'\n')
    (folder/'new_source.json').write_text(json.dumps(dict(
        logical_source_label=label, old_AX_word=OLD_AX, new_AX_word=root,
        exact_fine_emission=True, initial_grammar_rules=len(rules),
        framework_working_states=117, estimated_total_working_states=117+len(rules),
        new_AX_tree_properties=props, distinct_closed_operations=len(b.expansion(root)),
        new_program_bridge_required=True, production_checker_bypassed=False,
        production_checker_applicable=False),indent=2)+'\n')
    return folder

def main():
    results=json.loads((O/'basis_results.json').read_text())['results']
    for entry in results:
        if entry['label']=='old':continue
        best=None
        for penalty in (0.,0.05,0.1,0.2,0.4,0.8,1.,2.):
            try:
                chunks=segment(entry['semantic_AX_word'],penalty)
                root,rules,props=assemble(chunks)
            except ValueError:continue
            if best is None or len(rules)<len(best[1]):best=(root,rules,props,len(chunks),penalty)
        if best is None:raise ValueError(entry['label'])
        root,rules,props,nchunks,penalty=best
        folder=write_inputs(entry['label'],root,rules,props)
        print(entry['label'],len(rules),117+len(rules),'chunks',nchunks,'penalty',penalty,'props',props,folder)

if __name__=='__main__':main()
