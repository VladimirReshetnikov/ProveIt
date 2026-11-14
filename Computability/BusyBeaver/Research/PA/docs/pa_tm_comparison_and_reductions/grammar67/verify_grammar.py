#!/usr/bin/env python3
"""Independently check the formula word and integer grammar upper bound.

No optimizer is imported. This verifier checks a finite grammar witness,
including every selected production, its exact expansion, the primitive
source lengths, and the existing PA196 macro boundary contracts. Physical
transition-table verification is a separate required stage.
"""
from collections import Counter
from functools import lru_cache
import hashlib
import ast
import json
from pathlib import Path
import re
import formula_word as f

HERE=Path(__file__).resolve().parent
def token(x):return tuple(x)if isinstance(x,list)else x
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(condition,message):
    if not condition:raise AssertionError(message)

def parse_nodes(p):
    out={}
    for line in p.read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        fields=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        children=[name if name else('leaf',op,int(arg)if arg else None)for op,arg,name in fields]
        check(len(children)==2,'Malformed source node '+m[1]);out[m[1]]=tuple(children)
    return out

def dictionary(data,expected):
    words=[tuple(map(token,w))for w in data['words']]
    prods={int(k):v for k,v in data['productions'].items()}
    @lru_cache(None)
    def expand(i):
        check(i in prods,'Undefined grammar nonterminal')
        result=[]
        for kind,value in prods[i]:
            if kind=='token':result.append(token(value))
            else:
                check(kind=='word','Unknown grammar atom')
                check(len(words[value])<len(words[i]),'Grammar dependency is not shorter')
                result.extend(expand(value))
        check(tuple(result)==words[i],'Production expands incorrectly at '+str(i))
        return tuple(result)
    for i in prods:expand(i)
    check(expand(data['root'])==tuple(expected),'Grammar root does not equal formula word')
    check(all(len(p)>=2 for p in prods.values()),'Unary/empty productions were not normalized')
    return words,prods,sum(len(p)-1 for p in prods.values())

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    metadata=json.loads((HERE/'metadata.json').read_text())
    for name,expected in metadata['input_sha256'].items():
        check(digest(HERE/name)==expected,'Input hash mismatch: '+name)
    nodes=parse_nodes(HERE/'inputs/pa196_Program.lean')
    def macro_word(t):
        if isinstance(t,str)and t.startswith('x'):
            a,b=nodes[t];return macro_word(a)+macro_word(b)
        return [t]
    baseline=macro_word('x67');candidate=f.candidate_word()
    check(baseline==f.baseline_word(),'Baseline symbolic word disagrees with pinned Lean source')
    check(len(baseline)==201 and len(candidate)==199,'Unexpected macro counts')
    @lru_cache(None)
    def primitive_word(t):
        if isinstance(t,str):return primitive_word(nodes[t])
        if len(t)==3:return(t,)
        return primitive_word(t[0])+primitive_word(t[1])
    @lru_cache(None)
    def boundary(t):
        if isinstance(t,str):return boundary(nodes[t])
        if len(t)==3:
            _,op,arg=t
            return(1 if op=='dec'else arg if op=='breakTo'else 0,
                   arg if op=='continueTo'else 0,op=='halt')
        a,b=map(boundary,t)
        return(max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2])
    for tok in set(candidate)-{f.BREAK}:
        check(boundary(tok)==(0,0,False),'AX macro is not closed: '+str(tok))
    check(candidate[-1]==f.BREAK,'Closing jump must remain last')
    outside=len(primitive_word('node172'))-sum(len(primitive_word(t))for t in baseline)
    old_sites=outside+sum(len(primitive_word(t))for t in baseline)
    new_sites=outside+sum(len(primitive_word(t))for t in candidate)
    check((outside,old_sites,new_sites)==(169,3812,3773),'Primitive source lengths disagree')
    data=json.loads((HERE/'inputs/grammar67.json').read_text())
    words,prods,rule_upper=dictionary(data,candidate)
    check(rule_upper==67,'Expected exact integer grammar upper bound 67')
    labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',(HERE/'inputs/pa196_Conjugacy.lean').read_text())[1])
    rows={}
    for line in (HERE/'inputs/pa196.tm').read_text().splitlines():
        q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=int(w),d,labels[int(n)]
    check(rows[99,0]==(0,'R',61)and rows[99,1]==(1,'R',61),'Existing inc/inc reader rows mismatch')
    check(nodes['node60']==(f.INC,f.INC),'Existing inc/inc source subtree mismatch')
    free_receipts=[]
    for name,word,expected in [('grammar_freeii66.json',candidate,66),('baseline_freeii67.json',baseline,67)]:
        d=json.loads((HERE/'inputs'/name).read_text());ww,pp,raw=dictionary(d,word)
        free=set(d['free_words']).intersection(pp)
        check(len(free)==1,'Expected one selected reusable reader')
        for i in free:
            check(ww[i]==(f.INC,f.INC),'Unrecognized free macro word')
            check(pp[i]==[['token',list(f.INC)],['token',list(f.INC)]],'Free reader has another production')
            check(d['free_word_readers'][str(i)]==99,'Wrong native reusable reader')
        check(raw-len(free)==expected,'New reader upper bound differs')
        free_receipts.append({'file':name,'macro_word_length':len(word),'binary_rule_upper_bound':raw,
                              'existing_readers_reused':1,'new_reader_upper_bound_before_routing':expected})
    delta=Counter(candidate);delta.subtract(Counter(baseline))
    out={'status':'PASS','upstream_commit':metadata['upstream_commit'],
         'macro_words':{'baseline':201,'candidate':199},
         'primitive_sites':{'outside_AX':169,'baseline':3812,'candidate':3773},
         'macro_multiset_delta':[[k,v]for k,v in delta.items()if v],
         'selected_dictionary_productions':len(prods),'binary_rule_upper_bound':rule_upper,
         'existing_reader_grammar_witnesses':free_receipts,
         'scope':'Exact source-word and grammar witness only; no physical TM state-count claim',
         'head_order_zero_based':f.HEAD_ORDER,'distribution_head_antecedents_exchanged':True}
    s=json.dumps(out,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(s)
    print(s,end='')

if __name__=='__main__':main()
