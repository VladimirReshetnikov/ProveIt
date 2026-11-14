#!/usr/bin/env python3
"""Independent logical/source/startup binding audit for a distributed AX package.

This does not import its compiler or runtime checker. It parses the complete
delivered Lean Tree data, resolves every control edge by subtree intervals,
and compares the revised macro word and the unchanged outer source. Physical
arbitrary-register simulation remains the separate runtime certificate's job.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import hashlib
import json
import re
import distributed_gate as d
from verify_selected_word import short

def token_short(token):return short(list(token) if isinstance(token,tuple) else token)

def parse_program(text):
    definitions={}
    for name,expr in re.findall(r'^def (\w+) : Tree := (.+)$',text,re.M):
        tokens=re.findall(r'\(|\)|\.[A-Za-z]+|[A-Za-z0-9_]+',expr)
        cursor=0
        def take():
            nonlocal cursor
            d.require(cursor<len(tokens),'Truncated Tree expression')
            t=tokens[cursor];cursor+=1
            return t
        def term():
            t=take()
            if t=='(':
                v=term();d.require(take()==')','Unbalanced Tree parentheses');return v
            if t=='.node':return term(),term()
            if t=='.leaf':
                d.require(take()=='(','Malformed leaf')
                op=take()[1:]
                d.require(op in {'inc','dec','halt','continueTo','breakTo'},'Unknown primitive')
                n=None if op=='halt' else int(take())
                d.require(take()==')','Malformed leaf close')
                return 'leaf',op,n
            d.require(t in definitions,'Undefined Tree reference '+t)
            return t
        definitions[name]=term()
        d.require(cursor==len(tokens),'Unparsed Tree expression suffix')
    d.require('trie' in definitions and 'node172' in definitions,'Missing complete source root')
    return definitions

def expand(root,definitions,replacements=None):
    replacements={} if replacements is None else replacements
    @lru_cache(None)
    def rec(t):
        if isinstance(t,str):return rec(replacements.get(t,definitions[t]))
        if len(t)==3:return t
        return rec(t[0]),rec(t[1])
    return rec(root)

def grammar_tree(data):
    rules=data['rules']
    @lru_cache(None)
    def rec(t):
        if isinstance(t,str) and t in rules:return tuple(rec(freeze(v)) for v in rules[t])
        return t
    return rec(data['root'])

def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x

def sites(tree):
    out=[]
    def walk(t,path):
        if len(t)==3:out.append((path,t[1],t[2]));return
        walk(t[0],path+(0,));walk(t[1],path+(1,))
    walk(tree,())
    return out

def instructions(flat):
    # Each subtree occupies a contiguous half-open interval of leaf ordinals.
    intervals={}
    for i,(path,_,_) in enumerate(flat):
        for depth in range(len(path)+1):
            prefix=path[:depth]
            if prefix not in intervals:intervals[prefix]=[i,i+1]
            else:intervals[prefix][1]=i+1
    def ancestor(path,side,count):
        choices=[k for k,v in enumerate(path) if v==side]
        d.require(count>0 and len(choices)>=count,'Invalid relative control depth')
        return path[:choices[-count]]
    out=[]
    for i,(path,op,arg) in enumerate(flat):
        if op=='inc':ins=('inc',arg,i+1)
        elif op=='dec':ins=('dec',arg,intervals[ancestor(path,0,1)][1],i+1)
        elif op=='continueTo':ins=('jump',intervals[ancestor(path,1,arg)][0])
        elif op=='breakTo':ins=('jump',intervals[ancestor(path,0,arg)][1])
        else:ins=('halt',)
        d.require(all(0<=v<len(flat) for v in targets(ins)),'Control leaves the source')
        out.append(ins)
    return out

def targets(ins):
    return ins[2:] if ins[0] in ('inc','dec') else ins[1:] if ins[0]=='jump' else ()

def retarget(ins,f):
    cut=2 if ins[0] in ('inc','dec') else 1
    return ins[:cut]+tuple(f(v) for v in ins[cut:])

def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,direction,n=line.split();key=int(q),int(b)
        d.require(key not in rows,'Duplicate transition row')
        d.require(direction in ('L','R') and int(b) in (0,1) and int(w) in (0,1),'Nonbinary row')
        rows[key]=int(w),direction=='R',int(n)
    return rows

def audit(candidate,source,selected):
    basebytes=(source/'PA196/Program.lean').read_bytes()
    blockbytes=(source/'PA196/Source/AXProgram.lean').read_bytes()
    d.require(hashlib.sha256(basebytes).hexdigest()==d.PROGRAM_HASH,'Baseline source pin')
    d.require(hashlib.sha256(blockbytes).hexdigest()==d.AX_HASH,'Baseline blocks pin')
    baseline=parse_program(basebytes.decode())
    delivered=parse_program((candidate/'Program.lean').read_text())
    grammar=grammar_tree(json.loads((candidate/'grammar.json').read_text()))
    expanded=expand(grammar,baseline)
    complete=expand('trie',delivered)
    d.require(complete==expand('trie',baseline,{'x67':grammar}),'Whole delivered root is not the patched pinned source')
    d.require(expand('x67',delivered)==expanded,'Delivered AX is not the complete grammar')
    def macro_word(t):
        if isinstance(t,str) and t in ('node60','node61'):return macro_word(baseline[t])
        if isinstance(t,tuple) and len(t)==2:return macro_word(t[0])+macro_word(t[1])
        return [t]
    emitted_word=macro_word(grammar)
    expected=freeze(json.loads(selected.read_text()))
    d.require(tuple(emitted_word)==expected,'Grammar is not the mathematically audited selected word')
    d.require(freeze(json.loads((candidate/'selected-word.json').read_text()))==expected,'Package selected word mismatch')
    oldsites=sites(expand('trie',baseline));newsites=sites(complete)
    oldins=instructions(oldsites);newins=instructions(newsites)
    emitted=json.loads((candidate/'sites.json').read_text())
    expected_sites=[{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':arg,'instruction':list(newins[i])}
                    for i,(p,op,arg) in enumerate(newsites)]
    d.require(emitted==expected_sites,'Complete source/path/control graph differs from emitted certificate')
    block_text=blockbytes.decode().split('def blocks :',1)[1].split('def program :',1)[0]
    blocks=[(d.TOKEN[n],int(a),int(b)) for n,a,b in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',block_text)]
    oldstart,oldend=blocks[0][1],blocks[-1][2]
    patterns={};lengths={};reference={}
    for token,start,end in blocks:
        pattern=tuple(retarget(ins,lambda n:n-start) for ins in oldins[start:end])
        if token in patterns:d.require(pattern==patterns[token],'Baseline macro has context-dependent ordinal control')
        patterns[token]=pattern;lengths[token]=end-start;reference[token]=(start,end)
        if token!='J':d.require(all(0<=n<=end-start for ins in pattern for n in targets(ins)),
                                'Ordinary baseline macro has external control')
    newend=oldstart+sum(lengths[token_short(t)] for t in emitted_word)
    shift=newend-oldend
    def relocate(n):
        if n<=oldstart:return n
        if n>=oldend:return n+shift
        raise ValueError('Exterior control targets an interior AX instruction')
    for oldindex in list(range(oldstart))+list(range(oldend,len(oldsites))):
        newindex=relocate(oldindex)
        d.require(oldsites[oldindex]==newsites[newindex],'An exterior primitive/path changed')
        d.require(retarget(oldins[oldindex],relocate)==newins[newindex],'An exterior control edge changed')
    cursor=oldstart
    for raw in emitted_word:
        token=token_short(raw);start,end=reference[token]
        d.require([(op,arg) for _,op,arg in newsites[cursor:cursor+lengths[token]]]
                  ==[(op,arg) for _,op,arg in oldsites[start:end]],'A macro primitive expansion changed')
        expected_ins=tuple(retarget(ins,relocate) for ins in oldins[start:end]) if token=='J' else \
            tuple(retarget(ins,lambda n:n+cursor) for ins in patterns[token])
        d.require(expected_ins==tuple(newins[cursor:cursor+lengths[token]]),'A macro relative control edge changed')
        cursor+=lengths[token]
    d.require(cursor==newend and len(newsites)==3773 and shift==-39,'Source counts mismatch')
    # Reproduce the whole finite tape after blank startup, without its runtime.
    table=read_table(candidate/'candidate.tm');labels=json.loads((candidate/'labels.json').read_text())
    d.require(labels[0]==74 and labels[-1]==254,'Startup/halting label mismatch')
    q=0;head=0;ones=set();trace=hashlib.sha256()
    for step in range(58154):
        d.require(q<len(labels)-1,'Early blank-tape halt')
        bit=int(head in ones);w,right,n=table[q,bit]
        trace.update(f'{q},{head},{bit},{w},{int(right)},{n}\n'.encode())
        (ones.add if w else ones.discard)(head);head+=1 if right else -1;q=n
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    path=newsites[25][0];expected_ones={-3}|{-2+i for i,v in enumerate(path) if v}|{46}
    pos=47
    for v in physical:pos+=1;expected_ones.update(range(pos,pos+v+1));pos+=v+1
    d.require(q==labels.index(84) and head==-2 and ones==expected_ones,'Full blank startup frame mismatch')
    receipt={
        'result':'passed independent whole-source binding and startup audit',
        'working_states':len(labels)-1,'macro_tokens':len(emitted_word),'source_sites':len(newsites),
        'outside_ax_sites':len(oldsites)-(oldend-oldstart),'source_site_reduction':-shift,
        'whole_delivered_trie_bound':True,'all_primitive_control_edges_checked':True,
        'ordinary_macro_control_graphs_unchanged':True,'final_close_relocated':True,
        'selected_word_sha256':hashlib.sha256(selected.read_bytes()).hexdigest(),
        'new_top_to_bottom':['h5','h4','h3','h2','h6_exchanged','h1','rho8','generalization','saved'],
        'startup':{'steps':58154,'native_state':labels[q],'head':head,'source_site':25,
                   'source_path':list(path),'complete_tape_equal':True,'trace_sha256':trace.hexdigest()},
        'hashes':{name:hashlib.sha256((candidate/name).read_bytes()).hexdigest()
                  for name in ['Program.lean','grammar.json','candidate.tm','sites.json']},
        'scope':'Independent source/control and concrete startup checks; arbitrary-register physical simulation is a separate certificate.'}
    return receipt

if __name__=='__main__':
    here=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidate',type=Path)
    ap.add_argument('--source',type=Path,default=here/'inputs/BusyBeaver')
    ap.add_argument('--selected',type=Path,default=here/'selected_word.json')
    ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    output=json.dumps(audit(args.candidate,args.source,args.selected),indent=2)+'\n'
    if args.receipt:args.receipt.write_text(output)
    print(output,end='')
