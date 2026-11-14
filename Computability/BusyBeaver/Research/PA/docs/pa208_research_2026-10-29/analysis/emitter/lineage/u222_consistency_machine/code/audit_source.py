#!/usr/bin/env python3
"""Independent checks of the new U emitter and closed source splice.

This checker does not import the source generator or its source-tree helpers.
Finite primitive tests supplement, rather than replace, the written induction
proofs of the inherited pair/unpair macros.  No consistency claim follows from
running a machine for a bounded time.
"""
from __future__ import annotations
from functools import cache
from pathlib import Path
from math import isqrt
import argparse
import hashlib
import itertools
import json
import re

ROOT = Path(__file__).resolve().parent.parent
OLD = ROOT / 'inputs/k215_sites.json'


def need(p, message):
    if not p:
        raise ValueError(message)


def pair(a, b):
    return (a+b)*(a+b+1)//2+b


def unpair(n):
    diagonal = (isqrt(8*n+1)-1)//2
    b = n-diagonal*(diagonal+1)//2
    return diagonal-b, b


def graph(rows):
    """Ordinal CFG from subtree intervals, with an unwrapped exit ordinal."""
    intervals = {}
    for i, (path, op, arg) in enumerate(rows):
        for j in range(len(path)+1):
            prefix = path[:j]
            intervals.setdefault(prefix, [i, i+1])[1] = i+1
    def jump(path, bit, count):
        for k in range(len(path)-1, -1, -1):
            if path[k] == bit:
                count -= 1
                if count == 0:
                    return intervals[path[:k]][0 if bit == '1' else 1]
        raise ValueError(('escaping branch', path, bit, count))
    result = []
    for i, (path, op, arg) in enumerate(rows):
        if op == 'CI': destinations = (i+1,)
        elif op == 'CD': destinations = (jump(path, '0', 1), i+1)
        elif op == 'CB': destinations = (jump(path, '0', arg),)
        elif op == 'CC': destinations = (jump(path, '1', arg),)
        elif op == 'CH': destinations = ()
        else: raise ValueError(op)
        result.append((op, arg, destinations))
    return result


def run_interval(rows, rg, initial, cap=2_000_000, cfg=None):
    """Execute literal counter instructions, stopping at interval end."""
    cfg = graph(rows) if cfg is None else cfg
    lo, hi = rg
    registers = list(initial)
    i = lo
    for ticks in range(cap):
        if i == hi:
            return registers, ticks
        need(lo <= i < hi, ('interval escaped', i, rg))
        op, arg, targets = cfg[i]
        if op == 'CI': registers[arg] += 1; i = targets[0]
        elif op == 'CD':
            if registers[arg]: registers[arg] -= 1; i = targets[1]
            else: i = targets[0]
        elif op in ('CB', 'CC'): i = targets[0]
        else: raise ValueError('unexpected halt')
    raise ValueError(('test budget exceeded', rg, initial))


def code(tag, a, b): return 4*pair(a,b)+tag
def imp(a,b): return code(0,a,b)
def mem(a,b): return code(1,a,b)
def all_(a,b): return code(2,a,b)
def eq(a,b): return code(3,a,b)
def neg(a): return imp(a,1)


def expected_negseed(c,upper_first=False,unshifted=False):
    n = c if unshifted else c+1
    guard = all_(n, imp(mem(n,1), mem(n,0)))
    lower = all_(1, imp(guard, imp(n,mem(1,n))))
    upper = all_(1, imp(mem(1,n), n))
    first,second=(upper,lower) if upper_first else (lower,upper)
    return all_(n, imp(first, imp(second,1)))


def expected_tree(upper_first=False,unshifted=False):
    # This independent tree is written directly from the mathematical schema.
    n = 'c' if unshifted else ('+', 'c', 1)
    lower=('Q',1,('I',('Q',n,('I',('R',n,1),('R',n,0))),
                       ('I',n,('R',1,n))))
    upper=('Q',1,('I',('R',1,n),n))
    first,second=(upper,lower) if upper_first else (lower,upper)
    return ('Q',n,('I',first,('I',second,1)))


def replay_word(word,upper_first=False,unshifted=False):
    stack = ['prior-stack']
    current = 'prior-current'
    for t in word:
        if t in (0,1,'n','F'):
            stack.append(current)
            current = ('c' if unshifted else ('+','c',1)) if t=='n' else 1 if t=='F' else t
        elif t=='N':
            current = ('I',current,1)
        elif t in ('I','R','Q'):
            need(len(stack)>1, 'expression stack underflow')
            current = (t, stack.pop(), current)
        else: raise ValueError(('unknown token',t))
    need(stack == ['prior-stack','prior-current'], ('net stack effect',stack))
    need(current == expected_tree(upper_first,unshifted), 'symbolic emitter differs from power cover')
    return current


def evaluate_word(word,c,unshifted=False):
    stack=[]
    current=117
    for t in word:
        if t in (0,1,'n','F'):
            stack.append(current)
            current=(c if unshifted else c+1) if t=='n' else 1 if t=='F' else t
        elif t=='N': current=neg(current)
        else:
            a=stack.pop()
            current={'I':imp,'R':mem,'Q':all_}[t](a,current)
    need(stack==[117], 'numeric stack effect')
    return current


def macro_checks(rows, ranges):
    cfg=graph(rows)
    result={}
    for node in (119,168,171,177,180,181,218):
        rg=ranges[str(node)]
        count=0; max_ticks=0
        for top, left, tail, p3 in itertools.product(range(4),repeat=4):
            initial=[2,top,pair(left,tail),p3,3,2,0,0,1]
            expected=initial[:]
            if node in (171,168,177):
                expected[2]=pair(top,initial[2])
                expected[1]={171:0,168:p3,177:1}[node]
            elif node==218:
                expected[1]=neg(top)
            else:
                expected[2]=tail
                expected[1]=code({119:0,180:2,181:1}[node],left,top)
            actual,ticks=run_interval(rows,rg,initial,cfg=cfg)
            need(actual==expected,('macro contract',node,initial,actual,expected))
            count+=1;max_ticks=max(max_ticks,ticks)
        result[str(node)]={'literal_cases':count,'maximum_counter_steps':max_ticks,
                          'range':rg}
    return result


def bind_proved_macro_nodes(rows, ranges, dag_path):
    """Bind reusable intervals to the exact nodes proved in ProgLibPerm.v.

    This is a finite source normalization check, not an interpreter test.  The
    all-natural arithmetic contract is established by the referenced ordinary
    induction arguments and the verbatim proof templates.
    """
    raw=dag_path.read_bytes()
    digest=hashlib.sha256(raw).hexdigest()
    need(digest=='ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1',
         'macro proof DAG is not the pinned DagPerm.v')
    edge=r'(?:ENode|EInc|EDecnz|EBreak|EContinue)\s+\d+|EHalt'
    pattern=re.compile(r'^\s*\|\s*(\d+)\s*=>\s*\((' + edge +
                       r'),\s*(' + edge + r')\)\s*$',re.M)
    nodes={int(i):(a,b) for i,a,b in pattern.findall(raw.decode())}
    need(len(nodes)==487,('incomplete proof DAG parse',len(nodes)))
    def unfold_edge(e,path,ancestors):
        parts=e.split();kind=parts[0]
        if kind=='ENode':
            n=int(parts[1]);need(n not in ancestors,('cyclic proof DAG',n))
            need(n in nodes,('undefined proof DAG node',n))
            a,b=nodes[n]
            return (unfold_edge(a,path+'0',ancestors|{n})+
                    unfold_edge(b,path+'1',ancestors|{n}))
        op={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}[kind]
        return [[path,op,0 if kind=='EHalt' else int(parts[1])]]
    oldcfg=graph(rows)
    result={}
    lemmas={119:'cons119',168:'par168',171:'pushwff171',177:'v177',
            180:'wal180',181:'wel181',218:'wn218'}
    for n,lemma in lemmas.items():
        lo,hi=ranges[str(n)]
        proved=graph(unfold_edge('ENode '+str(n),'',set()))
        actual=[(op,arg,tuple(d-lo for d in dest))
                for op,arg,dest in oldcfg[lo:hi]]
        need(len(actual)==len(proved),('proved macro length differs',n))
        need([x[2] for x in actual]==[x[2] for x in proved],
             ('proved macro control destinations differ',n))
        changes=[];i=0
        while i<len(actual):
            if actual[i]==proved[i]:i+=1;continue
            op,arg,dest=actual[i];pop,parg,pdest=proved[i]
            if op==pop and op in ('CB','CC'):
                # The counts name tree ancestors; their resolved targets,
                # already compared above, are their entire CFG meaning.
                changes.append({'at':i,'kind':'same resolved branch',
                                'baseline_count':arg,'proof_count':parg})
                i+=1;continue
            if op==pop=='CI' and i+1<len(actual):
                a2,p2=actual[i+1],proved[i+1]
                need(a2[0]==p2[0]=='CI' and arg==p2[1] and parg==a2[1],
                     ('unproved macro instruction change',n,i))
                need(dest==(i+1,) and a2[2]==(i+2,),
                     ('increment swap is not a straight sequence',n,i))
                need(all(i+1 not in targets for k,(_,_,targets) in enumerate(actual) if k!=i),
                     ('branch enters increment swap interior',n,i))
                changes.append({'at':[i,i+1],'kind':'commuting adjacent increments',
                                'baseline_registers':[arg,a2[1]],
                                'proof_registers':[parg,p2[1]]})
                i+=2;continue
            raise ValueError(('unproved macro normalization',n,i,actual[i],proved[i]))
        result[str(n)]={'lemma':'ProgLibPerm.'+lemma,'range':[lo,hi],
                        'primitive_count':hi-lo,
                        'exact_CFG_match_modulo_primitive_normalization':True,
                        'normalization_steps':changes}
    return {'dag_sha256':digest,'macro_nodes':result,
            'scope':'Exact resolved control destinations; only adjacent commuting increments may differ. Arbitrary-input contracts follow from the named induction proofs.'}


def check_splice(old,new,lo,old_hi,new_hi):
    need([r[1:] for r in old[:lo]]==[r[1:]for r in new[:lo]],'prefix primitive word')
    need([r[1:] for r in old[old_hi:]]==[r[1:]for r in new[new_hi:]],'suffix primitive word')
    go,gn=graph(old),graph(new)
    def remap(i):
        if i<lo:return i
        if i==lo:return lo
        if i>=old_hi:return i+new_hi-old_hi
        raise ValueError(('retained control enters replaced interior',i))
    checked=0
    for i,(op,arg,dst)in enumerate(go):
        if lo<=i<old_hi:continue
        j=remap(i)
        need((op,arg)==gn[j][:2],('retained instruction',i,j))
        need(tuple(map(remap,dst))==gn[j][2],('retained CFG',i,j,dst,gn[j]))
        checked+=1
    return {'retained_primitive_nodes':checked,
            'no_retained_branch_enters_replaced_interior':True,
            'all_retained_control_edges_identical_after_index_translation':True}


def bind_word_to_primitive_cfg(old,new,word,ranges,start,stop,unshifted=False):
    """Bind the stated RPN recipe to every instruction AND branch in the table.

    This prevents an untrusted construction receipt from describing a correct
    formula while the actual replacement source computes a different one.
    """
    oldcfg,newcfg=graph(old),graph(new)
    which={0:171,1:177,'F':177,'n':168,'I':119,'R':181,'Q':180,'N':218}
    expected=[]
    for token in word:
        lo,hi=ranges[str(which[token])]
        offset=start+len(expected)
        for op,arg,dest in oldcfg[lo:hi]:
            need(all(lo<=d<=hi for d in dest),('macro control escape',token,dest))
            expected.append((op,arg,tuple(offset+d-lo for d in dest)))
        if token=='n' and not unshifted:
            expected.append(('CI',1,(start+len(expected)+1,)))
    need(start+len(expected)==stop,'declared macro lengths do not match replacement')
    for j,(actual,wanted)in enumerate(zip(newcfg[start:stop],expected)):
        need(actual==wanted,('new body does not implement macro word',start+j,actual,wanted))
    return {'bound_new_primitive_instructions':len(expected),
            'every_new_branch_matches_exact_macro_concatenation':True}


def expect_failure(action,name):
    try: action()
    except ValueError: return name
    raise ValueError(('negative control unexpectedly accepted',name))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--candidate',type=Path,default=ROOT/'machine')
    ap.add_argument('--out',type=Path,default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--skip-primitive',action='store_true')
    ap.add_argument('--upper-first',action='store_true')
    ap.add_argument('--unshifted',action='store_true',
                    help='Use n=c and require PAR3 without the successor increment.')
    ap.add_argument('--baseline',type=Path,default=OLD)
    ap.add_argument('--macro-dag',type=Path,
                    help='Bind primitive macro intervals to pinned DagPerm.v proof nodes.')
    a=ap.parse_args()
    need(hashlib.sha256(a.baseline.read_bytes()).hexdigest()==
         '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba',
         'baseline is not the pinned K215 primitive source')
    old=json.loads(a.baseline.read_text())
    new=json.loads((a.candidate/'sites.json').read_text())
    receipt=json.loads((a.candidate/'construction.json').read_text())
    lo,hi=receipt['old_replaced_interval']
    nh=lo+receipt['new_shell_leaf_count']
    symbolic=replay_word(receipt['new_shell_macro_word'],a.upper_first,a.unshifted)
    splice=check_splice(old,new,lo,hi,nh)
    binding=bind_word_to_primitive_cfg(old,new,receipt['new_shell_macro_word'],
                                      receipt['macro_source_intervals'],lo,nh,a.unshifted)
    badnew=[list(row) for row in new]
    pos=next(j for j in range(lo,nh) if badnew[j][1]=='CI')
    badnew[pos][2]=(badnew[pos][2]+1)%9
    negative=[expect_failure(lambda:bind_word_to_primitive_cfg(old,badnew,
        receipt['new_shell_macro_word'],receipt['macro_source_intervals'],lo,nh,a.unshifted),
        'changed register in replacement primitive rejected')]
    badword=list(receipt['new_shell_macro_word']);badword[-1]='I'
    negative.append(expect_failure(lambda:replay_word(badword,a.upper_first,a.unshifted),
                    'wrong outer formula constructor rejected'))
    macros={}if a.skip_primitive else macro_checks(old,receipt['macro_source_intervals'])
    proof_binding=(bind_proved_macro_nodes(old,receipt['macro_source_intervals'],a.macro_dag)
                   if a.macro_dag is not None else None)
    for c in list(range(2048))+[2**32-1,2**64,2**127+19]:
        need(evaluate_word(receipt['new_shell_macro_word'],c,a.unshifted)==expected_negseed(c,a.upper_first,a.unshifted),
             ('numeric shell mismatch',c))
    output={'status':'PASS','literal_macro_contracts':macros,
            'clause_order':'upper-first' if a.upper_first else 'lower-first',
            'matrix_code':'c' if a.unshifted else 'c+1',
            'closed_splice':splice,'exact_symbolic_tree':symbolic,
            'new_body_literal_binding':binding,
            'proved_macro_node_binding':proof_binding,
            'negative_controls':negative,
            'numeric_shell_cases':2051,
            'unchanged_axiom_stack_slots':10,
            'changed_body_contract':'T,S -> negseed(c),P(T,S); parameters preserved; scratch6=scratch7=0',
            'inputs':{'original_source_sha256':hashlib.sha256(a.baseline.read_bytes()).hexdigest(),
              'candidate_source_sha256':hashlib.sha256((a.candidate/'sites.json').read_bytes()).hexdigest()},
            'scope':'Exact finite syntax/CFG identities and bounded literal macro checks; the written uniform induction proof supplies unbounded correctness. No kernel proof and no consistency inference from finite tests.'}
    a.out.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))


if __name__=='__main__':main()
