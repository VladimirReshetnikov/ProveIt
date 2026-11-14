#!/usr/bin/env python3
"""Independent symbolic/CFG audit of the 202-DAG-node power-cover source.

This checker imports neither the source constructor nor the search heuristic.
It binds the literal primitive CFG to the independently stated constructor
word and checks every instruction/control edge outside the replaced shell.
"""
from pathlib import Path
import argparse, hashlib, itertools, json
from functools import cache

PIN='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
RANGES={'m168':[107,133],'m171':[26,45],'m177':[995,1015],
        'm119':[78,105],'m180':[78,107],'m181':[695,723],'m218':[995,1042]}
TOKEN={'m168':'c','m171':'0','m177':'1','m119':'I','m180':'Q','m181':'R','m218':'N'}


def require(p, msg):
    if not p:raise ValueError(msg)


def syntax(rows):
    instructions={p:(o,a) for p,o,a in rows}
    require(len(instructions)==len(rows),'duplicate source address')
    require(all(p and set(p)<={'0','1'} for p in instructions),'bad source address')
    prefixes={p[:j] for p in instructions for j in range(len(p))}
    require(not prefixes&instructions.keys(),'source not prefix-free')
    require(all(p+b in prefixes or p+b in instructions for p in prefixes for b in '01'),'incomplete tree')
    def build(p):
        if p in instructions:return ('leaf',)+instructions[p]
        return ('node',build(p+'0'),build(p+'1'))
    root=build('')
    require([p for p,_,_ in rows]==sorted(instructions),'noncanonical order')
    unique=set()
    def visit(t):
        if t in unique:return
        unique.add(t)
        if t[0]=='node':visit(t[1]);visit(t[2])
    visit(root)
    return {'dag_nodes':len(unique),'leaf_occurrences':len(rows),
            'maximum_depth':max(map(len,instructions)),
            'maximum_zero_run':max(len(s) for p in instructions for s in p.split('1'))}


def cfg(rows):
    bounds={}
    for i,(path,op,arg) in enumerate(rows):
        for j in range(len(path)+1):
            p=path[:j]
            if p not in bounds:bounds[p]=[i,i+1]
            else:bounds[p][1]=i+1
    out=[]
    for i,(path,op,arg) in enumerate(rows):
        if op=='CI':dest=(i+1,)
        elif op=='CH':dest=()
        else:
            require(op in ('CD','CB','CC'),('unknown instruction',op))
            which='1' if op=='CC' else '0'
            n=arg if op!='CD' else 1
            require(type(n)==int and n>=1,'invalid ancestor count')
            positions=[j for j,c in enumerate(path) if c==which]
            require(n<=len(positions),('escaping branch',path,op,arg))
            ancestor=path[:positions[-n]]
            target=bounds[ancestor][0 if op=='CC' else 1]
            dest=(target,i+1) if op=='CD' else (target,)
        out.append((op,arg,dest))
    return out

@cache
def node_size(node):
    return 1 if node[0]=='leaf' else node_size(node[1])+node_size(node[2])

@cache
def boundary(node):
    if node[0]=='leaf':
        _,op,arg=node
        return (1 if op=='CD' else arg if op=='CB' else 0,
                arg if op=='CC' else 0,op=='CH')
    a,b=boundary(node[1]),boundary(node[2])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2] or b[2]

def literal_tree(rows):
    d={p:('leaf',o,a) for p,o,a in rows}
    intervals={}
    def rec(p,start):
        if p in d:
            t=d[p]
        else:
            left=rec(p+'0',start)
            right=rec(p+'1',start+node_size(left))
            t=('node',left,right)
        intervals[start,start+node_size(t)]=t
        return t
    return rec('',0),intervals

def canonical_macro(root,lo,hi):
    factors=[]
    def rec(node,start):
        end=start+node_size(node)
        if end<=lo or start>=hi:return
        if lo<=start and end<=hi:
            require(boundary(node)==(0,0,False),'a macro factor is not closed')
            factors.append(node);return
        require(node[0]=='node','macro partially intersects a primitive')
        rec(node[1],start);rec(node[2],start+node_size(node[1]))
    rec(root,0)
    require(sum(map(node_size,factors))==hi-lo,'macro interval incomplete')
    out=factors[-1]
    for t in reversed(factors[:-1]):out=('node',t,out)
    return out

def expand_recipe(expr,macros):
    if isinstance(expr,str):return macros[expr]
    require(isinstance(expr,list) and len(expr)==2,'invalid parenthesization')
    return ('node',expand_recipe(expr[0],macros),expand_recipe(expr[1],macros))


def flatten(expr):
    if isinstance(expr,str):
        require(expr in TOKEN,('unsupported macro',expr));return [expr]
    require(isinstance(expr,list) and len(expr)==2,'invalid recipe node')
    return flatten(expr[0])+flatten(expr[1])


def tree(word):
    stack=['prior-stack'];current='prior-current'
    for x in word:
        if x in ('c','0','1'):
            stack.append(current);current=x
        elif x=='N':current=('I',current,'F')
        else:
            require(x in ('I','R','Q') and len(stack)>1,'invalid constructor')
            current=(x,stack.pop(),current)
    require(stack==['prior-stack','prior-current'],'wrong net stack effect')
    return current


def check(old_path,u222_path,new_path,recipe_path):
    old_raw=old_path.read_bytes()
    require(hashlib.sha256(old_raw).hexdigest()==PIN,'incorrect K215 source')
    old=json.loads(old_raw);base=json.loads(u222_path.read_text());new=json.loads(new_path.read_text());recipe=json.loads(recipe_path.read_text())
    metrics=syntax(new)
    require(metrics=={'dag_nodes':202,'leaf_occurrences':3891,'maximum_depth':45,'maximum_zero_run':6},('unexpected metrics',metrics))
    require(recipe['expected_metrics']==metrics,'recipe metrics differ')
    require(recipe['expected_source_sha256']==hashlib.sha256(new_path.read_bytes()).hexdigest(),'recipe source hash differs')
    require(recipe['replace_interval']==[2885,4482],'unexpected original interval')
    for name,span in RANGES.items():require(recipe['macro_intervals'][name[1:]]==span,('macro definition changed',name))
    macros=flatten(recipe['replacement']);word=[TOKEN[m] for m in macros]
    c='c';e=('R','1',c);g=('Q',c,('I',('R',c,'1'),('R',c,'0')))
    u=('Q','1',('I',e,c));l=('Q','1',('I',g,('I',c,e)))
    lp=('Q','1',('I',c,('I',g,e)))
    expected=('Q',c,('I',u,('I',lp,'F')))
    original=('Q',c,('I',l,('I',u,'F')))
    require(tree(word)==expected,('actual constructor word has wrong symbolic meaning',word,tree(word)))
    oc,bc,nc=cfg(old),cfg(base),cfg(new)
    expected_cfg=[];start=2885
    for macro in macros:
        lo,hi=RANGES[macro];offset=start+len(expected_cfg)
        for op,arg,dst in oc[lo:hi]:
            require(op!='CH' and all(lo<=x<=hi for x in dst),('macro is not closed',macro))
            expected_cfg.append((op,arg,tuple(offset+x-lo for x in dst)))
    stop=start+len(expected_cfg)
    require(stop==3622,'incorrect shell length')
    oldtree,_=literal_tree(old);_,new_intervals=literal_tree(new)
    macro_trees={name:canonical_macro(oldtree,*span) for name,span in RANGES.items()}
    expansion=expand_recipe(recipe['replacement'],macro_trees)
    require(boundary(expansion)==(0,0,False),'recipe replacement is not closed')
    require(new_intervals.get((start,stop))==expansion,'literal parenthesization differs from exact closed-macro recipe')
    require(nc[start:stop]==expected_cfg,'literal shell CFG does not implement the constructor word')
    require(len(base)==len(new),'old/new source lengths differ')
    exterior=0
    for i in itertools.chain(range(start),range(stop,len(new))):
        require(nc[i]==bc[i],('retained control/primitive changed',i,nc[i],bc[i]));exterior+=1
        require(all(not start<d<stop for d in nc[i][2]),('exterior enters shell interior',i))
    # The logical rewrite is the same implicational exchange axiom twice.
    truth_rows=[]
    for a,b,d in itertools.product((False,True),repeat=3):
        imp=lambda x,y:(not x) or y
        left=imp(a,imp(b,d));right=imp(b,imp(a,d))
        require(left==right,'implicational exchange invalid')
        truth_rows.append([a,b,d,left,right])
    return {'status':'SYMBOLIC_CONSTRUCTOR_AND_EXACT_CFG_PASS','source_sha256':hashlib.sha256(new_path.read_bytes()).hexdigest(),
            'metrics':metrics,'macro_word':word,'symbolic_original_shell':original,'symbolic_new_shell':expected,
            'replacement_interval':[start,stop],'exact_new_primitive_instructions_checked':len(expected_cfg),
            'retained_primitive_and_control_edges_checked':exterior,'all_macros_closed':True,
            'exact_closed_macro_parenthesization_matches_literal_source':True,
            'no_retained_branch_enters_replacement_interior':True,'truth_table_exchange':truth_rows,
            'scope':'Exact syntax/CFG audit plus propositional exchange. Arbitrary-input macro contracts are inherited from the pinned K215 proof. Equivalence holds for all c, including c=0,1; no binder or variable-label change. Physical TM compilation and universal runtime are separate obligations.',
            'machine_state_count_claim':None,'kernel_certificate':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('k215',type=Path);ap.add_argument('u222',type=Path)
    ap.add_argument('candidate',type=Path);ap.add_argument('recipe',type=Path);ap.add_argument('--output',type=Path)
    a=ap.parse_args();result=check(a.k215,a.u222,a.candidate,a.recipe);text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
