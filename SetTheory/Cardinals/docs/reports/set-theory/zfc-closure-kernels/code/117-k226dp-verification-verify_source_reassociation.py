#!/usr/bin/env python3
"""Independent exact source-reassociation audit, using ancestor unwinding.

No discovery, compiler, or runtime-engine imports. For each tree, instructions
are numbered left to right. Sequential execution chooses the next leaf; break
exits the ancestor reached by counting left edges; continue enters the ancestor
reached by counting right edges. Fixed-word arithmetic is checked separately
against these structural successors, including absence of stray nonzero suffixes.
Python 3.10+ standard library; assertions must be enabled.
"""
from pathlib import Path
import argparse, hashlib, json, sys

def require(ok, msg):
    if not ok: raise ValueError(msg)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def encoded(obj): return (json.dumps(obj,separators=(',',':'))+'\n').encode()

def increment(word):
    bits=list(word)
    for j in range(len(bits)-1,-1,-1):
        if bits[j]=='0':
            bits[j]='1';return ''.join(bits),0
        bits[j]='0'
    return ''.join(bits),1

class Node:
    def __init__(self,parent=None,side=None,path=''):
        self.parent=parent;self.side=side;self.path=path;self.children={};self.instruction=None
        self.first=None;self.last=None

def analyze(path):
    raw=json.loads(path.read_text());require(isinstance(raw,list),'Source must be a list')
    root=Node();seen=set()
    for row in raw:
        require(isinstance(row,list) and len(row)==3,'Malformed instruction')
        word,op,arg=row
        require(isinstance(word,str) and word and not set(word)-{'0','1'} and word not in seen,'Bad or repeated path')
        require(op in ('CI','CD','CB','CC','CH'),'Invalid opcode')
        require((op=='CH' and arg is None) or (op!='CH' and type(arg) is int and arg>=0),'Invalid operand')
        require(op not in ('CI','CD') or arg<9,'Invalid register')
        require(op not in ('CB','CC') or arg>=1,'Invalid control count')
        seen.add(word);node=root
        for side in word:
            require(node.instruction is None,'A leaf is a proper path prefix')
            if side not in node.children:node.children[side]=Node(node,side,node.path+side)
            node=node.children[side]
        require(not node.children and node.instruction is None,'Repeated or overlapping leaf')
        node.instruction=(op,arg)
    leaves=[];nodes=[]
    def visit(n):
        nodes.append(n);n.first=len(leaves)
        if n.instruction is not None:
            require(not n.children,'Leaf has children');leaves.append(n)
        else:
            require(set(n.children)=={'0','1'},'Internal node is not binary and full')
            visit(n.children['0']);visit(n.children['1'])
        n.last=len(leaves)-1
    visit(root)
    ordered=[[n.path,*n.instruction] for n in leaves]
    require(raw==ordered,'Source records are not in canonical left-to-right order')
    size=len(leaves);require(size>0,'Empty program')
    def ancestor(node,side,count):
        if count==0:return node
        while node.parent is not None:
            edge=node.side;node=node.parent
            if edge==side:
                count-=1
                if count==0:return node
        return root
    def check_word(word,target):
        actual=leaves[target].path;width=max(len(word),len(actual))
        require(word.ljust(width,'0')==actual.ljust(width,'0'),
                'Structural successor disagrees with tape PC, or has a nonzero stray suffix')
    check_word('',0);graph=[];guards=0;normalizations=1;word_records=[]
    for index,n in enumerate(leaves):
        op,arg=n.instruction;cases=[]
        if op in ('CI','CD'):
            word,carry=increment(n.path);target=(index+1)%size
            check_word(word,target);cases.append(('positive' if op=='CD' else 'always',target))
            word_records.append((index,cases[-1][0],word,target,carry));normalizations+=1
        if op in ('CD','CB'):
            base=ancestor(n,'0',1 if op=='CD' else arg)
            target=(base.last+1)%size;word,carry=increment(base.path)
            check_word(word,target);cases.append(('zero' if op=='CD' else 'always',target))
            word_records.append((index,cases[-1][0],word,target,carry));normalizations+=1
        elif op=='CC':
            base=ancestor(n,'1',arg);target=base.first
            check_word(base.path,target);cases.append(('always',target))
            word_records.append((index,'always',base.path,target,0));normalizations+=1
        elif op=='CH':cases=[('halt',None)]
        guards+=len(cases);graph.append((op,arg,cases))
    return {'rows':ordered,'graph':graph,'word_records':word_records,
            'summary':{'sha256':sha(path),'leaves':size,'internal_nodes':len(nodes)-size,
                       'guarded_cases':guards,'initial_leaf_index':0,'initial_leaf_path':leaves[0].path,
                       'maximum_depth':max(len(n.path) for n in leaves),
                       'maximum_zero_run':max(len(z) for n in leaves for z in n.path.split('1')),
                       'no_stray_checks_including_initial':normalizations,
                       'initial_empty_pc_matches_leaf':True,'all_guarded_successors_normalize':True}}

def main():
    require(__debug__ and not sys.flags.optimize,'Run with assertions enabled')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old-source',type=Path,required=True);ap.add_argument('--new-source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    old,new=analyze(a.old_source),analyze(a.new_source)
    require(old['summary']['leaves']==new['summary']['leaves']==5121,'Expected 5121 source leaves')
    require(old['summary']['guarded_cases']==new['summary']['guarded_cases']==6656,'Expected 6656 guards')
    require([r[1:] for r in old['rows']]==[r[1:] for r in new['rows']],'Ordered instructions changed')
    require(old['graph']==new['graph'],'A guarded source successor changed')
    out={'status':'EXACT_ORDERED_SOURCE_BISIMULATION_AND_NO_STRAY_PASS','old':old['summary'],'new':new['summary'],
         'ordered_instruction_count':5121,'guarded_case_count':6656,'initial_leaf_correspondence':[0,0],
         'changed_leaf_paths':sum(a[0]!=b[0] for a,b in zip(old['rows'],new['rows'])),
         'shared_guard_graph_sha256':hashlib.sha256(encoded(old['graph'])).hexdigest(),
         'old_pc_normalization_sha256':hashlib.sha256(encoded(old['word_records'])).hexdigest(),
         'new_pc_normalization_sha256':hashlib.sha256(encoded(new['word_records'])).hexdigest(),
         'checker_sha256':sha(Path(__file__)),
         'proof_method':'Independent full trie and ancestor-unwinding semantics; every instruction label and guarded successor index compared; separate fixed-word/tape normalization check.',
         'scope':'All nine-register valuations. Leaf-index/register correspondence is a one-step source bisimulation, including halt and initial state. Binary runtime is a separate certificate.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
