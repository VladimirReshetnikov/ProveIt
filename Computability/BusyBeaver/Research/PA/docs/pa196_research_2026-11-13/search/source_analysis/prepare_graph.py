#!/usr/bin/env python3
"""Read the byte-pinned Lean source DAG and emit a graph for finite analyses.

Usage: python prepare_graph.py BUSYBEAVER_SNAPSHOT OUTPUT_DIRECTORY
An independent interval resolver (compare_sources.graph) is used.
"""
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from compare_sources import graph, require

PINS = {
 'PA196/Program.lean':'8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872',
 'PA196/Source/Nonhalting.lean':'0fcab6b180e8445b1874335257bd8eaaaae9cf84ad97ef21e887555337f4756b',
 'PA196/Source/CommandRegisters.lean':'45a22b537f91a820875be23b953b1896de7258a46dae0daad50dab0c418eb0a1',
 'PA196/Logic/CommandSoundness.lean':'b749769a36c84fb000828748776c5d7729348ebd03d888898c807292872beb4c'}

def source_rows(text, want_trees=False):
    declarations={}
    pattern=r'\(|\)|\.(?:leaf|node|inc|dec|breakTo|continueTo|halt)|\b[A-Za-z]\w*\b|\d+'
    for name,body in re.findall(r'^def (\w+) : Tree := (\.node.+)$',text,re.M):
        tokens=re.findall(pattern,body);position=0
        def parse():
            nonlocal position
            token=tokens[position];position+=1
            if token=='(':
                value=parse();require(tokens[position]==')','unclosed term');position+=1;return value
            if token=='.node':return ('node',parse(),parse())
            if token=='.leaf':
                require(tokens[position]=='(','unparenthesized instruction');position+=1
                op=tokens[position][1:];position+=1
                arg=0 if op=='halt' else int(tokens[position]);position+=int(op!='halt')
                require(tokens[position]==')','unclosed instruction');position+=1
                return (op,arg)
            require(token in declarations,'undefined node')
            return declarations[token]
        declarations[name]=parse();require(position==len(tokens),'extra tokens')
    roots=re.findall(r'^def trie : Tree := (node\d+)\s*$',text,re.M)
    require(roots==['node172'],'unexpected root')
    if want_trees:
        return declarations[roots[0]],declarations
    ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    def leaves(node,path=''):
        if node[0]=='node':
            yield from leaves(node[1],path+'0');yield from leaves(node[2],path+'1')
        else:yield [path,ops[node[0]],node[1]]
    return list(leaves(declarations[roots[0]]))

def main():
    source,dest=map(Path,sys.argv[1:]);dest.mkdir(parents=True,exist_ok=True)
    for path,digest in PINS.items():require(sha256((source/path).read_bytes()).hexdigest()==digest,'source changed: '+path)
    rows=source_rows((source/'PA196/Program.lean').read_text());cfg=graph(rows)
    require(len(cfg)==3812 and all(None not in r for r in cfg),'unexpected source shape')
    opcodes={'halt':0,'jump':1,'inc':2,'dec':3}
    ascii_graph=str(len(cfg))+'\n'+'\n'.join(' '.join(map(str,[opcodes[r[0]],*r[1:]])) for r in cfg)+'\n'
    (dest/'source_graph.txt').write_text(ascii_graph)
    (dest/'source_graph.json').write_text(json.dumps(cfg))
    receipt={'source_sha256':PINS,'graph_sha256':sha256(ascii_graph.encode()).hexdigest(),
             'source_sites':len(cfg),'seed_site':25,'seed_registers':[2,0,0,0,0,0,0,0,0]}
    (dest/'graph_receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt))

if __name__=='__main__':main()
