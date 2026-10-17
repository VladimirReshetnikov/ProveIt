"""Normalize the literal register program's pure control instructions.

CB and CC do not modify registers. Their successor chain is followed until
CI, CD or CH. Zero padding is applied exactly as in the literal decoder, and
all nonzero remaining bits must be consumed. The resulting finite termination
certificate is independent of register values.
"""
import re

def decoder_nodes(text):
    source=text.split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',source)
    assert len(nodes)==6459
    return nodes

def walk(nodes,pc):
    q=0;path=''
    while True:
        bit=pc[len(path)] if len(path)<len(pc) else '0'
        op,*arg=nodes[q][int(bit)].split();path+=bit
        if op=='CN':q=int(arg[0]);continue
        assert '1' not in pc[len(path):]
        return path,op,int(arg[0]) if arg else None

def normalizer(nodes,successor):
    def normalize(pc):
        pc='' if pc is None else pc
        chain=[];seen=set()
        while True:
            path,op,r=walk(nodes,pc)
            if op not in ('CB','CC'):
                return pc,chain,(path,op,r)
            assert path not in seen,('silent_control_cycle',pc,chain)
            seen.add(path)
            nxt=successor(path,op,r,None)
            chain.append(dict(input_pc=pc,consumed=path,operation=op,argument=r,
                              successor='' if nxt is None else nxt))
            pc='' if nxt is None else nxt
    return normalize
