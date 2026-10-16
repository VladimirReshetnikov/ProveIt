#!/usr/bin/env python3
"""Strict binary format for the binding-certificate Hilbert checker.

Unary natural n = 0**n + 1. Formula tags: bot00, mem01, imp10, all11.
Free/bound term tags are 0/1 followed by a unary natural. Every reference,
count and depth is unary. Proof opcodes, in order, K S C UI UD PSC MP GEN,
are three bits. Rule arities determine argument and witness counts. A witness
stores source, output, row count; each row stores source/output/depth, a two-bit
child count (0,1,2), and that many earlier-row references. The binding mode is
inferred from the rule and arguments. No text, JSON parser or fresh names form
part of this binary format. The format is a correctness control, not a claim
of optimal certificate length or minimum Turing-machine state count.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

import binder_kernel as k

RULES = ('K','S','C','UI','UD','PSC','MP','GEN')
ARGC = (2,3,2,2,3,1,2,2)
TAGS = ('bot','mem','imp','all')


def modes(rule,args):
    if rule=='UI': return [k.Mode('open',args[1])]
    if rule=='UD': return [k.Mode('close',args[2])]*2
    if rule=='GEN': return [k.Mode('close',args[1])]
    if rule=='PSC': return [k.Mode('plug',2,0,3),k.Mode('plug',1,0,4),k.Mode('plug',0,1,4)]
    return []


def unary(n): return '0'*k.nat(n)+'1'


class Reader:
    def __init__(self,bits):
        if not isinstance(bits,str) or any(c not in '01' for c in bits):
            raise k.Invalid('certificate must be an ASCII bit string')
        self.bits=bits; self.pos=0
    def tag(self,width):
        end=self.pos+width
        if end>len(self.bits): raise k.Invalid('truncated tag')
        out=int(self.bits[self.pos:end],2); self.pos=end; return out
    def nat(self):
        end=self.bits.find('1',self.pos)
        if end<0: raise k.Invalid('unterminated unary natural')
        out=end-self.pos; self.pos=end+1; return out
    def term(self): return (('f','b')[self.tag(1)],self.nat())


def decode(bits):
    r=Reader(bits); nodes=[]
    for _ in range(r.nat()):
        tag=r.tag(2)
        if tag==0: node=('bot',)
        elif tag==1: node=('mem',r.term(),r.term())
        elif tag==2: node=('imp',r.nat(),r.nat())
        else: node=('all',r.nat())
        nodes.append(node)
    # Validate acyclicity, payloads and canonical interning before proof parsing.
    k.Arena.load(nodes)
    lines=[]
    for _ in range(r.nat()):
        op=r.tag(3); rule=RULES[op]; args=[r.nat() for _ in range(ARGC[op])]
        witnesses=[]
        for mode in modes(rule,args):
            source,output,count=r.nat(),r.nat(),r.nat(); rows=[]
            for _ in range(count):
                p,q,d=r.nat(),r.nat(),r.nat(); nchildren=r.tag(2)
                if nchildren==3: raise k.Invalid('invalid witness child count')
                rows.append([p,q,d,[r.nat() for _ in range(nchildren)]])
            witnesses.append({'mode':[mode.kind,mode.a,mode.b,mode.width],
                              'source':source,'output':output,'rows':rows})
        lines.append({'rule':rule,'args':args,'witnesses':witnesses})
    if r.pos!=len(bits): raise k.Invalid('trailing data')
    return {'formulas':nodes,'lines':lines}


def encode(document):
    k.check_document(document)
    out=[unary(len(document['formulas']))]
    for node in document['formulas']:
        out.append(f'{TAGS.index(node[0]):02b}')
        for x in node[1:]:
            if node[0]=='mem': out.extend(('0' if x[0]=='f' else '1',unary(x[1])))
            else: out.append(unary(x))
    out.append(unary(len(document['lines'])))
    for line in document['lines']:
        out.append(f"{RULES.index(line['rule']):03b}")
        out.extend(unary(x) for x in line['args'])
        for cert in line['witnesses']:
            out.extend((unary(cert['source']),unary(cert['output']),unary(len(cert['rows']))))
            for p,q,d,refs in cert['rows']:
                out.extend((unary(p),unary(q),unary(d),f'{len(refs):02b}'))
                out.extend(unary(x) for x in refs)
    return ''.join(out)


def check(bits): return k.check_document(decode(bits))


def accepts_refutation(bits):
    try:
        arena,lines=check(bits)
        return bool(lines) and lines[-1]==arena.bot
    except k.Invalid:
        return False


def search():
    """Conceptual unbounded search; no test or build invokes this function."""
    n=1
    while True:
        if accepts_refutation(bin(n)[3:]): return n
        n+=1


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('path',type=Path)
    args=p.parse_args()
    try:
        bits=args.path.read_bytes().decode('ascii'); arena,lines=check(bits)
    except (UnicodeDecodeError,k.Invalid) as exc:
        print(json.dumps({'valid_derivation':False,'error':str(exc)})); return 1
    print(json.dumps({'valid_derivation':True,'lines':len(lines),'bits':len(bits),
                      'accepted_refutation':bool(lines) and lines[-1]==arena.bot}))
    return 0


if __name__=='__main__': raise SystemExit(main())
