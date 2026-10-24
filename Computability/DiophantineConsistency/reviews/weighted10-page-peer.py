#!/usr/bin/env python3
"""Independent complete printed-front, live DAG and whole-tuple page peer.

Imports neither renderer nor equation producers. The displayed formulas
are manually transcribed from the reviewed TeX, then universally matched
using only exact associative/commutative +/* and ordered subtraction.
"""
import argparse
import ast
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
PAGE=ROOT/'candidates/one-page-weighted10'
OLD=ROOT/'candidates/one-page-shifted10'
PARENT=ROOT/'candidates/ten-positive-weighted-roots'
MARKER=r'\textbf{The four fixed integers.}'
FORMULAS=[
 ('qm','beta*J'),('q','qm+1'),('C','q-F-alpha'),
 ('X','w*q'),('k','eta+zeta'),('c','k*Y+eta'),('a','X*Y+Y'),
 ('mu','q*q+1'),('A','mu*(a+2)'),('H','4*A-1'),('Delta','A*(A+2)'),('ap','A-1'),
 ('I','i*c*c'),('V0','X*(mu*Y)*(mu*Y)'),('ell','V0*k'),('Dt','ell*(ell+k)+1'),
 ('R','(qm*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),('e','k-R-1'),('Bt','(K0+w)*C-F'),
 ('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),
 ('Tp','T+alpha'),('bp','c*Tp-R'),('V','Df*bp-c'),('Dy','Q*V*V-1'),
 ('K2','X*(X+2*ap*c)-1'),('L','H*I+bp'),('W','1+qm*L'),
 ('P1','q*q*q*qm'),('M','P1*mu*mu*H'),
 ('Z','P1*mu*mu*(H*(n+V)+K2)+H*(mu*mu*(qm*Y-q*q*q*W*Bt)-P1*e)'),
 ('S','delta*Z*Z'),('At','9*delta*M*M*Dt'),('Af','delta*M*M*Df'),('Ay','M*M*Dy'),
 ('Sigma1','S+Ay'),('Sigma2','At+Af'),('P','Sigma1-Sigma2'),('U','S*Ay'),('VN','At*Af'),
 ('E','P*P-4*(U+VN)'),('N','E*E-64*U*VN')]


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


class Terms:
    def __init__(self):self.nodes=[];self.index={}
    def make(self,k):
        if k not in self.index:self.index[k]=len(self.nodes);self.nodes.append(k)
        return self.index[k]
    def integer(self,n):return self.make(('int',n))
    def symbol(self,n):return self.make(('symbol',n))
    def operation(self,tag,a,b):
        if tag=='-':return self.make(('-',a,b))
        todo=[a,b];leaves=[];constant=0 if tag=='+'else 1
        while todo:
            j=todo.pop();k=self.nodes[j]
            if k[0]==tag:todo.extend(k[1:])
            elif k[0]=='int':constant=constant+k[1]if tag=='+'else constant*k[1]
            else:leaves.append(j)
        if tag=='*'and constant==0:return self.integer(0)
        if constant!=(0 if tag=='+'else 1)or not leaves:leaves.append(self.integer(constant))
        return leaves[0]if len(leaves)==1 else self.make((tag,*sorted(leaves)))
    def expression(self,text,env):
        def go(n):
            if isinstance(n,ast.Name):return env[n.id]
            if isinstance(n,ast.Constant):
                need(type(n.value)is int,'integer expression literal');return self.integer(n.value)
            need(isinstance(n,ast.BinOp),'printed arithmetic grammar')
            return self.operation({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(n.op)],go(n.left),go(n.right))
        return go(ast.parse(text,mode='eval').body)


def universal_front(packet):
    t=Terms();leaves=packet['witnesses']+packet['fixed_numerals'];start={n:t.symbol(n)for n in leaves}
    displayed=dict(start)
    for name,e in FORMULAS:displayed[name]=t.expression(e,displayed)
    actual=dict(start);definitions={};counts=Counter()
    for name,op,a,b in packet['source']:
        need(name not in actual and op in['+','-','*'],'unique live definition')
        args=[]
        for x in[a,b]:
            need(type(x)is int or x in actual,'topological operand')
            args.append(t.integer(x)if type(x)is int else actual[x])
        actual[name]=t.operation(op,*args);definitions[name]=[x for x in[a,b]if type(x)is not int];counts[op]+=1
    need(actual[packet['output']]==displayed['N'],'full universal printed-front identity')
    live=set();todo=[packet['output']]
    while todo:
        n=todo.pop()
        if n in live:continue
        live.add(n);todo.extend(definitions.get(n,[]))
    need(live==set(actual),'all102 gates and all14 leaves live')
    need(len(definitions)==102 and counts==Counter({'*':60,'+':24,'-':18}),'exact live binary-operation count')
    return dict(operations=102,multiplications=60,additions=24,subtractions=18,
                positive_unknowns=len(packet['witnesses']),fixed_ports=len(packet['fixed_numerals']),
                full_identity='Universal over every commutative ring by exact shared AC terms, ordered subtraction and integer arithmetic.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    packet=json.loads((PAGE/'polynomial.json').read_text());parent=json.loads((PARENT/'equation.json').read_text())
    need(packet['source']==parent['source']and packet['witnesses']==parent['witnesses']and packet['output']==parent['output'],'entire102-gate parent schedule')
    need(packet['domain']=='strictly positive integers' and packet['witnesses']==['J','F','alpha','i','T','w','Y','n','eta','zeta'] and packet['exact_degree']==368,'complete positive domain, coordinates and degree')
    front=universal_front(packet)
    rejected=[]
    for label,change in [
        ('reversed final subtraction',lambda p:p['source'][-1].__setitem__(slice(2,4),p['source'][-1][2:4][::-1])),
        ('wrong strong coordinate',lambda p:next(r for r in p['source']if r[0]=='I').__setitem__(3,'i')),
        ('altered fourfold scalar',lambda p:next(r for r in p['source']if r[0]=='4scab').__setitem__(2,5)),
    ]:
        bad=deepcopy(packet);change(bad)
        try:universal_front(bad)
        except(ValueError,KeyError):rejected.append(label)
        else:raise ValueError('accepted false front '+label)
    rawports={};records={}
    for n,pin in packet['coefficient_binding']['ports'].items():
        f=pin['file'];blob=(PAGE/'coefficients'/f).read_bytes();raw=gzip.decompress(blob)
        need(blob==(OLD/'coefficients'/f).read_bytes(),'whole inherited BFS44 payload '+n)
        need(digest(raw)==pin['raw_sha256']and digest(blob)==pin['gzip_sha256'],'entire port hashes '+n)
        rawports[n]=int.from_bytes(raw,'little');need(rawports[n].bit_length()==pin['bits'],'port bitlength')
        records[n]=dict(bytes=len(raw),sha256=digest(raw))
    beta=rawports['beta'];need(beta%2==1 and beta>=31 and 0<rawports['MC']<beta<rawports['MF']<2*beta and rawports['K0']>0,'all ordinary proof port-box hypotheses')
    template=(PAGE/'equation-template.tex').read_text();original=(OLD/'equation-template.tex').read_text()
    need(template.split(MARKER,1)[1]==original.split(MARKER,1)[1],'entire constant/943tile/rank/430action/initializer body')
    seed=(PAGE/'SEED.txt').read_text().strip();need(seed==(OLD/'SEED.txt').read_text().strip()and len(seed)==436,'complete436-character seed')
    lines=[line.strip()for line in(PAGE/'equation.txt').read_text().splitlines()];chunks=[seed[i:i+62]for i in range(0,len(seed),62)]
    need(any(lines[j:j+len(chunks)]==chunks for j in range(len(lines))),'all printed seed characters')
    need((PAGE/'equation.tex').read_text()==template.replace('%%SEED%%','\n'.join(s+r'\par'for s in chunks)),'complete standalone TeX')
    info=subprocess.run(['pdfinfo',str(PAGE/'equation.pdf')],capture_output=True,text=True,check=True).stdout
    need(any(s.startswith('Pages:')and s.split()[-1]=='1'for s in info.splitlines())and'612 x 792'in info,'single Letter page')
    need('Overfull'not in(PAGE/'TEX_DIAGNOSTICS.txt').read_text(),'no overflowing text or equations')
    need('102-operation'in template and'368'in template and'formalization remain open in Lean'in template,'visible metric/scope statements')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),printed_front_and_DAG=front,
                coherent_BFS44_whole_ports=records,ordinary_port_boxes=True,
                entire_constant_recipe_verbatim=True,all436_printed_seed_characters=True,
                one_Letter_page=True,no_overfull_boxes=True,
                rejected_semantic_mutations=rejected,
                sha256={n:digest((PAGE/n).read_bytes())for n in['equation-template.tex','equation.tex','equation.pdf','polynomial.json','SEED.txt']},
                scope='Independent full displayed front/count/live DAG/coherent whole tuple and page-body transfer. Ordinary Pell/source proof and finite tuple conjugacy are inherited; no Lean or internal-ZFC derivation.')
    s=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(s)
    print(s,end='')


if __name__=='__main__':main()
