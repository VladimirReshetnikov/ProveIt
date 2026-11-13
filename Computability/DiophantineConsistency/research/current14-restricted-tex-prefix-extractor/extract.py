#!/usr/bin/env python3
"""Parse only the pinned arithmetic fragment; this is not a TeX interpreter."""
import ast,re
from pathlib import Path

NAMES=['b','q','C','X','Y','E','k','ell','c','a','H','Delta','D','R','tau','V','P','Q','S','U','W','Z']
VARIABLES=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
PORTS=['beta','K','mu','omega']
MACROS={'alpha':'alpha','beta':'beta','Delta':'Delta','ell':'ell','eta':'eta','zeta':'zeta','gamma':'gamma','mu':'mu','omega':'omega','tau':'tau'}
class ParseError(ValueError):pass

def lex(text):
    result=[];i=0
    while i<len(text):
        c=text[i]
        if c.isspace():i+=1;continue
        if c=='\\':
            if text[i:i+2]=='\\\\':i+=2;continue
            m=re.match(r'\\([A-Za-z]+)',text[i:])
            if not m:raise ParseError('bad command')
            name=m.group(1);i+=len(m.group(0))
            if name=='quad':continue
            if name not in MACROS:raise ParseError('unrecognized command '+name)
            result.append(MACROS[name]);continue
        if c in '=,+-^()[]':result.append(c);i+=1;continue
        if c in '1234':result.append(c);i+=1;continue
        if 'A'<=c<='Z' or 'a'<=c<='z':result.append(c);i+=1;continue
        raise ParseError('unrecognized character '+repr(c))
    return result

class Parser:
    def __init__(self,tokens,known):self.t=tokens;self.i=0;self.known=known
    def peek(self):return self.t[self.i] if self.i<len(self.t) else None
    def take(self,x):
        if self.peek()!=x:raise ParseError('expected '+x)
        self.i+=1
    def atom(self):
        t=self.peek()
        if t in ('(','['):
            self.i+=1;v=self.expr();self.take(')' if t=='(' else ']');return v
        if t in self.known:self.i+=1;return t
        raise ParseError('unknown atom '+repr(t))
    def power(self):
        v=self.atom()
        if self.peek()=='^':
            self.i+=1;e=self.peek()
            if e not in ('2','3'):raise ParseError('unsupported exponent')
            self.i+=1;v=('sq' if e=='2' else 'cube',v)
        return v
    def product(self):
        v=self.power()
        while self.peek() in self.known or self.peek() in ('(','['):v=('*',v,self.power())
        return v
    def expr(self):
        v=self.product()
        while self.peek() in ('+','-'):
            op=self.peek();self.i+=1;v=(op,v,self.product())
        return v

def prefix(t):
    if isinstance(t,str):return [t]
    return [t[0]]+sum((prefix(x) for x in t[1:]),[])

def declarations(fragment):
    t=lex(fragment);known=set(VARIABLES+PORTS+['1','2','3','4']);out=[];i=0
    while i<len(t):
        name=t[i];i+=1
        if name not in NAMES or name in known:raise ParseError('invalid declaration '+str(name))
        if i>=len(t) or t[i]!='=':raise ParseError('missing equality')
        p=Parser(t[i+1:],known);tree=p.expr();i+=1+p.i
        out.append([name,'=']+prefix(tree));known.add(name)
        if i<len(t):
            if t[i]!=',':raise ParseError('missing separator')
            i+=1
            if i==len(t):raise ParseError('trailing separator')
    if [x[0] for x in out]!=NAMES:raise ParseError('declaration order')
    return out,known

def extract(tex):
    marker='All other symbols in the equation are polynomial abbreviations:'
    if tex.count(marker)!=1:raise ParseError('abbreviation marker')
    tail=tex.split(marker,1)[1]
    if tail.count('\\begin{gathered}')<1:raise ParseError('missing gathered')
    frag=tail.split('\\begin{gathered}',1)[1].split('\\end{gathered}',1)[0]
    frag=frag.rstrip()
    if not frag.endswith('.'):raise ParseError('missing declaration period')
    lines,known=declarations(frag[:-1])
    eqmarker='The single equation is'
    if tail.count(eqmarker)!=1:raise ParseError('equation marker')
    boxed=tail.split(eqmarker,1)[1]
    m=re.match(r'\s*\\\[\s*\\boxed\{([^{}]*)\}\s*\\\]',boxed)
    if not m:raise ParseError('boxed equation')
    expr=m.group(1)
    if not expr.endswith('=0.'):raise ParseError('equation right side')
    parser=Parser(lex(expr[:-3]),known);tree=parser.expr()
    if parser.peek() is not None:raise ParseError('trailing equation tokens')
    return lines+[['result','=']+prefix(tree)]

def lean_quote(source):
    m=re.search(r'def quoted : List \(List String\) := (\[.*?\]\])\s*\n\ndef quotedExpr',source,re.S)
    if not m:raise ParseError('historical quote')
    return ast.literal_eval(m.group(1))
