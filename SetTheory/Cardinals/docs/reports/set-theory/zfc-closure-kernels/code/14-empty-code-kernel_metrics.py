"""Explicit formula-tree metric for the displayed (uncurried) PSC/EPSC schema.

Variable indices/payloads and universal closure of extra parameters are not
counted. Each matrix occurrence is one atom. This is not a state-count metric.
"""
import json
from pathlib import Path

def mem(i,j):return ('mem',i,j)
def imp(a,b):return ('imp',a,b)
def all_(i,a):return ('all',i,a)
def not_(a):return ('not',a)
def and_(a,b):return not_(imp(a,not_(b)))
def or_(a,b):return imp(not_(a),b)
def ex(i,a):return not_(all_(i,not_(a)))

def wrapper(empty):
    phi=('matrix',)
    x,y,a,c,b,z=range(6)
    bound=all_(x,ex(b,all_(y,imp(phi,all_(z,imp(mem(z,y),mem(z,b)))))))
    seed=all_(z,not_(mem(z,x))) if empty else all_(z,imp(mem(z,x),mem(z,a)))
    closed=all_(x,all_(y,imp(and_(or_(seed,mem(x,c)),phi),mem(y,c))))
    support=all_(y,imp(mem(y,c),ex(x,phi)))
    body=ex(c,and_(closed,support))
    return imp(bound,body if empty else all_(a,body))

def transform(f,mode):
    op=f[0]
    if op in ('mem','matrix','bot'):return f
    if op=='imp':return imp(transform(f[1],mode),transform(f[2],mode))
    if op=='all':return all_(f[1],transform(f[2],mode))
    a=transform(f[1],mode)
    if mode=='bottom':return imp(a,('bot',))
    if mode=='cancel' and a[0]=='not':return a[1]
    return not_(a)

def count(f):
    if f[0] in ('mem','matrix','bot'):return 1
    if f[0]=='not':return 1+count(f[1])
    if f[0]=='all':return 1+count(f[2])
    return 1+count(f[1])+count(f[2])

def main():
    out={name:{mode:count(transform(wrapper(empty),mode)) for mode in ('unary','cancel','bottom')}
         for name,empty in (('PSC',False),('EPSC',True))}
    assert out=={'PSC':{'unary':41,'cancel':39,'bottom':52},'EPSC':{'unary':39,'cancel':37,'bottom':51}}
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
