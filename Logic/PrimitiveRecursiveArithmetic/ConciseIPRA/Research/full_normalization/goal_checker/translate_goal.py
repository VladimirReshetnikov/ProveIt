"""Untrusted conversion from the forward tree format to goal-directed trees."""
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def load(path):
    spec=importlib.util.spec_from_file_location(path.stem,path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def convert(p, g, n, m):
    tag=p[0]
    if tag in ('hyp','zero','succ','refl'):
        return None
    if tag=='qe':
        _,t,P,Q=p
        b=m.infer(P,g,n)[1]
        return ['qe',b,t,convert(P,g,n,m),convert(Q,g,n,m)]
    if tag=='de':
        _,a,P,Q=p
        b=m.infer(P,g,n)[1]
        return ['de',b,convert(P,g,n,m),convert(Q,[['q',b]]+[m.shift(x) for x in g],n+1,m)]
    if tag=='di':
        _,b,t,P=p
        a=m.sub(['q',b],t)[1]
        h=a if a[0]=='=' and t==['z'] else m.shift(m.sub(a,['z']))
        return ['di',t,convert(P,[h]+[m.shift(x) for x in g],n+1,m)]
    if tag=='tr':
        _,a,P,Q=p
        e=m.infer(P,g,n)
        return ['tr',e[1],e[2],a,convert(P,g,n,m),convert(Q,g,n,m)]
    raise ValueError('unknown proof')


def certificate(c,m):
    r=dict(c)
    r['proof']=convert(c['proof'],c['context'],c['variables'],m)
    return r
