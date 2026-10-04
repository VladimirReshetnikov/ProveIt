#!/usr/bin/env python3
"""Fresh full-polynomial audit of a uniform-gap binary timed-orbit component."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

BASE='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/'
PINS={BASE+'code/18-timed-quartics-compact_binary_quartic.py':'9243fa208603c59285ded9d25e4493beeeadf9d90508ea7cfa615f6add7b15d4',
      BASE+'18-timed-quartics-independent-audit.md':'ce4f6cdadf548b55a00fa981f140f870ebd0fab396f164ee2a5eb4c143b50a1a'}
INPUTS=['x','t','x0','x1','x2','x3']
MODES=['four','three_literal','three_clock','two_weighted','two','two_integer_boolean']

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

class P:
    def __init__(self,x=0):
        if isinstance(x,P):self.c=dict(x.c)
        elif type(x) is int or isinstance(x,Fraction):self.c={():x} if x else {}
        else:self.c={m:v for m,v in x.items() if v}
    def __add__(self,b):
        b=P(b);d=dict(self.c)
        for m,v in b.c.items():d[m]=d.get(m,0)+v
        return P(d)
    __radd__=__add__
    def __neg__(self):return P({m:-v for m,v in self.c.items()})
    def __sub__(self,b):return self+-P(b)
    def __rsub__(self,b):return P(b)+-self
    def __mul__(self,b):
        b=P(b);d={}
        for m,v in self.c.items():
            for n,w in b.c.items():
                key=tuple(sorted(m+n));d[key]=d.get(key,0)+v*w
        return P(d)
    __rmul__=__mul__
    def __eq__(self,b):return self.c==P(b).c
    def saved(self):return [[list(m),v] for m,v in sorted(self.c.items())]
def var(x):return P({(x,):1})

def emit(mode):
    ws=['e','n','j','u'] if mode=='four' else ['e','j','u'] if mode.startswith('three') else ['j','u']
    rows=[]
    def g(name,op,a,b):rows.append([name,op,a,b]);return name
    def add(n,a,b):return g(n,'+',a,b)
    def sub(n,a,b):return g(n,'-',a,b)
    def mul(n,a,b):return g(n,'*',a,b)
    if mode.startswith('two'):
        sub('position_difference','x2','x1');sub('e','position_difference',1)
    if mode=='four':
        add('gap_cycle','x','n');add('h','gap_cycle',1)
    elif mode=='three_literal':
        sub('right_without_phase','x3','e');sub('h','right_without_phase',6)
        sub('cycle_plus_one','h','x');sub('n','cycle_plus_one',1)
    else:
        sub('L','x3',6);sub('h','L','e')
    sub('e_minus_one','e',1);mul('boolean','e','e_minus_one')
    sub('h_minus_j','h','j');sub('domain','h_minus_j','u')
    if mode in ('four','three_literal'):
        add('clock_partial','h','x');add('clock_other','clock_partial',2)
        mul('cycle_clock','n','clock_other');add('phase_length','h',1)
        mul('phase_clock','e','phase_length');sub('clock1','t','cycle_clock')
        sub('clock2','clock1','j');sub('clock','clock2','phase_clock')
    else:
        sub('clock_low1','L','x');sub('clock_low','clock_low1',1)
        add('clock_high1','L','x');add('clock_high','clock_high1',2)
        mul('cycle_clock','clock_low','clock_high');mul('phase_clock','e','L')
        sub('clock1','t','cycle_clock');sub('clock2','clock1','j');add('clock','clock2','phase_clock')
    sub('spatial_arg1','h_minus_j','j');sub('spatial_arg','spatial_arg1',1)
    mul('spatial_phase','e','spatial_arg');add('predicted1','spatial_phase','j')
    add('predicted','predicted1',3);sub('position1','x1','predicted')
    residuals=['boolean','domain','clock','x0','position1']
    if not mode.startswith('two'):
        add('second1','predicted','e');add('second','second1',1)
        sub('position2','x2','second');residuals.append('position2')
    elif mode=='two_weighted':residuals.append('position1')
    if mode=='four':
        sub('right1','x3','h');sub('right2','right1','e')
        sub('position3','right2',6);residuals.append('position3')
    squares={}
    for r in residuals:
        if r not in squares:
            squares[r]=r if mode=='two_integer_boolean' and r=='boolean' else mul('square_'+r,r,r)
    acc=squares[residuals[0]]
    for k,r in enumerate(residuals[1:],1):acc=add('sum_'+str(k),acc,squares[r])
    counts=Counter(r[1] for r in rows)
    return dict(mode=mode,inputs=INPUTS,witnesses=ws,source=rows,residuals=residuals,output=acc,
                unsquared_nonnegative_integer_rows=['boolean'] if mode=='two_integer_boolean' else [],
                ledger=dict(M=counts['*'],A=counts['+']+counts['-'],total=len(rows)),degree=4)

def run(packet,values):
    env=dict(values);parents={}
    for name,op,left,right in packet['source']:
        need(name not in env and op in ('+','-','*'),'closed SSA')
        a=env[left] if type(left) is str else left;b=env[right] if type(right) is str else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
        parents[name]=[v for v in (left,right) if type(v) is str]
    live=set();pending=[packet['output']]
    while pending:
        v=pending.pop()
        if v not in live:live.add(v);pending.extend(parents.get(v,[]))
    need(live==set(env),'all paid rows and supplied ports live')
    return env

def reference(values):
    x,t,x0,x1,x2,x3,e,n,j,u=(values[k] for k in INPUTS+['e','n','j','u'])
    d=x+7;T=n*n+(2*d-11)*n
    return [e*(e-1),d+n-6-j-u,t-T-j-e*(d+n-5),x0,
            x1-3-j-e*(d+n-7-2*j),x2-4-j-e*(d+n-6-2*j),x3-d-n-e]
def sos(rows):
    result=P()
    for r in rows:result=result+r*r
    return result

def symbolic(packets):
    full={v:var(v) for v in INPUTS+['e','n','j','u']}
    rows=reference(full);p4=run(packets[0],full)
    need([p4[r] for r in packets[0]['residuals']]==rows,'seven literal compact residuals')
    need(p4[packets[0]['output']]==sos(rows),'entire four-witness polynomial')
    three={v:var(v) for v in INPUTS+['e','j','u']}
    ext3=dict(three,n=three['x3']-three['x']-7-three['e'])
    old3=run(packets[0],ext3);lit=run(packets[1],three);norm=run(packets[2],three)
    need(old3['position3']==0,'deleted cycle graph vanishes identically')
    need(old3[packets[0]['output']]==lit[packets[1]['output']]==norm[packets[2]['output']],'whole cycle pullback and clock identity')
    two={v:var(v) for v in INPUTS+['j','u']}
    ext2=dict(two,e=two['x2']-two['x1']-1)
    old2=run(packets[2],ext2);weighted=run(packets[3],two);best=run(packets[4],two)
    need(old2['position2']==old2['position1'],'second position row becomes first row')
    need(old2[packets[2]['output']]==weighted[packets[3]['output']],'whole weighted phase pullback')
    need(weighted[packets[3]['output']]==best[packets[4]['output']]+best['position1']*best['position1'],'exact complete duplicate-square correction')
    integer_boolean=run(packets[5],two);B=best['boolean']
    need(best[packets[4]['output']]==integer_boolean[packets[5]['output']]+B*B-B,'whole integer-Boolean square correction')
    records=[]
    for p in packets:
        env=run(p,{v:var(v) for v in p['inputs']+p['witnesses']});out=env[p['output']]
        need(max(map(len,out.c))==4,'uniform exact degree4')
        leader=('n',)*4 if p['mode']=='four' else ('x3',)*4
        need(out.c.get(leader)==1,'nonzero quartic coefficient')
        records.append(dict(packet=p,polynomial=out.saved(),residual_polynomials=[env[r].saved() for r in p['residuals']],coefficient_count=len(out.c)))
    return records

def checks(packets):
    zero_count=0;states=0
    for x in [0,1,2,5,19]:
      for n in range(9):
       for e in [0,1]:
        for j in range(x+n+2):
            d=x+7;h=x+n+1;T=n*n+(2*x+3)*n
            v=dict(x=x,t=T+j+e*(h+1),x0=0,x1=3+j+e*(h-1-2*j),
                   x2=4+j+e*(h-2*j),x3=d+n+e,e=e,n=n,j=j,u=h-j)
            need(v['t']>=0 and 0<v['x1']<v['x2']<v['x3'],'sorted complete output')
            for p in packets:
                env=run(p,{k:v[k] for k in p['inputs']+p['witnesses']})
                need(env[p['output']]==0,'complete positive-time natural zero');zero_count+=1
            states+=1
    rational=0
    for k in range(24):
        vals={n:Fraction((k+2)*(j+3)%19-9,1+j%4) for j,n in enumerate(INPUTS+['e','n','j','u'])}
        for p in packets:
            got=run(p,{n:vals[n] for n in p['inputs']+p['witnesses']})
            mapped=dict(vals)
            if p['mode'].startswith('two'):mapped['e']=vals['x2']-vals['x1']-1
            if p['mode']!='four':mapped['n']=vals['x3']-vals['x']-7-mapped['e']
            rs=reference(mapped);wanted=sum(r*r for r in rs)
            if p['mode'] in ('two','two_integer_boolean'):wanted-=rs[4]*rs[4]
            if p['mode']=='two_integer_boolean':wanted+=rs[0]-rs[0]*rs[0]
            need(got[p['output']]==wanted,'full rational pullback/correction');rational+=1
    # The time-domain hypothesis is indispensable to the projected cycle sign.
    bad=dict(x=0,t=-1,x0=0,x1=2,x2=4,x3=7,e=1,j=0,u=0)
    for p in packets[1:]:
        need(run(p,{k:bad[k] for k in p['inputs']+p['witnesses']})[p['output']]==0,'negative-time boundary witness')
    need(bad['x3']-bad['x']-7-bad['e']==-1,'negative inverse cycle')
    real_external=dict(x=0,t=1,x0=0,x1=3,x2=Fraction(9,2),x3=Fraction(15,2),j=0,u=1)
    need(run(packets[5],real_external)[packets[5]['output']]==Fraction(-1,4),'integer external restriction: not real-orthant nonnegative')
    # Independent bounded negative-cycle maximum, including both phase choices.
    rejected=0
    for x in range(25):
      for n in range(-x-1,0):
       for e in [0,1]:
        for j in range(x+n+2):
            t=n*n+(2*x+3)*n+j+e*(x+n+2)
            need(t<0,'every feasible negative cycle has negative time');rejected+=1
    return dict(complete_chart_states=states,full_zero_evaluations=zero_count,rational_evaluations=rational,
                negative_cycle_phase_cases=rejected,negative_time_counterexample=bad,
                noninteger_external_negative_value='-1/4 at x=0,t=1,positions=(0,3,9/2,15/2),j=0,u=1')

def verify(root):
    for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'source pin '+name)
    packets=[emit(mode) for mode in MODES]
    need([p['ledger']['total'] for p in packets]==[39,36,35,33,32,31],'fully paid six ledgers')
    records=symbolic(packets);numeric=checks(packets)
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,forms=records,
                full_source_gates=sum(len(p['source']) for p in packets),checks=numeric,
                scope='Uniform natural gap x and time t; complete sorted four-site binary orbit component, two natural witnesses, nonnegative-real exactness on integer external inputs. No universal bound or generic compiler claim.')

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo-root',required=True,type=Path)
    group=p.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
    a=p.parse_args();out=verify(a.repo_root)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'type-exact receipt')
    else:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',ledgers=[r['packet']['ledger'] for r in out['forms']],checks=out['checks'])))
if __name__=='__main__':main()
