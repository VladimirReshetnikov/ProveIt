#!/usr/bin/env python3
"""Check the exact H-only Shift guard transcription and exterior CFG transport.

This checks a source transformation under the explicit entry invariant X=1.
It is not a binary-machine compiler or a blank-start proof.
"""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent

def need(condition,message):
    if not condition: raise ValueError(message)

def parse(rows):
    root={}
    for path,op,arg in rows:
        at=root
        for bit in path:
            need(bit in '01' and 'leaf' not in at,'Bad path')
            at=at.setdefault(bit,{})
        need(not at,'Duplicate leaf');at['leaf']=(op,arg)
    def walk(n):
        if 'leaf' in n:
            need(set(n)=={'leaf'},'Overlapping leaves');return n['leaf']
        need(set(n)=={'0','1'},'Incomplete source tree')
        return walk(n['0']),walk(n['1'])
    return walk(root)

def flatten(t,p=''):
    return [[p,*t]] if isinstance(t[0],str) else flatten(t[0],p+'0')+flatten(t[1],p+'1')

def internals(t):
    result=set()
    def rec(n):
        if isinstance(n[0],str) or n in result:return
        result.add(n);rec(n[0]);rec(n[1])
    rec(t);return result

def graph_path(rows):
    leaves={p:i for i,(p,_,_) in enumerate(rows)};depth=max(map(len,leaves))
    def locate(p):
        word=p+'0'*depth
        for n in range(1,len(word)+1):
            if word[:n] in leaves:
                need('1'not in p[n:],'Stray path suffix');return leaves[word[:n]]
        raise ValueError('No successor')
    def nxt(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else ''
    def cut(p,bit,n):
        at=[i for i,b in enumerate(p)if b==bit]
        return p[:at[-n]]if len(at)>=n else ''
    out=[]
    for p,op,arg in rows:
        if op=='CI':out.append(['inc',arg,locate(nxt(p))])
        elif op=='CD':out.append(['dec',arg,locate(nxt(cut(p,'0',1))),locate(nxt(p))])
        elif op=='CB':out.append(['jump',locate(nxt(cut(p,'0',arg)))])
        elif op=='CC':out.append(['jump',locate(cut(p,'1',arg))])
        else:need(op=='CH','Unknown opcode');out.append(['halt'])
    return out

def graph_intervals(rows):
    indices={p:i for i,(p,_,_)in enumerate(rows)};intervals={}
    def visit(p):
        if p in indices:r=(indices[p],indices[p]+1)
        else:
            a,b=visit(p+'0'),visit(p+'1');need(a[1]==b[0],'Noncontiguous tree');r=(a[0],b[1])
        intervals[p]=r;return r
    visit('')
    def unwind(p,b,k):
        while p:
            last,p=p[-1],p[:-1]
            if last==b:
                k-=1
                if k==0:return intervals[p][1]%len(rows)if b=='0'else intervals[p][0]
        return 0
    out=[]
    for i,(p,op,arg)in enumerate(rows):
        n=(i+1)%len(rows)
        if op=='CI':out.append(['inc',arg,n])
        elif op=='CD':out.append(['dec',arg,unwind(p,'0',1),n])
        elif op=='CB':out.append(['jump',unwind(p,'0',arg)])
        elif op=='CC':out.append(['jump',unwind(p,'1',arg)])
        else:out.append(['halt'])
    return out

def main():
    oldrows=json.loads((HERE/'honly_original_source.json').read_text())
    rows=json.loads((HERE/'honly_guard_clear_x_first.json').read_text())
    old,new=parse(oldrows),parse(rows)
    D=lambda n:('CD',n)
    guard=(((D(6),D(5)),((D(5),('CB',1)),('CH',None))),(D(5),('CC',1)))
    need(new[0][0]==guard,'Guard is not the documented tree')
    need(new[0][1]==old[0][1]and new[1]==old[1],'Source outside the guard changed')
    need(flatten(old)==oldrows and flatten(new)==rows,'Canonical source order changed')
    oldg,g=graph_path(oldrows),graph_path(rows)
    need(oldg==graph_intervals(oldrows)and g==graph_intervals(rows),'Independent graph resolvers disagree')
    expected=[['dec',6,2,1],['dec',5,5,2],['dec',5,4,3],['jump',5],['halt'],['dec',5,7,6],['jump',5]]
    need(g[:7]==expected,'Guard CFG differs from the proved seven-row program')
    def transport(n):
        need(n==0 or n>=11,'An outside edge enters the old guard interior')
        return n if n==0 else n-4
    for i,r in enumerate(oldg[11:],11):
        if r[0]=='inc':s=r[:2]+[transport(r[2])]
        elif r[0]=='dec':s=r[:2]+[transport(r[2]),transport(r[3])]
        elif r[0]=='jump':s=[r[0],transport(r[1])]
        else:s=r
        need(g[i-4]==s,f'Exterior source row changed at old site {i}')
    # Deliberately falsify one copied successor as a negative control.
    bad=[r.copy()for r in expected];bad[2][2]=5
    need(bad!=g[:7],'Negative transcription control failed')
    result={'old_sites':len(oldrows),'new_sites':len(rows),'old_internal_nodes':len(internals(old)),
        'new_internal_nodes':len(internals(new)),'outside_rows_compared':len(oldrows)-11,
        'first_source_path':rows[0][0],'maximum_path_length':max(len(p)for p, _, _ in rows),
        'six_zero_paths':sum('000000'in p for p, _, _ in rows),'maximum_zero_run':max(len(z)for p, _, _ in rows for z in p.split('1')),
        'local_cfg':expected,'entry_condition':'X = register 6 = 1; H = register 5 arbitrary natural',
        'normal_effect':'H = 0 and X = 0, every other register unchanged',
        'halt_condition':'entry H = 1','machine_compiled':False,'blank_start_proved':False,
        'proof':'Three cases H=0, H=1, H>=2; terminating decrement loop in the last case.',
        'hashes':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()for name in('honly_original_source.json','honly_guard_clear_x_first.json')}}
    need((result['old_sites'],result['new_sites'],result['old_internal_nodes'],result['new_internal_nodes'])==(3811,3807,159,163),'Source metrics changed')
    (HERE/'guard_receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
