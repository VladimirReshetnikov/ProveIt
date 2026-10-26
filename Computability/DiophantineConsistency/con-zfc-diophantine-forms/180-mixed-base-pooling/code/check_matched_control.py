#!/usr/bin/env python3
"""Check the original-source 116-variable/degree24 matched control."""
import hashlib,json,math
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def need(c,m):
    if not c:raise ValueError(m)
def main():
    raw=(ROOT/'inputs/source216.json').read_bytes();src=json.loads(raw)
    c=json.loads((ROOT/'inputs/matched_control_integer116_degree24.json').read_text())
    profile=json.loads((ROOT/'inputs/monic_profile_integer112_degree24.json').read_text())
    suffix=[{'row':97,'variable':140},{'row':99,'variable':142},{'row':101,'variable':144},{'row':149,'variable':212},{'row':151,'variable':214}]
    need(c['source_sha256']==hashlib.sha256(raw).hexdigest(),'source hash')
    need(c['steps']==profile['steps']+suffix,'matched pivot list')
    defs={};removed=set()
    for s in c['steps']:
        v=s['variable'];r=s['row'];row=src['residuals'][r]['terms'];eps=[a for a,m in row if m==[v]]
        need(len(eps)==1 and abs(eps[0])==1,'unit pivot')
        need(not any(v in m for a,m in row if m!=[v]),'nonrecursive pivot')
        need(r not in removed and v not in defs,'duplicate pivot')
        defs[v]=[(a*-eps[0],m) for a,m in row if m!=[v]];removed.add(r)
    n=len(src['variables']);inputs=[v for v in range(n) if v not in defs]
    degree={v:1 for v in inputs};visiting=set();order=[]
    def deg(v):
        if v in degree:return degree[v]
        need(v not in visiting,'dependency cycle');visiting.add(v)
        d=max((sum(deg(i) for i in m) for a,m in defs[v]),default=0)
        degree[v]=d;order.append(v);visiting.remove(v);return d
    for v in defs:deg(v)
    retained=[r for r in range(len(src['residuals'])) if r not in removed]
    rd={r:max((sum(degree[i] for i in m) for a,m in src['residuals'][r]['terms']),default=0) for r in retained}
    need(c['source_variable_degrees']==[degree[v] for v in range(n)],'degree recurrence')
    need(c['retained_source_indices']==inputs and c['retained_source_rows']==retained,'partitions')
    w=c['degree_witness'];modulus=w['modulus'];need(modulus==1000000007,'modulus')
    point={int(k):v for k,v in w['input_point'].items()}
    need(point=={v:v+3 for v in inputs},'fixed leading point');tops=dict(point)
    for v in order:
        tops[v]=sum(a*math.prod(tops[i] for i in m) for a,m in defs[v] if sum(degree[i] for i in m)==degree[v])%modulus
    r=w['row'];d=max(rd.values());need(r in rd and rd[r]==d,'degree witness row')
    residue=sum(a*math.prod(tops[i] for i in m) for a,m in src['residuals'][r]['terms'] if sum(degree[i] for i in m)==d)%modulus
    need(residue!=0 and residue==w['leading_residue'],'nonzero homogeneous witness')
    need((len(inputs),len(retained),2*d)==(c['variables'],c['residuals'],c['degree']),'metrics')
    print(json.dumps({'status':'PASS','variables':len(inputs),'residuals':len(retained),'exact_degree':2*d,'monic_definitions':len(defs),'new_mixed_pool_theorem_used':False},sort_keys=True))
if __name__=='__main__':main()
