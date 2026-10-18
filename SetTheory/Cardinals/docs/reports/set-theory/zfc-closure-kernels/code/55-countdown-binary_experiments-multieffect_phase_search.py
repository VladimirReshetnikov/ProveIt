"""Combine universal affine excursions with source fixed-point intervals."""
import common as c
import multieffect as m
import multieffect_fold_search as fs
import sys,json
from pathlib import Path
sys.path.insert(0,str(c.ROOT/'compiler_experiments'))
import refined_phase as phase

raw=(c.HERE/'Prog254.v').read_bytes()
sites,cases,targets,first=phase.original.program_graph(raw)
domain=phase.Domain(32,1)
values,enabled,pops,edges=phase.analyze(sites,cases,targets,first,domain)
assert len(cases)==len(c.CASES)
intervals=[]
source_case_ids=[]
for i,(site,path,op,r,zero) in enumerate(cases):
    assert (path,op,r,zero)==c.CASES[i][:4]
    if not enabled[i]:continue
    logical=[]
    for mask in values[site]:
        assert mask
        lo=(mask&-mask).bit_length()-1
        hi=None if mask&(1<<domain.cap) else mask.bit_length()-1
        logical.append((lo,hi))
    if op=='CD':
        lo,hi=logical[r]
        logical[r]=(0,0) if zero else (max(lo,1),hi)
    physical=[None]*9
    for j,bound in enumerate(logical):physical[c.PHYS[j]]=bound
    assert all(hi is None or lo<=hi for lo,hi in physical)
    intervals.append(tuple(physical));source_case_ids.append(i)
c.CASES=[c.CASES[i] for i in source_case_ids]
active=None
def bounds(branch,r):
    assert active is not None
    return active[r]
m.bounds=bounds
ordinary=fs.one
def one(table,i):
    global active
    active=intervals[i]
    return ordinary(table,i)
fs.one=one
fs.RESULT_STEM='multieffect_phase_results'

if __name__=='__main__':
    fs.main()
    path=c.HERE/'multieffect_phase_results.json'
    result=json.loads(path.read_text())
    result['source_case_ids']=source_case_ids
    result['source_invariant']={'cap':domain.cap,'period':domain.period,'fixed_point_pops':pops,'transfer_edges':edges,'enabled_cases':sum(enabled),'excluded_cases':[i for i,b in enumerate(enabled) if not b],
       'intervals':intervals,'source_masks':values,'description':'Checked least fixed point of exact singleton values0..31 plus all>=32; each independent set then safely overapproximated by its interval hull.'}
    path.write_text(json.dumps(result,indent=2)+'\n')
