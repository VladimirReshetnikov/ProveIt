#!/usr/bin/env python3
"""Minimum-DAG grammar synthesis in a stated finite substring family.

A node denotes an exact word of closed RM macros. Each active non-atomic word
chooses one binary concatenation whose non-atomic children must also be active.
The parent-length decrease proves acyclicity. Minimize the number of active
non-atomic words. The bounded family consists of repeats and their suffixes,
plus the full source word and its suffixes. This is no global minimality claim.
"""
from __future__ import annotations
import argparse, importlib.util, json, sys, time
from pathlib import Path
from collections import Counter
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def solve(word,limit,free=()):
    w=tuple(word);counts=Counter(w[i:j] for i in range(len(w)) for j in range(i+2,len(w)+1))
    cand={s for s,n in counts.items() if n>=2}|{w}|{(x,) for x in w}
    for s in list(cand):cand.update(s[i:] for i in range(len(s)))
    words=sorted((s for s in cand if len(s)>1),key=lambda s:(len(s),s));ids={s:i for i,s in enumerate(words)}
    splits=[(s,k) for s in words for k in range(1,len(s)) if s[:k] in cand and s[k:] in cand]
    n=len(words)+len(splits);c=np.zeros(n);c[:len(words)]=[0 if s in free else 1 for s in words]
    ri=[];ci=[];va=[];lo=[];hi=[]
    def add(d,l,h):
        row=len(lo);lo.append(l);hi.append(h)
        for col,v in d.items():ri.append(row);ci.append(col);va.append(v)
    byl={s:[] for s in words}
    for j,(s,k) in enumerate(splits):byl[s].append(len(words)+j)
    for s in words:
        d={ids[s]:-1};d.update({q:1 for q in byl[s]});add(d,0,0)
    for j,(s,k) in enumerate(splits):
        p=len(words)+j
        for child in (s[:k],s[k:]):
            if len(child)>1:add({p:1,ids[child]:-1},-np.inf,0)
    add({ids[w]:1},1,1)
    mat=coo_matrix((va,(ri,ci)),shape=(len(lo),n)).tocsc()
    t=time.monotonic();res=milp(c=c,integrality=np.ones(n),bounds=Bounds(0,1),constraints=LinearConstraint(mat,lo,hi),options={'time_limit':limit,'mip_rel_gap':0.0})
    if res.x is None:raise RuntimeError(str(res))
    chosen={s:k for j,(s,k) in enumerate(splits) if res.x[len(words)+j]>.5}
    needed=set()
    def visit(s):
        if len(s)==1 or s in needed:return
        needed.add(s);k=chosen[s];visit(s[:k]);visit(s[k:])
    visit(w)
    ruleids={};grammar=[]
    for s in words:
        if s not in needed:continue
        k=chosen[s];a,b=s[:k],s[k:]
        grammar.append((a[0] if len(a)==1 else ruleids[a],b[0] if len(b)==1 else ruleids[b]))
        ruleids[s]=300+len(grammar)-1
    meta={'substring_variables':len(words),'binary_split_variables':len(splits),'objective_value':res.fun,'solver_status':res.status,'solver_message':res.message,'mip_gap':res.mip_gap,'mip_node_count':res.mip_node_count,'mip_dual_bound':res.mip_dual_bound,'needed_nonterminals':len(needed),'elapsed':time.monotonic()-t}
    return [ruleids[w]],grammar,meta

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--upstream',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--time-limit',type=float,default=120);p.add_argument('--lane',choices=['coarse','expanded'],default='expanded');p.add_argument('--free-161',action='store_true');a=p.parse_args()
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);rp=a.repo.resolve()/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    gs=load('grammar_search',Path(__file__).with_name('grammar_search.py'))
    h=load('inherited_rebracket',rp/'code/19-subst-engineering-vendor-one_schema_machine-rebracket_axioms.py')
    r=load('recover_wade_dag',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py')
    nodes,names=r.parse_dag((a.upstream/'ZF/m254/coq/prog/Dag254.v').read_text())
    source=json.loads((rp/'data/19-subst-engineering-artifacts-full_logic_results.json').read_text());word=source['macro_word']
    if a.lane=='coarse':word=gs.coarsen(word)
    residual,grammar,meta=solve(word,a.time_limit,free={(166,119)} if a.free_161 else ())
    assert gs.expand(residual,grammar)==word
    nn,nm,ax=h.transform(nodes,names,residual,grammar);meta.update(decision_nodes=len(nn),dispatcher_depth=gs.dispatch(nn),estimated_states=len(nn)+55+gs.dispatch(nn))
    def write(fn,x):(out/fn).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
    write('grammar.json',dict(word=word,residual=residual,grammar=grammar,lane=a.lane,free_161=a.free_161));write('results.json',meta)
    sys.path.insert(0,str(a.upstream.resolve()/'ZF/generator'));import TMBuilder as backend
    m=h.compile_dag(backend,nn,nm);h.reextract(m,nn,nm);m.save(str(out/'candidate.named.tm'))
    norm=load('normalize_named_input',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/audit_raw_candidate.py')
    table,labels,tmeta=norm.normalize_named((out/'candidate.named.tm').read_bytes());(out/'candidate.tm').write_bytes(table)
    assert tmeta['working_states']==meta['estimated_states']
    write('candidate.dag.json',dict(nodes=nn,names=nm,root=0,axioms_root=ax));write('candidate.labels.json',labels)
    ref=json.loads((rp/'data/19-subst-engineering-artifacts-full_logic_reference.dag.json').read_text());rn={int(q):tuple(es) for q,es in ref['nodes'].items()}
    cert,stats=h.bisimulation(rn,nn);write('rm_certificate.json',cert);write('reference.dag.json',ref)
    meta.update(table=tmeta,certificate_stats=stats,binary_simulation_or_ZFC_endpoint_proved=False,source_layout='source19 selected268 complete original logic');write('results.json',meta);print(json.dumps(meta),flush=True)
if __name__=='__main__':main()
