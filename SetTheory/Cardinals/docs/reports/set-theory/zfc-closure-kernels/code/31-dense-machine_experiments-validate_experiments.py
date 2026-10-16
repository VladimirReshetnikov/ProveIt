#!/usr/bin/env python3
"""Independent finite checks for this report's unsuccessful optimization runs.

The RM certificate checker uses the inherited independent path engine; it does
not use the generator's path implementation. Literal compilation is repeated
for every saved C++ best-so-far grammar and all edges are re-extracted. This
verifies finite artifacts, not an unbounded TM-to-RM or consistency theorem.
"""
from __future__ import annotations
import argparse,copy,hashlib,importlib.util,json,sys
from pathlib import Path
from collections import Counter

def load(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def certificate(engine,reference,candidate,cert):
    def machine(data):
        assert data['root']==0
        return engine.Machine({int(q):tuple(es) for q,es in data['nodes'].items()})
    old,new=machine(reference),machine(candidate);records=cert['pairs']
    assert cert['initial']==0 and cert['branch_order']=='EDecnz: zero, positive'
    assert old.contract('')==(records[0]['old'],records[0]['instruction'])
    assert new.contract('')==(records[0]['new'],records[0]['instruction'])
    seen=set()
    for rec in records:
        l,r,e=rec['old'],rec['new'],rec['instruction']
        assert (l,r) not in seen;seen.add((l,r))
        assert old.lookup(l)==(l,e) and new.lookup(r)==(r,e)
        xs,ys=old.targets(l,e),new.targets(r,e);ss=rec['successors']
        assert len(ss)==len(xs)==len(ys)
        for i,x,y in zip(ss,xs,ys,strict=True):
            assert type(i) is int and 0<=i<len(records)
            nxt=records[i];assert x==(nxt['old'],nxt['instruction']) and y==(nxt['new'],nxt['instruction'])
    reached=set();todo=[0]
    while todo:
        q=todo.pop()
        if q in reached:continue
        reached.add(q);todo.extend(records[q]['successors'])
    assert len(reached)==len(records)
    return {'related_operation_pairs':len(records),'instruction_counts':dict(Counter(r['instruction'].split()[0] for r in records)),'reference_nodes':len(old.rows),'candidate_nodes':len(new.rows)}

def mutations(engine,ref,cand,cert):
    inc=next(i for i,r in enumerate(cert['pairs']) if r['instruction'].startswith('EInc '))
    dec=next(i for i,r in enumerate(cert['pairs']) if r['instruction'].startswith('EDecnz '))
    kinds=['initial','missing','duplicate','operation','zero_exit','positive_exit'];results=[]
    for kind in kinds:
        c=copy.deepcopy(cert)
        if kind=='initial':c['initial']=1
        elif kind=='missing':c['pairs'].pop()
        elif kind=='duplicate':c['pairs'].append(copy.deepcopy(c['pairs'][0]))
        elif kind=='operation':c['pairs'][inc]['instruction']='EHalt'
        else:c['pairs'][dec]['successors'][int(kind=='positive_exit')]=len(c['pairs'])
        try:certificate(engine,ref,cand,c)
        except (AssertionError,ValueError,IndexError,KeyError):results.append({'mutation':kind,'rejected':True})
        else:raise AssertionError('accepted corrupt certificate '+kind)
    return results

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--upstream',type=Path,required=True);p.add_argument('--experiments',type=Path,default=Path(__file__).resolve().parent);a=p.parse_args()
    d=a.experiments.resolve();rp=a.repo.resolve()/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    gs=load('grammar_search',d/'grammar_search.py')
    h=load('rebracket_generation',rp/'code/19-subst-engineering-vendor-one_schema_machine-rebracket_axioms.py')
    enginepath=rp/'code/19-subst-engineering-vendor-one_schema_machine-verify_rm_certificate.py'
    engine=load('independent_rm',enginepath)
    r=load('recover_wade_dag',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py')
    ns,na=r.parse_dag((a.upstream/'ZF/m254/coq/prog/Dag254.v').read_text())
    source=json.loads((rp/'data/19-subst-engineering-artifacts-full_logic_results.json').read_text());word=gs.coarsen(source['macro_word'])
    sys.path.insert(0,str(a.upstream.resolve()/'ZF/generator'));import TMBuilder as backend
    fastchecks=[]
    for line in (d/'fast-coarse-records.jsonl').read_text().splitlines():
        x=json.loads(line);assert gs.expand(x['residual'],x['grammar'])==word
        nn,nm,ax=h.transform(ns,na,x['residual'],x['grammar']);m=h.compile_dag(backend,nn,nm);h.reextract(m,nn,nm)
        actual=len({q for q,b in m.states});assert actual==x['cost']==len(nn)+55+gs.dispatch(nn)
        fastchecks.append({'trial':x['trial'],'states':actual,'exact_macro_word':True,'all_decision_edges_reextracted':True})
    runs={}
    for run in ('search16k','milp_expanded'):
        path=d/run;ref=json.loads((path/'reference.dag.json').read_text());cand=json.loads((path/'candidate.dag.json').read_text());cert=json.loads((path/'rm_certificate.json').read_text())
        runs[run]={'certificate':certificate(engine,ref,cand,cert),'mutations':mutations(engine,ref,cand,cert)}
    au=load('table_audit',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/audit_tm.py')
    er=load('edge_rewrite',d/'edge_rewrite.py')
    m=au.parse_table('#! start 0\n0 0 0 R 1\n0 1 1 R 1\n1 0 0 R 2\n1 1 1 R 2\n2 0 0 L 3\n2 1 1 L 3\n3 0 0 R 4\n3 1 1 R 4\n')
    positive=negative=0
    for pat in range(32):
        bit=(pat>>2)&1;e=m.rows[0,bit];written=(pat&~(1<<2))|(e.write<<2)
        orig={c for c in er.trace(m,1,1,written,2,64,1) if c[0]!=1}
        good=er.trace(m,3,1,written,2,64,1);assert orig.intersection(good);positive+=1
        badwrite=written^(1<<2);bad=er.trace(m,3,1,badwrite,2,64,1);assert not orig.intersection(bad);negative+=1
    result={'verified':True,'source_recipe':source['recipe'],'independent_rm_engine_sha256':hashlib.sha256(enginepath.read_bytes()).hexdigest(),'fast_search_saved_improvements':fastchecks,'rm_certificate_runs':runs,'local_join_regression':{'all_32_windows_valid_deletion':positive,'all_32_windows_wrong_write_rejected':negative},'scope':'Exact finite grammar/table/certificate checks. No unbounded binary simulation, new minimality, or ZFC endpoint theorem.'}
    (d/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
