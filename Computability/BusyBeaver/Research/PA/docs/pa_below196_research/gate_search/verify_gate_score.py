#!/usr/bin/env python3
"""Independent audit of finite gate-search grammar witnesses.

This checks the emitted macro word, fully expanded source path bounds, and
the syntactic matching score against the separately supplied Python layout
implementation. Neither matching nor these checks prove a physical TM.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import glob
import hashlib
import importlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def need(p, msg):
    if not p:
        raise ValueError(msg)


def freeze(x):
    return tuple(map(freeze,x)) if isinstance(x,list) else x


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--inputs',type=Path,default=HERE/'inputs.json'if(HERE/'inputs.json').exists()else ROOT/'experiments/gate_search/inputs.json')
    ap.add_argument('--header',type=Path)
    ap.add_argument('--gate-variants',type=Path,default=HERE/'gate_variants.json'if(HERE/'gate_variants.json').exists()else ROOT/'agents/theory/gate_variants.json')
    ap.add_argument('--reference-package',type=Path,default=HERE/'reference'if(HERE/'reference').exists()else ROOT/'agents/incoming/extracted/pa_tm_extended_research_2026-11-13/pa_tm_extended_research_2026-11-13')
    ap.add_argument('--witness-glob',default=str(HERE/'witnesses/*.json'if(HERE/'witnesses').exists()else ROOT/'experiments/gate_search/search_b_gate*.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('gate_score_audit.json'))
    args=ap.parse_args()
    cfg=json.loads(args.inputs.read_text())
    header_path=args.header or args.inputs.with_suffix('.hpp')
    header=header_path.read_text()
    for key in ('prefix','suffix','heads','gate','symbol_attributes','symbol_states','initial_rules','base_rows','initial_root'):
        match=re.search(r'\b'+key+r'\s*=\s*([^;]+);',header)
        need(match is not None,f'C++ header omits{key}')
        value=json.loads(match[1].replace('{','[').replace('}',']'))
        need(value==cfg[key],f'C++ header/JSON mismatch:{key}')
    original=json.loads((args.reference_package/'experiments/config.json').read_text())
    gates=json.loads(args.gate_variants.read_text())
    for k in ('symbols','prefix','suffix','heads'):
        need(cfg[k]==original[k],f'Copied source configuration differs:{k}')
    symbols=list(map(freeze,cfg['symbols']));ids={s:i for i,s in enumerate(symbols)}
    expected_gates=[[[ids[freeze(s)]for s in v['words_by_equality_flip'][str(bool(f)).lower()]]for v in gates['variants']]for f in(0,1)]
    need(cfg['gate']==expected_gates,'Exported eight-gate token words differ from generator result')
    sys.path.insert(0,str(args.reference_package/'verification'))
    layout=importlib.import_module('layout');grammar=importlib.import_module('grammar')
    raw=grammar.raw_nodes()
    @lru_cache(None)
    def full_paths(t):
        if isinstance(t,str):return full_paths(raw[t])
        if t[0]=='leaf':return ((),)
        return tuple((0,)+p for p in full_paths(t[0]))+tuple((1,)+p for p in full_paths(t[1]))
    def path_attrs(paths):
        height=max(map(len,paths),default=0)
        leading=max((next((i for i,b in enumerate(p)if b),len(p))for p in paths),default=0)
        zero=max((max((len(s)for s in ''.join(map(str,p)).split('1')),default=0)for p in paths),default=0)
        return [height,leading,zero]
    attrs=[path_attrs(full_paths(s))for s in symbols]
    need(attrs==cfg['symbol_attributes'],'Exported symbol attributes differ from explicit primitive expansion')
    need([layout.MACROS.get(s,302)for s in symbols]==cfg['symbol_states'],'Exported physical macro labels differ')
    native,_=layout.machine()
    need([[q,b,w,int(d),n]for(q,b),(w,d,n)in sorted(native.items())if q<1300]==cfg['base_rows'],'Base physical rows differ')
    baseline={'label':'independent_baseline','rules':cfg['initial_rules'],'root':cfg['initial_root'],'flip':0,'gate':0,'roles':[0]*6,'order':list(range(6)),'nodes':68,'folds':6,'cost':62,'height':30,'zero_run':6}
    witnesses=[('<baseline>',baseline)]
    for p in sorted(glob.glob(args.witness_glob)):
        witnesses.append((p,json.loads(Path(p).read_text())))
    results=[]
    for path,w in witnesses:
        rs=w['rules'];n=len(rs)
        need(len({tuple(x)for x in rs})==n,'Duplicate grammar production')
        for i,(a,b)in enumerate(rs):
            for x in(a,b):need((-len(symbols)<=x<0)or(0<=x<i),'Grammar is not a topologically ordered binary DAG')
        @lru_cache(None)
        def tree(x):
            return symbols[-x-1]if x<0 else tuple(tree(y)for y in rs[x])
        @lru_cache(None)
        def tokens(x):
            return [-x-1]if x<0 else tokens(rs[x][0])+tokens(rs[x][1])
        reached=set()
        def mark(x):
            if x<0 or x in reached:return
            reached.add(x)
            for y in rs[x]:mark(y)
        mark(w['root']);need(len(reached)==n,'Grammar includes unreachable productions')
        need(sorted(w['order'])==list(range(6)),'Head order is not a permutation')
        expected=list(cfg['prefix'])
        for j in w['order']:expected+=cfg['heads'][w['flip']][j][w['roles'][j]]
        expected+=cfg['gate'][w['flip']][w['gate']]+cfg['suffix']
        actual=tokens(w['root'])
        need(actual==expected,'Expanded grammar word differs from selected meta configuration')
        need(len(actual)==201,'Selected gate word is not201tokens')
        t=tree(w['root']);height,leading,zero=path_attrs(full_paths(t))
        need(height==w['height']and zero==w['zero_run'],'C++ expanded AX path bounds differ')
        rows,index,shape=layout.build(t)
        need(len(shape)==n==w['nodes'],'C++/Python physical reader-node counts differ')
        ops=layout.opportunities_fast(rows,shape)
        matching=layout.max_matching(ops)
        # Deliberately compare to the slower helper enumeration as a second
        # implementation; its equal-row allowance may add pairs absent from
        # the fast restricted incoming-class model, so compare restricted sets.
        incoming={q:set()for q in shape}
        for(q,b),(v,right,target)in rows.items():
            if right and v==b and target in incoming:incoming[target].add(b)
        slow=layout.opportunities(rows,shape)
        slow_pairs={frozenset((a,b))for a,b,o in slow if {frozenset(incoming[a]),frozenset(incoming[b])}=={frozenset((0,)),frozenset((1,))}}
        fast_pairs={frozenset((a,b))for a,b,o in ops}
        need(slow_pairs==fast_pairs,'Fast and exhaustive helper-edge sets differ')
        nf=len(matching)
        expected_cost=n-nf if zero<=6 and height<=38 else n+2*max(0,zero-6)+max(0,height-38)
        expected_folds=nf if zero<=6 and height<=38 else 0
        need(w['cost']==expected_cost and w['folds']==expected_folds,'C++/Python syntactic reader matching score differs')
        sites,ins,cs=layout.source(t)
        if path=='<baseline>':
            oldsites,oldins=layout.program()
            need(ins==oldins,'Baseline ordinal source CFG differs from published source')
        maxpath,_,wholezero=path_attrs(tuple(p for p,_,_ in sites))
        results.append({'witness':path,'status':'PASS','macro_tokens':len(actual),'macro_word_sha256':hashlib.sha256(json.dumps(actual,separators=(',',':')).encode()).hexdigest(),'AX_primitive_height':height,'AX_max_zero_run':zero,'whole_program_max_path':maxpath,'whole_program_max_zero_run':wholezero,'source_sites':len(sites),'symbolic_cases_generated_not_run':len(cs),'reader_nodes':n,'syntactic_helper_edges':len(ops),'matching_folds':nf,'cpp_counted_folds':w['folds'],'within_layout_filter':zero<=6 and height<=38,'cost_kind':'reader_count_minus_matching'if zero<=6 and height<=38 else'penalty_outside_path_filter','effective_reader_score':expected_cost,'nominal_state_score':134+expected_cost if zero<=6 and height<=38 else None,'gate':w['gate'],'flip':w['flip'],'matching_pairs':matching})
    result={'status':'PASS','witnesses_checked':len(results),'reference_package':str(args.reference_package),'inputs_sha256':hashlib.sha256(args.inputs.read_bytes()).hexdigest(),'cpp_header_sha256':hashlib.sha256(header_path.read_bytes()).hexdigest(),'gate_variants_sha256':hashlib.sha256(args.gate_variants.read_bytes()).hexdigest(),'scope':'Exact201-token word,source path attributes and syntactic helper matching only; no simultaneous-fold soundness,arbitrary-register contracts,startup or consistency endpoint verified.','results':results}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='results'},indent=2))
    for r in results:print(json.dumps({k:v for k,v in r.items()if k not in('matching_pairs','macro_word_sha256')},sort_keys=True))


if __name__=='__main__':main()
