#!/usr/bin/env python3
"""Measure fixed CP/GIC axiom emission with all original logical rows intact.

Offline compiler experiment. No new exact TM/ZFC equivalence is asserted.
The new source word uses CP(0,1,2), GIC(0,1,c+2), and gated old vacuity.
Unchanged upstream source files and their license are retained in vendor/.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import importlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'vendor/python'))
import recover_wade_dag as recover
recover.SNAPSHOT = HERE/'vendor/snapshot'
import theory_backend_experiment as t
import rebracket_axioms as helper
from full_grammar_experiment import safe_repair, expand, normalize
from pairing_backend_experiment import execute_helper
sys.path.insert(0, str(HERE/'vendor/snapshot/ZF/generator'))
backend = importlib.import_module('TMBuilder')
INC = 'EInc 1'


def emit(p):
    if p == 'k': return [168, INC, INC]
    if p == 2: return [177, INC]
    if not isinstance(p, tuple): return t.emit(p)
    if p[0] == 'imp' and p[2] == 1:
        inner = p[1]
        if (isinstance(inner, tuple) and inner[0] in ('imp','all') and
            isinstance(inner[2], tuple) and inner[2][0]=='imp' and inner[2][2]==1):
            return emit(inner[1])+emit(inner[2][1])+[178 if inner[0]=='imp' else 183]
        return emit(inner)+[218]
    return emit(p[1])+emit(p[2])+[{'imp':119,'rel':181,'eq':182,'all':180}[p[0]]]


def conjuncts(p):
    if (isinstance(p,tuple) and p[0]=='imp' and p[2]==1 and
        isinstance(p[1],tuple) and p[1][0]=='imp' and
        isinstance(p[1][2],tuple) and p[1][2][0]=='imp' and p[1][2][2]==1):
        return p[1][1],p[1][2][1]
    return None


def commutations(p):
    """Enumerate only ordinary conjunction commutations, recursively."""
    if not isinstance(p,tuple): return [p]
    parts=conjuncts(p)
    if parts:
        out=[]
        for a in commutations(parts[0]):
            for b in commutations(parts[1]):
                out.extend([t.And(a,b),t.And(b,a)])
        return list(dict.fromkeys(out))
    return list(dict.fromkeys((p[0],a,b) for a in commutations(p[1])
                             for b in commutations(p[2])))


def offset(p):
    if p=='k': return ('offset','c',2)
    if isinstance(p,tuple): return tuple(offset(x) for x in p)
    return p


def symbolic(word):
    stack=['old_top'];b='h';u=None;events=[]
    ct={119:t.Imp,181:t.Rel,182:t.Eq,180:t.All,178:t.And,183:t.Ex}
    for m in word:
        if m==INC:
            x=stack[-1]
            if type(x) is int:stack[-1]=x+1
            elif x=='c':stack[-1]=('offset','c',1)
            elif isinstance(x,tuple) and x[0]=='offset':stack[-1]=(x[0],x[1],x[2]+1)
            else:raise ValueError(('increment of nonscalar',x))
        elif m in (166,121,168,171,177):
            stack.append({166:'a',121:b,168:'c',171:0,177:1}[m])
        elif m in ct:
            y,x=stack.pop(),stack.pop();stack.append(ct[m](x,y))
        elif m==218:stack[-1]=t.Not(stack[-1])
        elif m==176:b='b';events.append(('read_b',len(stack)))
        elif m==158:u='u'
        elif m==208:
            assert stack[-1]==0 and u=='u';stack[-1]=u;u=None
        elif m in t.TAIL:events.append((t.MACROS[m],len(stack)))
        else:raise ValueError(('unknown macro',m))
    return stack,events


def transform(nodes,names,seq,grammar):
    """Generic source08 DAG rebracketing; also accepts direct EInc leaves."""
    out={q:es for q,es in nodes.items() if not 1<=q<=114}
    namesout={q:s for q,s in names.items() if q in out}
    interner={es:q for q,es in out.items()};nextid=max(nodes)+1;remap={}
    def edge(v):
        if isinstance(v,str):return v
        return f'ENode {remap.get(v,v)}'
    def pair(a,b):
        nonlocal nextid
        es=(a,b)
        if es not in interner:
            interner[es]=nextid;out[nextid]=es;namesout[nextid]=f'fixed_ax_{nextid}'
            nextid+=1
        return interner[es]
    for j,(a,b) in enumerate(grammar):remap[300+j]=pair(edge(a),edge(b))
    rootedge=edge(seq[-1])
    for v in reversed(seq[:-1]):rootedge=f'ENode {pair(edge(v),rootedge)}'
    assert rootedge.startswith('ENode ')
    root=int(rootedge[6:])
    for q,es in tuple(out.items()):out[q]=tuple(rootedge if e=='ENode 1' else e for e in es)
    seen=set();todo=[0]
    while todo:
        q=todo.pop()
        if q in seen:continue
        seen.add(q)
        todo.extend(int(e[6:]) for e in out[q] if e.startswith('ENode '))
    ordered=[0]+sorted(seen-{0});ids={q:j for j,q in enumerate(ordered)}
    converted={ids[q]:tuple(f'ENode {ids[int(e[6:])]}' if e.startswith('ENode ') else e
                            for e in out[q]) for q in ordered}
    return converted,{ids[q]:namesout[q] for q in ordered},ids[root]


def metric(machine,nodes):
    states={q for q,b in machine.states};framework=sum(q[0].isdigit() for q in states)
    return {'working_states':len(states),'decision_states':len(states)-framework,
            'framework_states':framework,'dag_nodes':len(nodes),
            'partial_transition_rows':len(machine.states)}


def write(path,data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def main():
    if not __debug__:raise RuntimeError('assertions required')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'results')
    parser.add_argument('--seeds',type=int,default=8)
    parser.add_argument('--exponents',type=int,nargs='+',default=[1,4])
    parser.add_argument('--refine-seeds',type=int,default=256)
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    oldword,logical,contract=t.old_contract(nodes);sp,_=t.published_spec()
    C=sp['bundle_C'](0,1,2)
    W=t.Ex(1,t.And('c',t.Rel(1,'k')))
    G=t.Ex('k',t.And(t.All(0,t.Imp(t.Rel(0,1),t.All(1,t.Imp('c',W)))),
                        t.All(1,t.Imp(t.Rel(1,'k'),t.Ex(0,'c')))))
    Vr=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    Ve=t.Imp(t.Eq('a','b'),t.All('c',t.Eq('a','b')))
    V=t.And(Vr,Ve);Cs,Gs=commutations(C),commutations(G)
    bounds=helper.bounder(nodes)
    assert all(bounds(f'ENode {m}')==(0,0) for m in t.MACROS)
    print(json.dumps({'CP_commutations':len(Cs),'GIC_commutations':len(Gs),'logical_prefix_macros':len(logical)}),flush=True)
    def source(cidx,gidx,order,group):
        c,g=Cs[cidx],Gs[gidx];pair=[c,g] if order==0 else [g,c]
        formulas=pair+[V] if group=='separate' else [t.And(*pair),V]
        word=logical+[m for p in formulas for m in emit(p)]+t.TAIL
        expected=['old_top']+sp['ax_rows']('a','h','b','c','u')+[offset(p) for p in formulas]
        actual,events=symbolic(word)
        assert actual==expected
        assert word[:len(logical)]==logical and word[-5:]==t.TAIL
        return word,formulas,events
    best=None;hist=Counter();recipes=[];tested=0;start=time.monotonic()
    def evaluate(cidx,gidx,order,group,seed,exponent):
        nonlocal best,tested
        word,formulas,events=source(cidx,gidx,order,group)
        seq,rules,diag=safe_repair(word,seed,exponent)
        assert expand(seq,rules)==word
        ns,nm,ax=transform(nodes,names,seq,rules)
        machine=helper.compile_dag(backend,ns,nm)
        met=metric(machine,ns);tested+=1;hist[met['working_states']]+=1
        recipe=dict(C=cidx,G=gidx,order=order,group=group,seed=seed,exponent=exponent)
        record=dict(recipe=recipe,**met,macro_word_length=len(word))
        recipes.append(record)
        key=(met['working_states'],met['framework_states'],len(ns),len(rules),len(seq),repr(recipe))
        if best is None or key<best['key']:
            best=dict(key=key,recipe=recipe,nodes=ns,names=nm,axroot=ax,machine=machine,
                      word=word,formulas=formulas,events=events,residual=seq,productions=rules,metrics=met)
            print(json.dumps({'new_best':record,'tested':tested,'seconds':round(time.monotonic()-start,2)}),flush=True)
    for ci in range(len(Cs)):
        for gi in range(len(Gs)):
            for order in (0,1):
                for group in ('separate','pair'):
                    for exponent in args.exponents:
                        for seed in range(args.seeds):evaluate(ci,gi,order,group,seed,exponent)
    phase1=best['recipe'].copy();phase1_count=tested
    for exponent in args.exponents:
        for seed in range(args.seeds,args.refine_seeds):
            evaluate(phase1['C'],phase1['G'],phase1['order'],phase1['group'],seed,exponent)
    word=best['word'];rn,rnames,rroot=transform(nodes,names,word,[])
    reference=helper.compile_dag(backend,rn,rnames)
    helper.reextract(best['machine'],best['nodes'],best['names'])
    helper.reextract(reference,rn,rnames)
    cert,stats=helper.bisimulation(rn,best['nodes'])
    write(out/'reference_dag.json',dict(root=0,nodes=rn,names=rnames,axioms_root=rroot))
    write(out/'candidate_dag.json',dict(root=0,nodes=best['nodes'],names=best['names'],axioms_root=best['axroot']))
    write(out/'rm_bisimulation.json',cert)
    write(out/'grammar.json',{k:best[k] for k in ('word','residual','productions')})
    best['machine'].save(str(out/'candidate.named.tm'))
    table,labels,missing=normalize(best['machine']);(out/'candidate.tm').write_bytes(table)
    write(out/'labels.json',labels);write(out/'all_measurements.json',recipes)
    evidence=dict(source_upstream_commit=recover.COMMIT,ProveIt_source_pin='4747142d5d15213eb711bdadfa3cc7e769fcb7a7',
        source_contract=contract,logical_prefix_unchanged=True,all_nine_logical_rows_retained=True,
        old_base_four_formula_codec_unchanged=True,old_vacuity_pair_and_gates_unchanged=True,
        CP_fixed_labels=[0,1,2],GIC_fixed_input_output=[0,1],GIC_fresh_binder='c+2',
        new_axiom_stack_rows=best['formulas'],symbolic_macro_audit=True,
        CP_commutations=len(Cs),GIC_commutations=len(Gs),phase1_measurements=phase1_count,
        total_measurements=tested,best_recipe=best['recipe'],best_metrics=best['metrics'],
        actual_compiler_run_for_every_measurement=True,histogram=dict(sorted(hist.items())),
        reference_metrics=metric(reference,rn),reference_to_compressed_rm_bisimulation=stats,
        candidate_sha256=hashlib.sha256(table).hexdigest(),
        partial_row_totalization=missing,totalized_transition_rows=len(table.decode().splitlines())-1,
        binary_TM_compiler_correctness_proved=False,new_calculus_completeness_proved=False,
        internal_ZFC_endpoint_proved=False,new_ZFC_state_bound_claimed=False,
        seconds=round(time.monotonic()-start,3))
    write(out/'evidence.json',evidence)
    write(out/'vendor_hashes.json',{str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted((HERE/'vendor').rglob('*')) if p.is_file() and '__pycache__' not in str(p)})
    print(json.dumps(evidence,indent=2),flush=True)


if __name__=='__main__':main()
