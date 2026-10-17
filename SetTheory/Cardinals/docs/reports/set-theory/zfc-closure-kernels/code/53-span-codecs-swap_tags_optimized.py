#!/usr/bin/env python3
"""Change All/Eq tags in the existing optimized tree and audit a literal patch.

This is a compiler experiment. Source edits are certified by a finite
register-program segment comparison; changed binary rows require the full
affine instruction check. Blank initialization and ZFC calibration are separate.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
from functools import lru_cache
import hashlib,importlib.util,json,sys,types
from pathlib import Path
BASE=Path(__file__).resolve().parent
REPO=BASE.parent/'ProveIt'
sys.dont_write_bytecode=True
sys.path[:0]=[str(BASE/'reference'),str(REPO/'Computability/BusyBeaver/Research/ZFC')]
import recover_wade_dag as rec
import bisim254 as bi

OLD=json.loads((BASE/'reference/decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ENTRIES={int(k):int(max(v,key=v.get)) for k,v in OLD['state_entries'].items()}
LEAVES={tuple(k.split(':')):int(max(v,key=v.get)) for k,v in OLD['leaf_entries'].items()}

def source_change():
    source,names=rec.parse_dag((BASE/'reference/Dag254.v').read_text())
    kind={'ENode':'node','EInc':'inc','EDecnz':'decnz','EBreak':'brk','EContinue':'cont','EHalt':'halt'}
    out=[]
    for q in range(len(source)):
        row=[]
        for e in source[q]:
            op,*arg=e.split();row.append((kind[op],int(arg[0]) if arg else 0))
        out.append(tuple(row))
    assert out[180]==(('node',119),('node',159))
    assert out[182]==(('node',119),('node',157))
    out[180],out[182]=out[182],out[180]
    return out

def main():
    global REPO
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--output',type=Path,default=BASE/'swap_tags_results.json')
    ap.add_argument('--factor',choices=('direct','left'),default='direct')
    args=ap.parse_args()
    REPO=args.repo.resolve()
    sys.path.insert(0,str(REPO/'Computability/BusyBeaver/Research/ZFC'))
    import candidate252_independent_audit as au
    assert hashlib.sha256((BASE/'reference/Dag254.v').read_bytes()).hexdigest()==rec.SOURCE_SHA256['ZF/m254/coq/prog/Dag254.v']
    mapping=json.loads((BASE/'constructor_subtree_mapping.json').read_text())
    add={b-1 for a,b,_,_ in mapping['constructors']['All']['calls']}
    delete={b-1 for a,b,_,_ in mapping['constructors']['Eq']['calls']}
    assert len(add)==25 and len(delete)==8 and not add&delete
    @lru_cache(None)
    def unfold(n):
        return ('N',*(unfold(e[1]) if e[0]=='N' else e for e in NODES[n]))
    plus2=unfold(52);impl=unfold(57);rel=unfold(79)
    def factor(out,n):
        if args.factor=='direct':return out
        if out==('N',impl,('N',('I',1),plus2)):
            return ('N',unfold(58),('I',1))
        if out==('N',unfold(49),('N',unfold(58),('I',1))):
            return unfold(87)
        if n==110:
            _,left,right=out
            assert left[0]=='N' and left[2]==impl
            all3=left[1]
            _,middle,tail=right
            _,initial,continuation=middle
            _,three,parameter=initial
            assert three==('N',('I',1),plus2)
            return ('N',('N',all3,all3),('N',('N',parameter,continuation),tail))
        return out
    occurrence=defaultdict(list);direct=defaultdict(list);arithmetic=0
    def walkedge(e):
        nonlocal arithmetic
        if e[0]=='N':return walk(e[1])
        if e[0] in 'IDH':
            i=arithmetic;arithmetic+=1
            if i in add:
                assert e==('I',1)
                return ('N',e,e)
            if i in delete:
                assert e==('I',1)
                return None
        return e
    def walk(n):
        a,b=map(walkedge,NODES[n])
        out=b if a is None else a if b is None else ('N',a,b)
        assert out is not None
        out=factor(out,n)
        occurrence[n].append(out)
        if a is not None and b is not None:direct[n].append(out)
        return out
    tree=walk(OLD['root'])
    ids={};nodes={};origins=defaultdict(list)
    def intern(e):
        if e[0]!='N':return e
        if e not in ids:
            q=len(ids);ids[e]=q;nodes[q]=(intern(e[1]),intern(e[2]))
        return ('N',ids[e])
    assert intern(tree)==('N',0)
    for old,vals in direct.items():
        for e in set(vals):
            if e in ids:origins[ids[e]].append(old)
    fingerprints={unfold(n):n for n in NODES}
    assigned={};provenance={};allocation=255
    for e,n in ids.items():
        if e in fingerprints:
            old=fingerprints[e];assigned[n]=ENTRIES[old];provenance[n]=old
        else:
            possible=[old for old in origins[n] if len(set(occurrence[old]))==1]
            if possible:
                old=min(possible);assigned[n]=ENTRIES[old];provenance[n]=old
            else:
                assigned[n]=allocation;allocation+=1;provenance[n]=None
    assert assigned[0]==96
    def torows(nd):
        names={'N':'node','I':'inc','D':'decnz','B':'brk','C':'cont','H':'halt'}
        return [tuple((names[e[0]],e[1] if len(e)>1 else 0) for e in nd[q]) for q in range(len(nd))]
    result=dict(experiment=__doc__,factor=args.factor,arithmetic_sites_before=arithmetic,
       arithmetic_increments_added=len(add),arithmetic_increments_removed=len(delete),
       decision_nodes_before=len(NODES),decision_nodes_after=len(nodes),
       new_state_allocations=list(range(255,allocation)))
    try:
        cert=bi.build(bi.Prog(torows(nodes)),bi.Prog(source_change()))
        result['source_segment_certificate_pairs']=len(cert)
    except SystemExit as ex:
        result['source_segment_certificate_failure']=str(ex)
        args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return
    raw=(REPO/'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==au.EXPECTED_SHA
    table=au.read_table(raw)
    changed=table.copy();requests=defaultdict(list)
    def leaf(e,b):
        if e[0]=='N':return b,'R',assigned[e[1]]
        if e[0] in 'IDH':return b,'R',LEAVES[tuple(map(str,e))]
        choices=Counter()
        for q,pair in NODES.items():
            if pair[b]==e:choices[table[ENTRIES[q],b]]+=1
        assert choices,(e,b)
        return choices.most_common(1)[0][0]
    for n,pair in nodes.items():
        old=provenance[n];q=assigned[n]
        for b,e in enumerate(pair):
            original_e=None if old is None else NODES[old][b]
            unchanged=(original_e==e if e[0]!='N' else original_e[0]=='N' and assigned[e[1]]==ENTRIES[original_e[1]]) if original_e is not None else False
            row=table[q,b] if unchanged and (q,b) in table else leaf(e,b)
            requests[q,b].append((row,n,old))
    conflicts={str(k):v for k,v in requests.items() if len({x[0] for x in v})>1}
    result['row_assignment_conflicts']=conflicts
    if conflicts:
        args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return
    for k,vals in requests.items():changed[k]=vals[0][0]
    result['changed_rows']=[dict(state=q,read=b,before=table.get((q,b)),after=v) for (q,b),v in changed.items() if table.get((q,b))!=v]
    result['protected_boxes_unchanged']=all(changed[k]==table[k] for k in au.BOX_PAIRS)
    assert result['protected_boxes_unchanged']
    sys.modules['cost_search']=types.SimpleNamespace()
    path=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    spec=importlib.util.spec_from_file_location('swap_tags_affine',path);st=importlib.util.module_from_spec(spec);spec.loader.exec_module(st)
    strings={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in changed.items()}
    sites=[]
    def visit(n,p):
        for b,e in enumerate(nodes[n]):
            if e[0]=='N':visit(e[1],p+str(b))
            else:sites.append((p+str(b),'C'+e[0],e[1] if len(e)>1 else None))
    visit(0,'')
    failures=[];cases=0;case_records=[]
    for p,op,r in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=au.NEWPHYS[r] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            nxt=au.successor(p,op,r,zero)
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=[('b',int(b)) for b in nxt] if nxt is not None else []
            right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
            case_records.append(dict(index=cases,path=p,op=op,logical_register=r,physical_register=physical,
                zero=zero,branch=branch,successor=nxt,effect=effect,target=st.canon([('b',1)],right),halt=op=='CH'))
            try:st.run(strings,p,branch,st.canon([('b',1)],right),halt=op=='CH',fuel=1000)
            except (AssertionError,KeyError) as ex:
                failures.append(dict(index=cases,path=p,op=op,register=r,zero=zero,error=str(ex)))
            cases+=1
    result['affine_cases']=cases;result['affine_failures']=failures
    result['working_states_before_pruning']=len(changed)//2
    if not failures:
        (BASE/'swap_tags_segment_certificate.json').write_text(json.dumps(cert,separators=(',',':'))+'\n')
        (BASE/'swap_tags_source_dag.json').write_text(json.dumps(source_change(),separators=(',',':'))+'\n')
        (BASE/'swap_tags_optimized_nodes.json').write_text(json.dumps(dict(root=0,nodes=nodes,entries=assigned),indent=2)+'\n')
        graph=au.graph_audit(changed)
        result['graph_before_pruning']=graph
        unreachable=set(graph['unreachable_states'])
        changed={k:v for k,v in changed.items() if k[0] not in unreachable}
        states={q for q,_ in changed}
        assert all(t in states|{254} for w,d,t in changed.values())
        assert len(changed)==2*len(states)
        result['graph_after_pruning']=au.graph_audit(changed)
        oldlabel='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(changed.items()))
        (BASE/'swap_tags_runtime_old.tm').write_text(oldlabel)
        ids2={q:i for i,q in enumerate([64]+sorted(states-{64}))};ids2[254]=len(states)
        canonical='#! start 0\n'+''.join(f'{ids2[q]} {b} {w} {d} {ids2[t]}\n' for q in sorted(states,key=ids2.get) for b in (0,1) for w,d,t in [changed[q,b]])
        (BASE/'swap_tags_runtime.tm').write_text(canonical)
        (BASE/'swap_tags_guard_cases.json').write_text(json.dumps(case_records,separators=(',',':'))+'\n')
        result['canonical_table_sha256']=hashlib.sha256(canonical.encode()).hexdigest()
        result['oldlabel_table_sha256']=hashlib.sha256(oldlabel.encode()).hexdigest()
        result['start_oldlabel']=64;result['halt_oldlabel']=254
        result['blank_bootstrap_checked']=False
        result['canonical_renumbering']=ids2
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({**result,'affine_failures':failures[:5]},indent=2))
if __name__=='__main__':main()
