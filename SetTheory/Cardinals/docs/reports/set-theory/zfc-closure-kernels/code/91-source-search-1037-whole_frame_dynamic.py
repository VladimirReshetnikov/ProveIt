#!/usr/bin/env python3
"""Replay the inherited prefix engine on any explicit complete source-site tree.

This is an all-values driver: every primary register is an independent natural,
the header has an independent arbitrary extra gap, and the nonempty spare suffix
has an arbitrary first value followed by an arbitrary finite list. It imports
only the inherited symbolic rules, not the original program's interval bounds.
The table uses the inherited old-label engine interface (dispatch 96, halt 254).
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, importlib.util, json, sys, time

PHYSICAL=(6,2,0,4,3,7,8,5,1)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def validate_sites(data,padding):
    assert isinstance(data,list) and data,'A nonempty complete binary source tree is required.'
    trie={};out=[];inverse={v:i for i,v in enumerate(PHYSICAL)}
    for row in data:
        assert isinstance(row,list) and len(row)==3,row
        p,op,r=row
        assert isinstance(p,str) and 1<=len(p)<=padding and set(p)<=set('01'),p
        assert op in ('CI','CD','CB','CC','CH'),op
        assert (r is None) if op=='CH' else (type(r)is int and r>=0),(p,op,r)
        if op in ('CI','CD'):assert r in inverse,(p,op,r)
        node=trie
        for bit in p:
            assert 'leaf' not in node,'A source address prefixes another.'
            node=node.setdefault(bit,{})
        assert not node,'Duplicate source address or internal-node leaf.'
        node['leaf']=True
        out.append((p,op,inverse[r]if op in ('CI','CD')else r))
    def complete(node):
        assert set(node)=={'leaf'} or set(node)=={'0','1'},'Incomplete source tree.'
        if 'leaf'not in node:complete(node['0']);complete(node['1'])
    complete(trie)
    assert any(op=='CH'for p,op,r in out),'The explicit source needs a halt leaf.'
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',type=Path,required=True,help='Recovered runtime package containing code/full_symbolic_parametric.py.')
    ap.add_argument('--table',type=Path,required=True,help='Actual emitted old-label table.')
    ap.add_argument('--sites',type=Path,required=True,help='Actual emitted source sites, with PHYSICAL register indices.')
    ap.add_argument('--padding',type=int,default=64)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--source-reference',type=Path,help='Optional explicit modified source artifact, recorded by hash.')
    args=ap.parse_args();assert __debug__ and args.padding>=1
    runtime=args.runtime.resolve();module_path=runtime/'code/full_symbolic_parametric.py'
    sys.path[:0]=[str(runtime/'code'),str(runtime/'reference/context246/code')]
    spec=importlib.util.spec_from_file_location('dynamic_whole_frame_rules',module_path)
    f=importlib.util.module_from_spec(spec);sys.modules[spec.name]=f;spec.loader.exec_module(f)
    f.PADDING=args.padding
    table,start=f.rebuild.read_table(args.table);states={q for q,b in table}
    assert len(table)==2*len(states) and set(table)=={(q,b)for q in states for b in(0,1)}
    assert 96 in states and {t for w,d,t in table.values()}-states=={254}
    f.m.TABLE=table
    sites=validate_sites(json.loads(args.sites.read_text()),args.padding)
    expected=sum(2 if op=='CD'else 1 for p,op,r in sites)
    hashes=dict(table_sha256=sha(args.table),sites_sha256=sha(args.sites),
        driver_sha256=sha(Path(__file__)),symbolic_rules_sha256=sha(module_path),
        induction_rules_sha256=sha(Path(f.m.__file__)))
    if args.source_reference:hashes['source_reference_sha256']=sha(args.source_reference)
    began=time.monotonic();cases=[];rows=set();counts=Counter();current=None
    try:
        # Derive every used oracle/list rule on THIS exact table before use.
        f.m.prove_blocks();identity=f.m.prove_word_identity()
        macros=f.m.prove_macros();marks=f.m.prove_marks()
        macro_proofs=list(f.m.BLOCK_PROOFS.values())+macros+marks
        macro_rows=sorted({(step['state'],step['read'])for proof in macro_proofs for step in proof['trace']if 'state'in step})
        for index,(p,op,r)in enumerate(sites):
            for zero in((True,False)if op=='CD'else(None,)):
                current=dict(index=index,pc=p,op=op,logical_register=r,zero=zero)
                result=f.case(p,op,r,zero,[[0,9]for _ in range(9)])
                assert result['time_lower_bound']>=1
                for step in result['trace']:
                    if 'state'in step:rows.add((step['state'],step['read']))
                counts['cases']+=1;counts['symbolic_rules']+=result['rules']
                counts[op+('/zero'if zero else'/positive')if op=='CD'else op]+=1
                cases.append(dict(**current,**{k:v for k,v in result.items()if k!='trace'}))
        assert counts['cases']==expected
        result=dict(status='PASS',complete=True,expected_cases=expected,source_leaf_count=len(sites),
            working_states=len(states),binary_rows=len(table),frame_padding=args.padding,
            all_values=True,positive_progress_checked=True,minimum_steps=min(c['time_lower_bound']for c in cases),
            scope='Arbitrary extra gap, nine independent primary naturals, arbitrary nonempty spare suffix; complete source tree and every named decrement guard.',
            exact_table_macro_support=dict(status='PASS',block_theorems=len(f.m.BLOCK_PROOFS),arithmetic_macros=len(macros),register_selectors=len(marks),rows=macro_rows,word_identity=identity),
            counts=dict(counts),rows=sorted(rows),cases=cases,seconds=time.monotonic()-began,**hashes,
            source_calibration='Separate obligation: this runtime theorem concerns the explicitly supplied source sites; it asserts no logical equivalence to a different source or to Con(ZFC).')
    except Exception as exc:
        result=dict(status='FAIL',complete=False,expected_cases=expected,source_leaf_count=len(sites),
            frame_padding=args.padding,all_values=True,counts=dict(counts),first_failed_case=current,
            error=repr(exc),seconds=time.monotonic()-began,**hashes)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('rows','cases','exact_table_macro_support')},indent=2),flush=True)
    if result['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
