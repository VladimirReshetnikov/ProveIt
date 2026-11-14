#!/usr/bin/env python3
"""Rebuild two optional 195-state MP-tail experiments.

Uses only the standard library and the accompanying PA194QN construction
compiler/runtime. These are physical source-contract results, not new
consistency-equivalence theorems. Original source/runtime attribution is
retained by the enclosing package; the two tail patches and bounded screens
are new research.
"""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,sys,tempfile

HERE=Path(__file__).resolve().parent

def write_json(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def sha(data):return hashlib.sha256(data).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--merge-screen',action='store_true',help='Also repeat the two bounded 776-action synthesis screens.')
    args=ap.parse_args()
    assert __debug__ and not sys.flags.optimize,'Keep assertions enabled.'
    package=args.package.resolve()
    sys.path.insert(0,str(package/'construction'))
    import compiler as c
    import baseline_tools as b
    original_machine,original_nodes=c.machine,c.raw_nodes
    grammar_path=package/'construction/inputs/primary.grammar.json'
    folds_path=HERE/'primary.folds.json'
    grammar=c.read_grammar(grammar_path)
    folds=json.loads(folds_path.read_text())
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    out=args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='pa195-mp-tails-'))
    out.mkdir(parents=True,exist_ok=True)
    receipts=[]
    for kind in ('D_to_T','D_to_T_H'):
        base,labels=original_machine();nodes=original_nodes()
        if kind=='D_to_T':
            tail=(('leaf','dec',4),'node38')
            patch={(900,0):(0,True,144),(900,1):(1,True,57)}
            expected_sites,expected_outcomes=3650,4750
            effect='(b,w,0,0)'
            survivor=130
        else:
            tail=('node51','node19')
            patch={(900,0):base[114,0],(900,1):(1,True,31)}
            expected_sites,expected_outcomes=3654,4755
            effect='(b,w,0,b)'
            survivor=114
        assert nodes['node163']==('node6','node55')
        nodes['node163']=('node6',tail)
        patch[164,1]=(1,True,900)
        def machine():
            rows,ls=original_machine();rows.update(patch);return rows,ls
        c.machine=machine;c.raw_nodes=lambda:nodes
        raw,_,shape=c.build(grammar)
        child,aliases=b.apply_folds(raw,folds)
        local=b.check_local_folds(raw,child,aliases,folds)
        assert len(raw)==404 and len(shape)==67 and len(child)==390
        assert len(local['cases'])==28
        assert all(child[q,bit]==base[q,bit]for q in c.BOXSTATES for bit in(0,1))
        sites,instructions,contracts=c.source(grammar)
        assert len(sites)==expected_sites and len(contracts)==expected_outcomes
        runtime=c.validate(child,contracts);assert runtime['ok'],runtime
        startup=b.startup(child,sites[25][0]);assert startup['steps']==58154
        dense,labels=b.dense_table(child,195)
        dest=out/kind;dest.mkdir(parents=True,exist_ok=True)
        for name,table in [('raw.native.tm',raw),('machine.native.tm',child),('machine.tm',dense)]:
            (dest/name).write_text(b.table_text(table))
        for name,obj in [('labels.json',labels),('source.json',dict(sites=sites,instructions=instructions)),
                         ('local_cases.json',local)]:write_json(dest/name,obj)

        # All incoming rows must establish one previous bit by moving right.
        incoming=collections.defaultdict(list)
        for key,act in raw.items():incoming[act[2]].append((key,act))
        strict={q for q in {q for q,_ in raw} if q!=74 and incoming[q] and
                {act[1]for key,act in incoming[q]}=={True} and
                len({act[0]for key,act in incoming[q]})==1}
        ops=c.opportunities_fast(raw,strict)
        matching=c.max_matching(ops)
        helper=dict(strict_history_controls=len(strict),opportunity_pairs=len(ops),
                    maximum_matching_in_template=len(matching),
                    new_reader_pairs=[op for op in ops if 900 in op[:2]],
                    scope='Inherited three-step helper template with strict one-bit entry history; not a global lower bound.')
        assert len(ops)==len(matching)==7 and not helper['new_reader_pairs']
        write_json(dest/'helper_screen.json',helper)

        receipt=dict(status='PASS',kind=kind,working_states=195,raw_states=202,
            fixed_controls=135,AX_readers=67,retained_folds=7,local_cases=28,
            source_sites=len(sites),source_outcomes=len(contracts),success_store=effect,
            symbolic_runtime=runtime,startup=startup,
            native_sha256=sha(b.table_text(child).encode()),dense_sha256=sha(b.table_text(dense).encode()),
            source_tail=tail,new_rows=[[q,bit,*act]for(q,bit),act in patch.items()],
            input_sha256={'primary.grammar.json':sha(grammar_path.read_bytes()),
                          'primary.folds.json':sha(folds_path.read_bytes())},
            helper_screen=helper,kernel_checked=False,consistency_calibration_supplied=False,
            scope='Inherited universal symbolic source-instruction checks, retained simultaneous folds, and exact blank startup. No full Con(PA) theorem or separate independent physical audit for these experiments.')
        if args.merge_screen:
            merged=child.copy();merged.pop((900,0));merged.pop((900,1))
            merged[164,1]=(1,True,survivor)
            states=sorted({q for q,_ in merged})
            chosen=[co for co in contracts if 3634<=co[0]<=3642]
            selected={id(co)for co in chosen}
            allcs=chosen+[co for co in contracts if id(co)not in selected]
            hits=[];trials=0;witnesses=[]
            for w,d,n in itertools.product((0,1),(False,True),states):
                trials+=1;merged[survivor,1]=(w,d,n)
                failed=any(c.run(merged,co,1024)is None for co in chosen)
                if failed:continue
                for co in allcs:
                    if id(co)in selected:continue
                    if c.run(merged,co,1024)is None:
                        chosen.append(co);selected.add(id(co));witnesses.append([co[0],co[1]])
                        failed=True;break
                if not failed:hits.append([w,d,n])
            screen=dict(survivor=survivor,changed_row=[survivor,1],trials=trials,hits=hits,
                retained_counterexample_contracts=len(chosen),added_witnesses=witnesses,
                scope='New reader redirected to this fixed survivor; one conflicting row may have any write,move,working-target combination; symbolic fuel 1024.')
            assert trials==776 and not hits
            write_json(dest/'single_row_merge_screen.json',screen)
            receipt['single_row_merge_screen']=screen
        write_json(dest/'receipt.json',receipt);receipts.append(receipt)
        print(json.dumps({k:receipt[k]for k in ('kind','working_states','source_sites','source_outcomes','dense_sha256')},indent=2),flush=True)
    write_json(out/'summary.json',receipts)
    print('Replayed experimental physical constructions in',out)

if __name__=='__main__':main()
