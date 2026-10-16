#!/usr/bin/env python3
"""Audit fixed-emission scalar helpers and the saved operation certificate."""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import tempfile

from experiment import HERE,recover,backend,emit,INC,helper,metric,write,t
from pairing_backend_experiment import execute_helper
from verify_operation_certificate import verify


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results',type=Path,default=HERE/'results')
    args=p.parse_args();out=args.results
    nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    baseline=helper.compile_dag(backend,nodes,names)
    helper.reextract(baseline,nodes,names)
    scalar_cases=0
    pair=lambda a,b:(a+b)*(a+b+1)//2+b
    for value in (2,'k'):
        builder=recover.builder_from_dag(backend,nodes,names)
        builder.sequence_lookup={s.seq:i for i,s in enumerate(builder.sequences)}
        root=builder.add_sequence(['3.topwff.inc' if v==INC else v for v in emit(value)])
        builder.reduce_to_cons()
        for c in range(8):
            for top in (0,1,3):
                for rest in (0,1,4):
                    values=[7,top,rest,c,11,13,0,0,19]
                    wanted=[7,c+2 if value=='k' else 2,pair(top,rest),c,11,13,0,0,19]
                    status=execute_helper(builder,root,values)
                    assert status==('normal',) and values==wanted,(value,c,top,rest,status,values,wanted)
                    scalar_cases+=1
    reference=out/'reference_dag.json';candidate=out/'candidate_dag.json';certificate=out/'rm_bisimulation.json'
    checked=verify(reference,candidate,certificate)
    cert=json.loads(certificate.read_text())
    inc=next(i for i,r in enumerate(cert['pairs']) if r['instruction'].startswith('EInc '))
    dec=next(i for i,r in enumerate(cert['pairs']) if r['instruction'].startswith('EDecnz '))
    mutations=[]
    for mode in ('wrong_operation','missing_pair','duplicate_pair','wrong_zero_successor','wrong_positive_successor','wrong_initial'):
        data=copy.deepcopy(cert)
        if mode=='wrong_operation':data['pairs'][inc]['instruction']='EHalt'
        elif mode=='missing_pair':data['pairs'].pop()
        elif mode=='duplicate_pair':data['pairs'].append(copy.deepcopy(data['pairs'][0]))
        elif mode=='wrong_initial':data['initial']=1
        else:data['pairs'][dec]['successors'][int(mode=='wrong_positive_successor')]=len(data['pairs'])
        with tempfile.TemporaryDirectory() as scratch:
            bad=Path(scratch)/'bad.json';write(bad,data)
            try:verify(reference,candidate,bad)
            except (AssertionError,ValueError,IndexError,KeyError):mutations.append(dict(mutation=mode,rejected=True))
            else:raise AssertionError(('bad certificate accepted',mode))
    original_word,_,_=t.old_contract(nodes)
    new_word=json.loads((out/'grammar.json').read_text())['word']
    emission_comparison=dict(original_macro_word_length=len(original_word),
        fixed_macro_word_length=len(new_word),new_scalar_increment_tokens=new_word.count(INC),
        original_conjunction_tokens=original_word.count(178),
        fixed_conjunction_tokens=new_word.count(178))
    result=dict(scalar_helper_cases=scalar_cases,scalar_helpers_checked=['push_2','push_c_plus_2'],
                emission_comparison=emission_comparison,
                all_untouched_registers_and_stack_tail_checked=True,
                baseline_public_Wade_recompile=metric(baseline,nodes),
                independent_certificate=checked,mutation_controls=mutations)
    write(out/'audit.json',result);print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':main()
