"""Measure PSC with the ENTIRE original logical engine, outside scratch only.

The original281 compilation is matched first. No new calculus completeness,
binary simulation, internal ZFC theorem or sub254 machine is claimed.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys
from recover_wade_dag import ROOT,COMMIT,REGISTERS,builder_from_dag,git_bytes,parse_dag
from pairing_backend_experiment import execute_helper
import theory_backend_experiment as t
import psc_backend_experiment as p
import logic_engine_controls as logic


def offset_checks(builder):
    root=builder.add_sequence([168,[p.INC,p.INC]])
    pair=lambda x,y:(x+y)*(x+y+1)//2+y
    count=0
    for c in range(12):
        for top in (0,1,17):
            for rest in (0,5):
                values=[7,top,rest,c,11,13,0,0,19]
                expected=values.copy();expected[1]=c+2;expected[2]=pair(top,rest)
                assert execute_helper(builder,root,values)==('normal',) and values==expected
                count+=1
    return count


def build(backend,nodes,names,logical,ir,seed):
    vr=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    ve=t.Imp(t.Eq('a','b'),t.All('c',t.Eq('a','b')))
    word=logical+p.emit(p.psc_template())
    if ir:word+=p.emit(t.All(1,t.Not(t.Rel(1,1))))
    word+=t.emit(t.And(vr,ve))+t.TAIL
    b=builder_from_dag(backend,nodes,names)
    b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
    offset=offset_checks(b)
    if seed is None:
        t.lower_program(b,nodes,word,'full_logic_PSC',shared=True)
    else:
        residual,grammar=p.repair(word,seed);refs={}
        resolve=lambda x:refs[x] if isinstance(x,tuple) else x
        for i,pair in enumerate(grammar):refs['g',i]=b.add_sequence([resolve(x) for x in pair])
        root=b.add_sequence([resolve(x) for x in residual])
        b.sequences[root].name=f'full_logic_PSC_{seed}().0'
        assert p.macro_expansion(b,root)==word
        for i,s in enumerate(b.sequences):
            if i!=1:s.seq=tuple(root if x==1 else x for x in s.seq)
        b.breakout_common_subsequences();b.reduce_to_cons();b.name_sequences()
        assert p.macro_expansion(b,root)==word
    return b,offset


def main():
    if not __debug__:raise RuntimeError('run without -O: audit requires assertions')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scratch',type=Path,required=True)
    parser.add_argument('--output-evidence',type=Path)
    args=parser.parse_args();scratch=args.scratch.resolve()
    if scratch==Path('/') or scratch==ROOT or ROOT in scratch.parents:parser.error('scratch must be outside repository')
    scratch.mkdir(parents=True,exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (scratch/name).write_bytes(git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(scratch));backend=importlib.import_module('TMBuilder')
    nodes,names=parse_dag(git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    _,logical,contract=t.old_contract(nodes)
    baseline=p.record(builder_from_dag(backend,nodes,names),scratch/'original281.tm')
    assert baseline['working_states']==281
    results={}
    for ir in (False,True):
        for seed in (None,2):
            b,offset=build(backend,nodes,names,logical,ir,seed)
            results[f'PSC_explicitIR{ir}_seed{seed}']=p.record(b,scratch/f'PSC_IR{ir}_seed{seed}.tm')
    evidence=dict(upstream_commit=COMMIT,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        original_AX_symbolic_contract=contract,baseline=baseline,variants=results,
        equality_aware_alpha_cases=logic.eq_alpha_checks(),fresh_offset_register_cases=offset,
        entire_original_logical_engine_retained=True,original_four_tags_and_F_alias_retained=True,
        new_proof_translation_or_binary_simulation_proved=False,new_ZFC_machine_or_state_bound_claimed=False)
    text=json.dumps(evidence,indent=2,sort_keys=True)+'\n'
    if args.output_evidence:args.output_evidence.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
