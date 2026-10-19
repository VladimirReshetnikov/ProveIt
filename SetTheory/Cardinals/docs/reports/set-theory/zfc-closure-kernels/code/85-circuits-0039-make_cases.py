#!/usr/bin/env python3
"""Regenerate finite instruction fixtures for the arbitrary-row fusion search.

All target tapes are supplied by the attributed literal register-contract
implementation, not by executing a mutated machine. Optional guard restriction
requires the independently checked source-product invariant and CFG transport.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
REFERENCE=ROOT/'reference/context246'
LAYOUTS=('baseline','0','233','235','236','237')
EXCLUDED=(8202,8203,8204,8358,8359,8360)

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module
    spec.loader.exec_module(module)
    return module

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def generate(layout,scope,output, *, check_guards=True):
    if not __debug__: raise RuntimeError('Run with assertions enabled.')
    assert layout in LAYOUTS and scope in ('all','admissible','product')
    if scope=='product':
        runtime=ROOT/'code/runtime'
        sys.path.insert(0,str(runtime))
        guards=load('fusion_guard_transport',runtime/'admissible_guards.py')
        guard_result=guards.verify_transport((layout,))
        maker=load('fusion_product_fixtures',runtime/'make_merge_cases.py')
        content,result=maker.generate(layout,'product')
        result.update(scope=scope,guard_certificate_checked=True,guard_transport=guard_result)
        if output is None:return content,result
        output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(content)
        return result
    literal_path=REFERENCE/'code/check_literal_instructions.py'
    literal=load('fusion_literal_contracts',literal_path)
    if layout=='baseline':
        table_path=REFERENCE/'machine/zfc_prefix246_old.tm'
        source_path=REFERENCE/'sources/Prog254.v'
        sites=literal.program_sites(source_path)
        table=literal.read_table(table_path)
    else:
        folder=ROOT/f'candidates/layout{layout}'
        table_path=folder/'machine_old.tm';source_path=folder/'program.json'
        descriptor=json.loads(source_path.read_text())
        sites=descriptor['sites']
        used=set(map(int,descriptor['used']))
        table={key:row for key,row in literal.read_table(table_path).items() if key[0] in used}
        assert len(used)==246 and used=={q for q,b in table}
    states={q for q,b in table}
    assert len(states)==246 and len(table)==492
    assert set(table)=={(q,b) for q in states for b in (0,1)}
    assert {row[2] for row in table.values()} <= states|{254}
    assert 254 not in states and 96 in states and len(sites)==6460
    guard_result=None
    if scope=='admissible' and check_guards:
        runtime=ROOT/'code/runtime'
        sys.path.insert(0,str(runtime))
        guards=load('fusion_guard_transport',runtime/'admissible_guards.py')
        guard_result=guards.verify_transport([] if layout=='baseline' else [int(layout)])
    lines=[str(len(table))]
    for (q,b),(w,d,target) in sorted(table.items()):
        assert w in (0,1) and d in (-1,1)
        lines.append(f'{q} {b} {w} {d} {target}')
    fixtures=[];case_index=0
    for pc,op,register in sites:
        for positive in ((False,True) if op=='CD' else (None,)):
            registers=[(i*3+1)%5 for i in range(9)]
            if op=='CD':registers[literal.PHYSICAL[register]]=2 if positive else 0
            spares=[0,2]
            initial=sorted(literal.paint(pc,40,registers,spares,0))
            expected=literal.expected(pc,op,register,registers,spares,0,40)
            head=0 if expected is None else expected[0]
            target=[] if expected is None else sorted(expected[1])
            assert all(-64<=x<=447 for x in initial+target)
            row=' '.join(map(str,[int(op=='CH'),head,len(initial),*initial,len(target),*target]))
            if scope=='all' or case_index not in EXCLUDED:fixtures.append(row)
            case_index+=1
    assert case_index==8391 and len(fixtures)==(8391 if scope=='all' else 8385)
    lines.append(str(len(fixtures)));lines.extend(fixtures)
    content='\n'.join(lines)+'\n'
    if output is not None:
        output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(content)
    result=dict(layout=layout,scope=scope,working_states=246,transition_rows=492,
        original_guarded_cases=8391,fixture_cases=len(fixtures),
        excluded_case_indices=list(EXCLUDED) if scope=='admissible' else [],
        guard_certificate_checked=bool(scope=='admissible' and check_guards),
        table_sha256=sha(table_path),program_sha256=sha(source_path),
        literal_contract_module_sha256=sha(literal_path),fixture_sha256=hashlib.sha256(content.encode()).hexdigest(),
        head=0,header_distance=40,primary_values=[(i*3+1)%5 for i in range(9)],
        tested_decrement_values=[0,2],spare_values=[0,2],
        scope_note='Finite fixtures. Complete tapes and exact nonhalting endpoints; halting fixtures require an actual halt. This is not an unbounded macro proof.')
    if guard_result is not None:result['guard_transport']=guard_result
    return result if output is not None else (content,result)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--layout',choices=LAYOUTS,default='baseline')
    parser.add_argument('--scope',choices=('all','admissible','product'),default='product')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=generate(args.layout,args.scope,args.output)
    args.output.with_suffix('.metadata.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
