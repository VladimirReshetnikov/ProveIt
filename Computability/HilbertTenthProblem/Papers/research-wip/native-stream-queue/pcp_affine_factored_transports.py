"""Exact paid linear-form optimization of complete affine-pair transports.

Repeated coefficients and a common offset sum can share real source gates.
The full comparison vector and final polynomial are unchanged, including
on signed assignments.  All native typing remains in the parent packet.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import affine_history_linear_forms as linear
import pcp_uniform_affine_pair_history as parent

execute=parent.execute
scalar=parent.scalar


def seed(source):
    g=parent.DAG();g.source=list(source)
    for name,op,a,b in source:
        if op in ('+','*') and repr(a)>repr(b):a,b=b,a
        # Prefer the first paid representative of an identical instruction.
        g.cache.setdefault((op,a,b),name)
    return g


def eliminate_dead(source, roots, inputs):
    rows={n:(n,op,a,b) for n,op,a,b in source};live=set();pending=list(roots)
    while pending:
        v=pending.pop()
        if not isinstance(v,str) or v in inputs or v in live:continue
        assert v in rows,v
        live.add(v);pending.extend(rows[v][2:])
    answer=[row for row in source if row[0] in live]
    known=set(inputs)
    # New forms can reuse previously computed terms, so order by actual
    # dependencies after replacing the transport-output references.
    pending=answer;answer=[]
    while pending:
        following=[]
        for row in pending:
            name,_,a,b=row
            if all(not isinstance(v,str) or v in known for v in (a,b)):
                assert name not in known
                answer.append(row);known.add(name)
            else:following.append(row)
        assert len(following)<len(pending),'cyclic rewritten form'
        pending=following
    return answer


def forms_for(old):
    if 'linear_forms' in old:return old['linear_forms']
    forms=[]
    for tag,ai,ci in (('U',0,1),('V',2,3)):
        coefficients={}
        for i,row in enumerate(old['maps']):
            coefficients[f'Z{tag}hat{i}']=row[ai]
            coefficients[f'Shat{i}']=row[ci]
        forms.append(dict(coefficients=coefficients,
            constant=-sum(row[ai]+row[ci] for row in old['maps']),
            output=old['interfaces']['next'+tag]))
    return forms


def rewrite(old,mode='auto'):
    if mode=='auto':
        options=[rewrite(old,m) for m in linear.MODES]
        best=min(options,key=lambda p:(p['operations'],p['multiplications'],p['linear_mode']))
        # The literal parent remains an explicit fallback.
        if best['operations']>old['operations']:
            best=dict(old,linear_mode='parent',parent_operations=old['operations'],
                      linear_forms=forms_for(old))
        return dict(best,linear_candidate_ledgers=[ledger(p) for p in options])
    forms=forms_for(old);g=seed(old['source']);outputs=linear.emit(g,forms,mode)
    aliases={form['output']:value for form,value in zip(forms,outputs) if form['output']!=value}
    assert not any(key in old['parameters']+old['auxiliaries'] for key in aliases)
    def alias(v):return aliases.get(v,v)
    # Only original consumers are redirected.  The appended DAG may reuse
    # a proper old subexpression; its own already-paid operands stay literal.
    source=[(n,op,alias(a),alias(b)) for n,op,a,b in old['source']]
    source+=g.source[len(old['source']):]
    pairs=[(alias(a),alias(b)) for a,b in old['comparisons']]
    interfaces={n:alias(v) for n,v in old['interfaces'].items()}
    native_prefix=old.get('native_prefix','and__')
    native_names=[n for n,_,_,_ in old['source'] if n.startswith(native_prefix)]
    roots=[v for pair in pairs for v in pair]+list(interfaces.values())+native_names
    source=eliminate_dead(source,roots,set(old['parameters']+old['auxiliaries']))
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert [row for row in source if row[0].startswith(native_prefix)]==[
        row for row in old['source'] if row[0].startswith(native_prefix)]
    return dict(old,source=source,comparisons=pairs,interfaces=interfaces,
        linear_forms=[dict(form,output=value) for form,value in zip(forms,outputs)],
        linear_mode=mode,parent_operations=old['operations'],operations=len(source),
        multiplications=counts['M'],additions_subtractions=counts['A'],
        wrapper_operations=len(source)-len(native_names))


def build(maps=parent.DEFAULT_MAPS,layout='auto',mode='auto'):
    if layout=='auto':
        choices=[rewrite(parent.build(maps,l),mode) for l in ('contiguous','interleaved')]
        best=min(choices,key=lambda p:(p['operations'],p['scale_exponent'],p['multiplications']))
        return dict(best,requested_layout='auto',layout_candidate_ledgers=[ledger(p) for p in choices])
    return rewrite(parent.build(maps,layout),mode)


def ledger(packet):
    return dict(parent.ledger(packet),linear_mode=packet['linear_mode'],
                parent_operations=packet['parent_operations'],
                operations_saved=packet['parent_operations']-packet['operations'])


def replace_history(old, packet):
    """Compose any compatible complete raw history with the paid input boundary.

    The input loader and boundary gates remain literal; only the separately
    prefixed history block and its positive witnesses are replaced.  This
    also supports histories with fewer selected-value witnesses.
    """
    assert packet['parameters']==old['history_packet']['parameters']
    assert packet['maps']==old['history_packet']['maps'], 'history must retain the actual fixed tile table'
    def alias(v):
        if isinstance(v,int):return v
        if v=='Vinitial' and old['inline_initial']:return 'input_bottom'
        if v in packet['parameters']:return v
        return 'hist__'+v
    prefix=[row for row in old['source'] if not row[0].startswith('hist__')]
    source=prefix+[('hist__'+n,op,alias(a),alias(b)) for n,op,a,b in packet['source']]
    pairs=old['comparisons'][:old['boundary_comparisons']]+[(alias(a),alias(b)) for a,b in packet['comparisons']]
    aux=[n for n in old['auxiliaries'] if not n.startswith('hist__')]+['hist__'+n for n in packet['auxiliaries']]
    known=set(old['parameters']+aux)
    for n,_,a,b in source:
        assert n not in known and all(not isinstance(v,str) or v in known for v in (a,b))
        known.add(n)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==old['operations']-old['history_packet']['operations']+packet['operations']
    return dict(old,source=source,comparisons=pairs,auxiliaries=aux,history_packet=packet,
        layout=packet['layout'],operations=len(source),multiplications=counts['M'],
        additions_subtractions=counts['A'],equations=len(pairs),witnesses=len(aux))


def verify():
    import gpcp_complete_fixed_program as complete
    import gpcp_complete_fixed_program_units as complete_units
    rng=random.Random(180918)
    odd=complete.odd_machine()['history_packet']['maps']
    tables=[((1,0,1,0),),parent.DEFAULT_MAPS,
            tuple((4,i,4,i) for i in range(8)),
            ((2,3,4,5),(2,3,4,3),(4,8,2,1),(2,1,2,8)),odd]
    records=[];cases=signed=0
    for maps in tables:
      for layout in ('contiguous','interleaved'):
        old=parent.build(maps,layout);old_sos,oldout=parent.polynomial_source(old)
        for mode in linear.MODES:
            packet=rewrite(old,mode);source,out=parent.polynomial_source(packet)
            records.append(ledger(packet))
            for i in range(16):
                values={n:rng.randrange(1,5) if i<8 else rng.randrange(-2,4)
                        for n in packet['parameters']+packet['auxiliaries']}
                before=execute(old_sos,values);after=execute(source,values)
                assert [scalar(a,before)-scalar(b,before) for a,b in old['comparisons']]==[
                    scalar(a,after)-scalar(b,after) for a,b in packet['comparisons']]
                assert before[oldout]==after[out]
                for key,v in old['interfaces'].items():
                    assert scalar(v,before)==scalar(packet['interfaces'][key],after)
                cases+=1;signed+=i>=8
        best=rewrite(old)
        assert best['operations']<=old['operations']
    full=[];composed_cases=0
    for layout in ('contiguous','interleaved'):
      for inline in (False,True):
        old=complete.odd_machine(layout=layout,inline_initial=inline)
        packet=replace_history(old,rewrite(old['history_packet']))
        old_unit=complete_units.rewrite(old);new_unit=complete_units.rewrite(packet)
        for before,after,finalizer in ((old,packet,complete.polynomial_source),
                                      (old_unit,new_unit,complete_units.polynomial_source)):
            bs,bo=finalizer(before);ns,no=finalizer(after)
            assert before['parameters']==after['parameters'] and before['auxiliaries']==after['auxiliaries']
            for i in range(16):
                values={n:rng.randrange(-2,4) for n in before['parameters']+before['auxiliaries']}
                assert execute(bs,values)[bo]==execute(ns,values)[no]
                composed_cases+=1
        assert complete.degree_check(old)['exact_degree']==complete.degree_check(packet)['exact_degree']
        assert complete_units.degree_audit(old_unit)['exact_degree']==complete_units.degree_audit(new_unit)['exact_degree']
        full.append(dict(raw=complete.ledger(packet),unit=complete_units.ledger(new_unit),
                         raw_degree=complete.degree_check(packet)['exact_degree'],
                         unit_degree=complete_units.degree_audit(new_unit)['exact_degree']))
    example=build(odd)
    return dict(status='PASS_PCP_AFFINE_FACTORED_TRANSPORTS',
        full_polynomial_identities=cases,signed_cases=signed,ledgers=records,
        selected_examples=[ledger(build(maps)) for maps in tables],
        complete_composition_identities=composed_cases,complete_odd_machine_ledgers=full,
        example=dict(ledger=ledger(example),source=example['source'],comparisons=example['comparisons']),
        scope='Exact identities of every comparison residual and full SOS on all integer tuples. Native core, positive domain, witness count and polynomial degree are unchanged. Finite checks supplement the linear-form proof; the odd recognizer is not universal.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
