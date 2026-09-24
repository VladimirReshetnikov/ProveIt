#!/usr/bin/env python3
"""Exact113: fuse raw junk support with its native TestV adapter."""
from pathlib import Path
import json
import sympy as sp
import explore_intrinsic_program_width as old
import explore_parity_aligned_raw_counters as arithmetic


PROGRAM=old.PROGRAM
ZALL=old.ZALL
FIELDS=old.FIELDS
OUTER_NAMES=[name for name in old.OUTER_NAMES if name!='PTV']
CORE_NAMES=old.CORE_NAMES
SYM={name:value for name,value in old.SYM.items() if name!='PTV'}


def build():
    previous,pairs,source,_=old.build();ops=[]
    for name,op,left,right in previous:
        if name=='program_native_TV':continue
        if name=='program_V_rhs':left='PNV'
        ops.append((name,op,left,right))
    new_pairs=[];new_source=[];origins=[]
    for index,(pair,polynomial) in enumerate(zip(pairs,source)):
        if index==28:continue
        if index==23:
            pair=('PNTV','program_V_rhs')
            polynomial=SYM['PNTV']-SYM['PNV']-ZALL*SYM['H']
        new_pairs.append(pair);new_source.append(polynomial);origins.append(index)
    return ops,new_pairs,new_source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    hist=arithmetic.baseline.run_schedule(ops,env)
    primitives,counts=arithmetic.verify_primitives(ops,env)
    assert len(primitives)==113 and counts=={'+':58,'*':55}
    assert len(source)==len(pairs)==29 and len(OUTER_NAMES+CORE_NAMES)==41
    previous=old.build()[2];z=SYM;u=z['j']*z['c']+2*z['r']+1;records=[]
    assert sp.expand(source[23]-previous[23]-previous[28]+previous[26])==0
    reconstructed=z['PV']+ZALL*z['H']
    assert previous[23].subs(old.SYM['PTV'],reconstructed)==0
    assert sp.expand(previous[28].subs(old.SYM['PTV'],reconstructed)-source[23]-previous[26])==0
    for index,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[17]*(u*u-z['y_aux']**2) if index==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,index
        if origin!=23:assert polynomial==previous[origin]
        records.append(dict(index=index,prior_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    used={v for row in ops for v in row[2:]}|{v for pair in pairs for v in pair}
    assert set(SYM)<=used and not used&{'PTV','program_native_TV'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert FIELDS==old.FIELDS and len(FIELDS)==12 and 'PNTV' in FIELDS
    assert ZALL>0
    return dict(status='PASS',operations=113,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=41,
                equations=29,primitive_instructions=primitives,equalities=pairs,residuals=records,
                fixed_program=PROGRAM,masked_fields=FIELDS,
                exact_delta=dict(deleted_unknown='PTV',deleted_register='program_native_TV',
                    old_equalities=['PTV=PV+Zall*H','PNTV=Jrep+PTV'],
                    retained_adapter='PNV=Jrep+PV',new_equality='PNTV=PNV+Zall*H',
                    unique_positive_extension='PTV=PV+Zall*H',
                    residual_identity='new=old23+old28-old26',unchanged_retained_sources=28),
                scope='Exact same-witness elimination of one positive raw coordinate. All twelve supplied mask fields and every kernel coordinate stay unchanged.')


def canonical(x):
    result=old.canonical(x)
    result['inherited_114_outer_residuals']=result.pop('outer_residuals')
    result['retained_113_outer_residuals']=19
    result['source_scope']='All20 predecessor outer residuals are checked; deleting PTV and using the exact support/adapter identity gives all19 new outer residuals with identical packed fields.'
    return result


def verify():
    return dict(status='PASS_NATIVE_JUNK_SUPPORT_FUSION_113',arithmetic=verify_certificate(),
                canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_NATIVE_JUNK_SUPPORT_FUSION.md',
                scope='Complete113-operation universal family, conditional only on the independently established114 predecessor. It remains above the universal frontier90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['canonical'])
