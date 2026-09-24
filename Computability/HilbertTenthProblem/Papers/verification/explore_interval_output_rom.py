#!/usr/bin/env python3
"""Scoped rejection of direct dense-gap output in the fixed-row ROM."""
from pathlib import Path
import json
import sympy as sp
import explore_complemented_counter_guards as base


def verify():
    c=base.PROGRAM;Zstar=base.ZALL
    Kzero=sum(3**(c['d']+c['bz']-c['a'][i]) for i in range(len(c['a'])) if c['zeros'][i]==0)
    Kbase=c['K']-Kzero
    assert Kbase>0 and Kzero>0
    R,g,C,K0,K1,hz,D=sp.symbols('R g C K0 K1 hz D',integer=True)
    assert sp.expand((K0+g*K1)*C-hz*(g*D)-(K0*C+g*(K1*C-hz*D)))==0
    rows=[];row_checks=0
    for extra in (0,1,2):
        width=c['B']+extra;radix=3**width;gap_factor=(radix-3)//6
        assert 6*gap_factor==radix-3 and 9*gap_factor>=radix
        table=Kbase+gap_factor*Kzero
        assert table*c['S']>=radix
        for i,j in c['edges']:
            state=3**c['a'][i];nextstate=3**c['a'][j]
            sign=int(c['signs'][i]==1);nozero=1-c['zeros'][i]
            ordinary=Kbase*state-c['g']*nextstate-c['hs']*sign
            cross=Kzero*state-c['hz']*nozero
            assert ordinary>=0 and cross>0
            other=next(k for k in range(len(c['a'])) if c['zeros'][k]==0 and k!=i)
            exponent=c['d']+c['bz']+c['a'][i]-c['a'][other]
            assert exponent>=2 and cross>=3**exponent
            junk=table*state-c['g']*nextstate-c['hs']*sign-c['hz']*gap_factor*nozero
            assert junk==ordinary+gap_factor*cross>=radix
            row_checks+=1
        rows.append(dict(width=width,canonical_row_products_fit=False,
                         minimum_dense_cross_term_exponent=2,
                         scope='Every edge of the unchanged six-state table has another nozero-emitting state, forcing a cross interval at least one radix long.'))
    canonical=[]
    for x in (1,2):
        radix=c['Rmin'];factor=(radix-3)//6
        path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
        u=len(path)-1;q=radix**u;J=(q-1)//2;H=(q-1)//(radix-1)
        Cword=Next=Kp=Dword=V=0;table=Kbase+factor*Kzero
        for b,i in enumerate(path[:-1]):
            j=path[b+1];assert (i,j) in c['edges']
            weight=radix**b;state=3**c['a'][i];nextstate=3**c['a'][j]
            sign=int(c['signs'][i]==1);nozero=1-c['zeros'][i]
            junk=table*state-c['g']*nextstate-c['hs']*sign-c['hz']*factor*nozero
            assert junk>=radix
            Cword+=state*weight;Next+=nextstate*weight;Kp+=sign*weight;Dword+=nozero*weight;V+=junk*weight
        gap=factor*Dword
        assert V==table*Cword-c['g']*Next-c['hs']*Kp-c['hz']*gap
        entry=3**c['a'][path[0]]
        assert radix*Next==Cword+(q-1)*entry
        assert (radix*table-c['g'])*Cword==c['g']*entry*(q-1)+radix*(V+c['hs']*Kp+c['hz']*gap)
        assert V>=q
        TV=V+Zstar*H
        assert TV>J
        canonical.append(dict(x=x,serial_blocks=u,width=c['B'],junk_at_least_q=True,
                              required_top_field_bound_fails=True,
                              source_route_identity_preserved=True,
                              scope='Exact direct transformation of the existing canonical path; the retained TV<=J packed-bound consequence rejects it. No alternate interval encoding is ruled out.'))
    return dict(status='PASS_DIRECT_INTERVAL_ROM_OBSTRUCTION',
                formal_operation_ledger=dict(base_operations=104,base_histogram={'*':55,'+':49},
                    replaced_top_and_flag_vs_new_factor_table_net={'*':0,'+':0},
                    one_fewer_Horner_field={'*':-1,'+':-1},
                    q11_scale_extra_product={'*':1,'+':0},
                    purely_formal_total=103,purely_formal_histogram={'*':55,'+':48},
                    not_a_correct_certificate=True),
                checked_row_products=row_checks,width_tests=rows,canonical=canonical,
                proof='../1980/EXPLORATION_INTERVAL_OUTPUT_ROM.md',
                scope='Exact algebra/count ledger for the proposed direct table change and a uniform canonical row-overflow obstruction. No valid103 system or universal lower bound is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']);print(result['formal_operation_ledger']);print(result['checked_row_products']);print(result['canonical'])
