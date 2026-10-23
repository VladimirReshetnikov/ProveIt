#!/usr/bin/env python3
"""Emit the 14-positive-variable, degree-52, 79-operation polynomial.

This is an ordinary mathematical adapter, not a proof-assistant certificate.
All four non-small integer constants are bound by coefficients/ports.json.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def build():
    rows = []
    def g(name, op, left, right):
        rows.append([name, op, left, right])
    g('q_minus_one','*','beta','J')
    g('q','+','q_minus_one',1)
    g('q2','*','q','q')
    g('q3','*','q2','q')
    g('q4','*','q2','q2')
    g('U','*',4,'q4')
    g('X','*','w','q')
    g('Y','*','s','q3')
    g('E','*','X','Y')
    g('k','+','eta','zeta')
    g('kY','*','k','Y')
    g('ell','*','E','kY')
    g('ell_plus_k','+','ell','k')
    g('first_part','*','ell','ell_plus_k')
    g('tau2','*','tau','tau')
    g('N0','-','tau2','first_part')
    g('c','+','kY','eta')
    g('a','+','E','Y')
    g('ac','*','a','c')
    g('b0','+','X','ac')
    g('four_a','*',4,'a')
    g('H','+','four_a',3)
    g('a2','*','a','a')
    g('Delta','+','a2','H')
    g('c2','*','c','c')
    g('Delta_c2','*','Delta','c2')
    g('G','+','Delta_c2',1)
    g('q_minus_F','-','q','F')
    g('C','-','q_minus_F','alpha')
    g('gap_product','*','q_minus_one','q_minus_F')
    g('gap','+','gap_product','alpha')
    g('q2_minus_one','-','q2',1)
    g('R_product','*','gap','q2_minus_one')
    g('qMF','*','q','MF')
    g('mask_factor','+','MC','qMF')
    g('mask','*','mask_factor','J')
    g('R','+','R_product','mask')
    g('r_plus_one','-','k','R')
    g('r','-','r_plus_one',1)
    g('U_gamma','*','U','gamma')
    g('carrier','-','U_gamma','r')
    g('H_carrier','*','H','carrier')
    g('U_b0','*','U','b0')
    g('Dstar','+','U_b0','H_carrier')
    g('Dstar2','*','Dstar','Dstar')
    g('U2','*','U','U')
    g('U2G','*','U2','G')
    g('main_residual','-','Dstar2','U2G')
    g('Kplusw','+','K0','w')
    g('transport_product','*','Kplusw','C')
    g('transport_sum','+','transport_product','q_minus_F')
    g('transport_rhs','*','z','q_minus_one')
    g('Nt','-','transport_sum','transport_rhs')
    g('f2','*','f','f')
    g('f2_minus_one','-','f2',1)
    # Squared-modulus quotient: old T = f*T.  Four gates, versus five.
    g('cT','*','c','T')
    g('quotient_gap','-','cT','R')
    g('f2_quotient','*','f2','quotient_gap')
    g('V','-','f2_quotient','c')
    g('y','+','V','e')
    g('V2','*','V','V')
    g('y2','*','y','y')
    g('square_gap','-','V2','y2')
    g('I','*','i','c2')
    g('I2','*','I','I')
    g('Aaux','*','Delta','f2_minus_one')
    g('strong_residual','-','I2','Aaux')
    g('aux_term','*','Aaux','square_gap')
    g('Na','+','aux_term','y2')
    g('first_transport','*','N0','Nt')
    g('first_transport_residual','-','first_transport',1)
    for name in ('main_residual','strong_residual','Na','first_transport_residual'):
        g(name+'_square','*',name,name)
    g('sum0','+','main_residual_square','strong_residual_square')
    g('sum1','+','sum0','Na_square')
    g('sum2','+','sum1','first_transport_residual_square')
    g('polynomial','-','sum2',1)
    if len(rows) != 79:
        raise ValueError('Unexpected operation count')
    return {
        'name':'absorbed_gap14_degree52',
        'witness_domain':'strictly positive integers',
        'witnesses':['J','F','alpha','z','f','i','T','s','w','tau','eta','zeta','e','gamma'],
        'fixed_numerals':['beta','K0','MC','MF'],
        'coefficient_binding':'coefficients/ports.json',
        'source':rows,'output':'polynomial',
        'operations':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),
        'exact_degree':52,
        'inheritance':'PROOF.md and upstream/',
        'formal_status':'Ordinary mathematical reduction; no new Lean/Rocq certificate.'}

if __name__ == '__main__':
    data=build()
    (ROOT/'polynomial.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:data[k] for k in ('operations','operation_counts','exact_degree')}))
