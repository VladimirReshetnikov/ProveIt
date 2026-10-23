#!/usr/bin/env python3
"""Build the 14-positive-variable, degree-30, 83-gate equation.

All registers are polynomial abbreviations. Four fixed leaves bind to the
whole compact native tuple in native/COEFFICIENT_BINDING.json.
"""
from pathlib import Path
from collections import Counter
import json

HERE = Path(__file__).resolve().parent

def build():
    rows = []
    def g(name, op, left, right):
        rows.append([name, op, left, right])
    g('q_minus_one','*','beta','J')
    g('q','+','q_minus_one',1)
    g('q2','*','q','q')
    g('q3','*','q2','q')
    g('U','*','Y','Y')
    g('X','*','w','q')
    g('E','*','X','Y')
    g('k','+','eta','zeta')
    g('kY','*','k','Y')
    g('ell','*','E','kY')
    g('ell_plus_k','+','ell','k')
    g('first_product','*','ell','ell_plus_k')
    g('first_radicand','+','first_product',1)
    g('ell_plus_rho','+','ell','rho')
    g('scaled_gap','*','q3','ell_plus_rho')
    g('first_carrier','+','scaled_gap','Y')
    g('first_carrier_square','*','first_carrier','first_carrier')
    g('q6','*','q3','q3')
    g('scaled_first_radicand','*','q6','first_radicand')
    g('A0','-','first_carrier_square','scaled_first_radicand')
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
    g('main_gap','-','U_gamma','r')
    g('H_main_gap','*','H','main_gap')
    g('U_b0','*','U','b0')
    g('Dstar','+','U_b0','H_main_gap')
    g('Dstar2','*','Dstar','Dstar')
    g('U2','*','U','U')
    g('U2G','*','U2','G')
    g('M','-','Dstar2','U2G')
    g('Kplusw','+','K0','w')
    g('transport_product','*','Kplusw','C')
    g('transport_sum','-','transport_product','F')
    g('transport_rhs','*','z','q_minus_one')
    g('Lt','-','transport_sum','transport_rhs')
    g('f2','*','f','f')
    g('f2_minus_one','-','f2',1)
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
    g('W','-','I2','Aaux')
    g('aux_term','*','Aaux','square_gap')
    g('Na','+','aux_term','y2')
    for n in ('A0','M','W','Na','Lt'):
        g(n+'_square','*',n,n)
    g('sum0','+','A0_square','M_square')
    g('sum1','+','sum0','W_square')
    g('sum2','+','sum1','Na_square')
    g('sum3','+','sum2','Lt_square')
    g('polynomial','-','sum3',1)
    return {'name':'free_ordinate_absorber14_degree30',
            'witness_domain':'strictly positive integers',
            'witnesses':['J','F','alpha','z','f','i','T','Y','w','rho','eta','zeta','e','gamma'],
            'fixed_numerals':['beta','K0','MC','MF'],
            'coefficient_binding':{'file':'native/COEFFICIENT_BINDING.json',
                'aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}},
            'source':rows,'output':'polynomial',
            'operations':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),
            'exact_degree':30,'residual_degrees':{'A0':12,'M':14,'W':10,'Na':15,'Lt':2},
            'proof':'PROOF.md',
            'formal_status':'Ordinary mathematical proof with explicitly inherited native/Pell/K215 dependencies; no new kernel-checked end-to-end theorem.'}

if __name__ == '__main__':
    p=build()
    (HERE/'polynomial.json').write_text(json.dumps(p,indent=2)+'\n')
    print(json.dumps({k:p[k] for k in ['operations','operation_counts','exact_degree','residual_degrees']},indent=2))
