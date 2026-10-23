#!/usr/bin/env python3
"""Emit a new fourteen-positive-coordinate norm circuit (stdlib only)."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def build():
    rows = []
    def gate(name, op, a, b):
        rows.append([name, op, a, b])
        return name
    gate('q_minus_one','*','beta','J')
    gate('q','+','q_minus_one',1)
    gate('q2','*','q','q')
    gate('q3','*','q2','q')
    gate('q4','*','q2','q2')
    gate('U','*',4,'q4')
    gate('X','*','w','q')
    gate('Y','*','s','q3')
    gate('E','*','X','Y')
    gate('k','+','eta','zeta')
    gate('kY','*','k','Y')
    gate('ell','*','E','kY')
    gate('ell_plus_k','+','ell','k')
    gate('first_radical_part','*','ell','ell_plus_k')
    gate('tau2','*','tau','tau')
    gate('N0','-','tau2','first_radical_part')
    gate('c','+','kY','eta')
    gate('a','+','E','Y')
    gate('ac','*','a','c')
    gate('b0','+','X','ac')
    gate('four_a','*',4,'a')
    gate('H','+','four_a',3)
    gate('a2','*','a','a')
    gate('Delta','+','a2','H')
    gate('c2','*','c','c')
    gate('Delta_c2','*','Delta','c2')
    gate('G','+','Delta_c2',1)
    gate('q_minus_F','-','q','F')
    gate('C','-','q_minus_F','alpha')
    gate('gap_product','*','q_minus_one','q_minus_F')
    gate('gap','+','gap_product','alpha')
    gate('q2_minus_one','-','q2',1)
    gate('R_product','*','gap','q2_minus_one')
    gate('qMF','*','q','MF')
    gate('mask_factor','+','MC','qMF')
    gate('mask','*','mask_factor','J')
    gate('R','+','R_product','mask')
    gate('r_plus_one','-','k','R')
    gate('r','-','r_plus_one',1)
    gate('U_gamma','*','U','gamma')
    gate('carrier','-','U_gamma','r')
    gate('H_carrier','*','H','carrier')
    gate('U_b0','*','U','b0')
    gate('D_scaled','+','U_b0','H_carrier')
    gate('D_scaled2','*','D_scaled','D_scaled')
    gate('U2','*','U','U')
    gate('U2G','*','U2','G')
    gate('main_residual','-','D_scaled2','U2G')
    gate('Kplusw','+','K0','w')
    gate('transport_product','*','Kplusw','C')
    gate('transport_sum','+','transport_product','q_minus_F')
    gate('transport_rhs','*','z','q_minus_one')
    gate('Nt','-','transport_sum','transport_rhs')
    gate('f2','*','f','f')
    gate('f2_minus_one','-','f2',1)
    gate('Tf','*','T','f')
    gate('Tf_minus_one','-','Tf',1)
    gate('c_Tf_minus_one','*','c','Tf_minus_one')
    gate('Rf2','*','R','f2')
    gate('V','-','c_Tf_minus_one','Rf2')
    gate('V2','*','V','V')
    gate('y2','*','y','y')
    gate('V2_minus_y2','-','V2','y2')
    gate('I','*','i','c2')
    gate('I2','*','I','I')
    gate('aux_coefficient','*','Delta','f2_minus_one')
    gate('strong_residual','-','I2','aux_coefficient')
    gate('aux_term','*','aux_coefficient','V2_minus_y2')
    gate('Na','+','aux_term','y2')
    gate('aux_residual','-','Na',1)
    gate('first_transport','*','N0','Nt')
    gate('first_transport_residual','-','first_transport',1)
    residuals=['main_residual','strong_residual','aux_residual','first_transport_residual']
    for r in residuals:
        gate(r+'_square','*',r,r)
    gate('sum0','+','main_residual_square','strong_residual_square')
    gate('sum1','+','sum0','aux_residual_square')
    gate('polynomial','+','sum1','first_transport_residual_square')
    return dict(name='fourteen_positive_ordinary_quartic_modulus_norm',witness_domain='strictly positive integers',
                witnesses=['J','F','alpha','z','f','i','T','s','w','tau','eta','zeta','y','gamma'],
                fixed_numerals=['beta','K0','MC','MF'],source=rows,output='polynomial',
                source_commit='124c07c0b77a9e20e84676514d8b1ff78536ea3f',
                coefficient_binding='../coefficients/ports.json',
                selected_tuple='31-sun10 complete 121-by-8801 tuple; MF is already shifted',
                proof_boundary='Ordinary mathematical adapter; no new end-to-end Lean certificate.')

if __name__ == '__main__':
    data=build()
    (ROOT/'fourteen_positive.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'operations':len(data['source']),'counts':{op:sum(row[1]==op for row in data['source']) for op in '+-*'}}))
