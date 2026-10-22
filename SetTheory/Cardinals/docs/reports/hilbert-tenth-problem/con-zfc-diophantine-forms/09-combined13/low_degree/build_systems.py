#!/usr/bin/env python3
"""Emit and audit the ordinary-strong inputless sources (no dependencies)."""
import json
from pathlib import Path
from sparse_polynomial import Ring

CONSTANTS=['beta','K0','MC','MF']
COEFFICIENT_BINDING={
    'manifest':'../COEFFICIENT_BINDINGS.json',
    'default_recipe_from_package_root':'compiler/tshape_constants.json',
    'arithmetic_interface_origin':'06-blank67',
    'mask_convention':'MF is the shifted mask port',
}
BASE15='J F alpha z f h i T s w tau eta zeta y gamma'.split()
BASE16='J F alpha z f h i o j s w tau eta zeta y gamma'.split()

def build(retained=False):
    witnesses=BASE16 if retained else BASE15
    rows=[]
    def emit(name,op,lhs,rhs):
        rows.append([name,op,lhs,rhs])
        return name
    emit('tau2','*','tau','tau')
    emit('rep','*','beta','J')
    emit('q','+','rep',1)
    emit('q2','*','q','q')
    emit('q3','*','q2','q')
    emit('X','*','w','q')
    emit('Y','*','s','q3')
    emit('E','*','X','Y')
    emit('k','+','eta','zeta')
    emit('kY','*','k','Y')
    emit('Lfirst','*','E','kY')
    emit('first_next','+','Lfirst','k')
    emit('first_product','*','Lfirst','first_next')
    emit('N0','-','tau2','first_product')
    emit('c','+','kY','eta')
    emit('a','+','E','Y')
    emit('ac','*','a','c')
    emit('Dbase','+','X','ac')
    emit('a4','*',4,'a')
    emit('H','+','a4',3)
    emit('gammaH','*','gamma','H')
    emit('D','+','Dbase','gammaH')
    emit('D2','*','D','D')
    emit('a2','*','a','a')
    emit('Delta','+','a2','H')
    emit('c2','*','c','c')
    emit('Dc2','*','Delta','c2')
    emit('N1','-','D2','Dc2')
    emit('qF','-','q','F')
    emit('C','-','qF','alpha')
    emit('y2','*','y','y')
    emit('hE','*','h','E')
    emit('index_part','-','k','hE')
    emit('gap_product','*','rep','qF')
    emit('G','+','gap_product','alpha')
    emit('q2m1','-','q2',1)
    emit('Rprod','*','G','q2m1')
    emit('qMF','*','q','MF')
    emit('mask_factor','+','MC','qMF')
    emit('mask','*','mask_factor','J')
    emit('R','+','Rprod','mask')
    emit('Nk','-','index_part','R')
    emit('Kplusw','+','K0','w')
    emit('innerC','*','Kplusw','C')
    emit('trans_part','+','innerC','qF')
    emit('zrep','*','z','rep')
    emit('Nt','-','trans_part','zrep')
    emit('f2','*','f','f')
    if retained:
        emit('of','*','o','f')
        emit('V','-','of','c')
        emit('jc','*','j','c')
        emit('U','-','jc','R')
    else:
        emit('Tf','*','T','f')
        emit('Tfm1','-','Tf',1)
        emit('cTfm1','*','c','Tfm1')
        emit('Rf2','*','R','f2')
        emit('V','-','cTfm1','Rf2')
    emit('V2','*','V','V')
    emit('aux_gap','-','V2','y2')
    emit('I','*','i','c2')
    emit('I2','*','I','I')
    emit('f2m1','-','f2',1)
    emit('A0','*','Delta','f2m1')
    emit('aux_product','*','A0','aux_gap')
    emit('Na','+','aux_product','y2')
    comparisons=[['N0',1],['N1',1],['Na',1],['Nk',1],['Nt',1],['I2','A0']]
    if retained:
        comparisons.append(['U','V'])
    return {'name':'retained16_system60' if retained else 'ordinary15_system61',
            'witness_domain':'strictly positive integers',
            'witnesses':witnesses,'fixed_numerals':CONSTANTS,
            'coefficient_binding':COEFFICIENT_BINDING,
            'source':rows,'comparisons':comparisons}

def audit(packet):
    witnesses=packet['witnesses']
    ring=Ring(witnesses+CONSTANTS)
    values=dict(ring.variables)
    def val(x):return ring.coerce(x) if isinstance(x,int) else values[x]
    for name,op,lhs,rhs in packet['source']:
        assert name not in values
        a,b=val(lhs),val(rhs)
        values[name] = a+b if op=='+' else a-b if op=='-' else a*b
    residuals=[val(lhs)-val(rhs) for lhs,rhs in packet['comparisons']]
    degrees=[p.degree(len(witnesses)) for p in residuals]
    operations=len(packet['source'])
    multiplications=sum(row[1]=='*' for row in packet['source'])
    # Backward liveness audit.
    live={x for pair in packet['comparisons'] for x in pair if isinstance(x,str)}
    for name,op,lhs,rhs in reversed(packet['source']):
        assert name in live, name
        for x in (lhs,rhs):
            if isinstance(x,str):live.add(x)
    assert all(x in live for x in witnesses+CONSTANTS)
    packet['ledger']={'operations':operations,'multiplications':multiplications,
        'additions_subtractions':operations-multiplications,
        'all_gates_live':True,'all_ports_live':True}
    packet['residual_exact_degrees']=degrees
    packet['highest_homogeneous_terms']=[
        [{'powers':list(m),'coefficient':c} for m,c in p.terms.items() if sum(m[:len(witnesses)])==d]
        for p,d in zip(residuals,degrees)]
    packet['homogeneous_term_coordinate_order']=list(ring.names)
    packet['sum_of_squares']={
        'degree':2*max(degrees),
        'operations':operations+3*len(residuals)-1,
        'multiplications':multiplications+len(residuals),
        'additions_subtractions':operations-multiplications+2*len(residuals)-1,
        'definition':'sum of squared (left-right) comparison residuals',
        'degree_proof':'Only the auxiliary residual attains the largest degree; its square has nonzero leading form.',
    }
    sos_source=list(packet['source'])
    for index,(lhs,rhs) in enumerate(packet['comparisons']):
        sos_source.append([f'residual{index}','-',lhs,rhs])
        sos_source.append([f'square{index}','*',f'residual{index}',f'residual{index}'])
    running='square0'
    for index in range(1,len(residuals)):
        name=f'sos{index}'
        sos_source.append([name,'+',running,f'square{index}'])
        running=name
    assert len(sos_source)==packet['sum_of_squares']['operations']
    packet['sum_of_squares'].update(source=sos_source,output=running)
    return residuals,values

def main():
    root=Path(__file__).resolve().parent
    receipts=[]
    for retained in [False,True]:
        packet=build(retained)
        _,values=audit(packet)
        if retained:
            assert packet['ledger']['operations']==60
            assert packet['residual_exact_degrees']==[22,18,24,7,2,22,6]
        else:
            assert packet['ledger']['operations']==61
            assert packet['residual_exact_degrees']==[22,18,28,7,2,22]
            # Each factor has a nonzero leading form over Z[beta,K0,MC,MF].
            # Product degree is the sum in this integral domain; subtracting1
            # cannot alter that degree.
            packet['product69']={
                'factor_definitions':['N0','N1','Na','Nk','Nt','1+I2-A0'],
                'polynomial':'N0*N1*Na*Nk*Nt*(1+I2-A0)-1',
                'degree':99,'operations':69,
                'multiplications':39,'additions_subtractions':30,
                'factor_degrees':[22,18,28,7,2,22],
                'scope':'Uses the ordinary-strong unit-sign proof in ../proofs/LOW_DEGREE_PROOF.md.'
            }
            product_rows=list(packet['source'])+[
                ['strong_plus1','+','I2',1],
                ['Ns','-','strong_plus1','A0'],
                ['factor2','*','N0','N1'],
                ['factor3','*','factor2','Na'],
                ['factor4','*','factor3','Nk'],
                ['factor5','*','factor4','Nt'],
                ['factor6','*','factor5','Ns'],
                ['P69','-','factor6',1],
            ]
            assert len(product_rows)==69
            packet['product69'].update(source=product_rows,output='P69')
        packet['formal_status']='Exact finite polynomial checks; imported Pell/compiler mathematics is not kernel checked here.'
        (root/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        receipt={k:packet[k] for k in ['name','coefficient_binding','ledger','residual_exact_degrees']}
        receipt['sum_of_squares']={k:v for k,v in packet['sum_of_squares'].items() if k!='source'}
        receipts.append(receipt)
    (root/'system_checks.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))

if __name__=='__main__':main()
