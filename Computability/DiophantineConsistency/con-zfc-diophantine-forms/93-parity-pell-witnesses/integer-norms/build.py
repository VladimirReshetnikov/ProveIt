#!/usr/bin/env python3
"""Build literal integer consistency equations by affine root-sum merging.

The inherited deterministic DAG emitter is copied byte for byte in
upstream_builder.py. Its main function is not run. New formulas are here.
All registers are polynomial abbreviations, never extra unknowns.
"""
import json
from pathlib import Path
import upstream_builder as old

ROOT = Path(__file__).resolve().parent


def common():
    regs = old.common17()
    for key in ('I', 'strong'):
        del regs[key]
    regs.update({'n': '2*n0+1', 'd': 'c**4',
                 'Q': 'Delta*(f**2-1)'})
    return regs


def make16(mod4=False):
    regs = common()
    if mod4:
        regs['n']='4*n0+2'
    regs.update({
        'n_total': 'n+B0' if mod4 else 'n+2*B0',
        'Gfirst': 'n**2+B0*(2*n-k)-1' if mod4 else 'n**2+4*B0*(n-k)-4',
        'Anorm': 'd*Gfirst+Q',
        'Nnorm': 'Anorm**2-4*d*n_total**2*Q',
    })
    variables = ['J','C','z','f','h','n0','v','w','nu','gamma','T',
                 'c','t','p1','p2','p3']
    rows = ['main','(V+nu)**2-Q*nu*(2*V+nu)-1','guard','Nnorm']
    name='integer16_mod4_degree112' if mod4 else 'integer16_odd_degree112'
    return old.construct(name, variables, regs, rows,
        112, {'c':16,'J':60,'w':12,'v':16,'h':8},
        '2**40*3**72*beta**60' if mod4 else '2**48*3**72*beta**60')


def make15(centered=False,mod4=False):
    regs = common()
    if mod4:
        regs['n']='4*(n0-h*Y*R)+2' if centered else '4*n0+2'
    elif centered:
        regs['n']='2*(n0-h*Y*R)+1'
    regs.update({
        'S': 'k*(2*m+1)',
        'Afirst': '1+B0*(B0+k)',
        'delta': 'Q-1',
        'den': 'd*delta',
        'n_total': 'n+B0+4*S*V' if mod4 else 'n+2*(B0+S*V)',
        'Abar': 'Afirst*den' if mod4 else '4*Afirst*den',
        'Bbar': 'Q*delta',
        'Cbar': '16*S**2*d*(Q*V**2-1)' if mod4 else '4*S**2*d*(Q*V**2-1)',
        'Ninner': 'den*n_total**2-Abar-Bbar-Cbar',
        'Nmiddle': 'Ninner**2-4*(Abar*Bbar+Abar*Cbar+Bbar*Cbar)',
        'Nnorm': 'Nmiddle**2-64*Abar*Bbar*Cbar*den*n_total**2',
        'Gsum': 'main**2+guard**2',
    })
    variables = ['J','C','z','f','h','n0','v','w','gamma','T',
                 'c','t','p1','p2','p3']
    rows = ['main','guard','Nnorm']
    degree=306 if centered else 310
    name='integer15_'+('mod4' if mod4 else 'odd')+'_degree'+str(degree)
    witness=({'c':16,'J':184,'w':26,'v':42,'h':14,'z':8,'f':16} if centered
        else {'c':16,'J':184,'w':28,'v':44,'h':16,'z':6,'f':16})
    coefficient=(('2**116*3**210*beta**184' if mod4 else '2**112*3**210*beta**184') if centered
                 else ('2**122*3**212*beta**184' if mod4 else '2**118*3**212*beta**184'))
    packet, _ = old.construct(name,variables,regs,rows,degree,witness,coefficient)
    expression = 'Gsum+Nnorm+Gsum*Nnorm'
    packet.update({'combination':'positive_unit_product',
        'polynomial_expression':expression,
        'single_equation':'positive sum-of-squares factor times norm factor minus one = 0'})
    builder = old.Circuit(variables,old.PORTS)
    for key,expr in regs.items():
        builder.symbols[key] = builder.parse(expr)
    circuit = builder.finish(builder.parse(expression))
    circuit.update({'name':packet['name'],'variables':variables,
        'fixed_ports':old.PORTS,'coefficient_binding':'../coefficients/BINDING.json'})
    return packet,circuit


def main():
    metrics=[]
    for packet,circuit in (make16(),make15(),make15(centered=True),
                           make16(mod4=True),make15(mod4=True),make15(centered=True,mod4=True)):
        name=packet['name']
        for directory in ('equations','circuits'):
            (ROOT/directory).mkdir(exist_ok=True)
        (ROOT/'equations'/f'{name}.json').write_text(json.dumps(packet,indent=2)+'\n')
        (ROOT/'circuits'/f'{name}.json').write_text(json.dumps(circuit,indent=2)+'\n')
        metrics.append({k:packet[k] for k in ('name','variable_count','residual_count','exact_degree')} |
                       {'live_binary_operations':circuit['live_binary_operations'],'counts':circuit['counts']})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))


if __name__=='__main__':
    main()
