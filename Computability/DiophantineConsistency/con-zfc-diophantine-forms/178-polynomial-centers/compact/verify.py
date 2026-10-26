#!/usr/bin/env python3
"""Independent exact graph, degree and identity checker.

No producer or inherited verifier is imported. Polynomial arithmetic is
retained with attribution in polynomial.py. Formula cuts cover every gate.
This checks finite artifacts, not the unbounded proof in PROOF.md.
"""
from collections import Counter
from pathlib import Path
import argparse
import copy
import gzip
import hashlib
import json
from polynomial import Poly, require

ROOT = Path(__file__).resolve().parent
INPUTS = ['J', 'F', 'alpha', 'i', 'T', 'w', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']


def topology(g):
    require(g['domain'] == 'strictly positive integers', 'domain')
    require(g['witnesses'] == INPUTS, 'witnesses')
    require(g['fixed_numerals'] == PORTS, 'fixed ports')
    require(g['transport_weight'] in ('bV','b2'),'transport weight')
    require(g['root_scale']==(2 if g['center_parameter']=='quotient' else 1),
            'fixed root scale')
    available = set(INPUTS + PORTS)
    deps = {}
    for name, op, x, y in g['source']:
        require(name not in available, 'duplicate register')
        require(op in ['+', '-', '*'], 'ordinary arithmetic only')
        for a in [x, y]:
            require(type(a) is int or a in available, 'operand topology')
        deps[name] = (x, y)
        available.add(name)
    live = set()
    def visit(name):
        if type(name) is int or name in live:
            return
        live.add(name)
        for arg in deps.get(name, ()):
            visit(arg)
    visit(g['output'])
    require(live == available, 'every gate, input and port is live')
    require(g['operations'] == len(g['source']), 'operation count')
    counts = dict(Counter(r[1] for r in g['source']))
    require(counts == g['operation_breakdown'], 'operation classes')
    cost = {'A':88,'Am1':87,'quotient':96,None:85}[g['center_parameter']]
    require(g['operations'] == cost, 'expected cost')
    return counts


def cuts(g):
    definitions = {r[0]: r[1:] for r in g['source']}
    boundary = {n: Poly.v(n) for n in INPUTS + PORTS}
    used, receipts = set(), []
    def expand(n, memo):
        if type(n) is int: return Poly(n)
        if n in boundary: return boundary[n]
        if n in memo: return memo[n]
        op, x, y = definitions[n]
        used.add(n)
        a, b = expand(x, memo), expand(y, memo)
        memo[n] = a+b if op == '+' else a-b if op == '-' else a*b
        return memo[n]
    def cut(n, expected):
        p = expand(n, {})
        require(p == expected, 'free polynomial cut: ' + n)
        receipts.append({'register': n, 'terms': len(p.d)})
        boundary[n] = Poly.v(n)
    p = boundary.__getitem__
    cut('bJ', p('beta')*p('J'))
    cut('q', p('bJ')+1)
    cut('q2', p('q')**2)
    cut('q4', p('q2')**2)
    cut('q6', p('q4')*p('q2'))
    cut('sixq6', 6*p('q6'))
    cut('Y', p('q')*p('s'))
    cut('qmF', p('q')-p('F'))
    cut('C', p('qmF')-p('alpha'))
    cut('X', p('q')*p('w'))
    cut('k', p('eta')+p('zeta'))
    cut('kY', p('k')*p('Y'))
    cut('c', p('kY')+p('eta'))
    cut('XY', p('X')*p('Y'))
    cut('Am1', p('XY')+p('Y'))
    cut('Ap1', p('Am1')+2)
    cut('Hp', 4*p('Am1')-1)
    cut('V0k', p('XY')*p('kY'))
    cut('Dtau', 1+p('V0k')*(p('V0k')+p('k')))
    cut('R', (p('bJ')*p('qmF')+p('alpha'))*(p('q2')-1)
             +(p('MC')+p('q')*p('MF'))*p('J'))
    cut('eclear', 6*(p('k')-p('R')-1-p('q4')*p('s'))
                  -p('V0k')*(p('k')**2-4))
    cut('Bt', (p('K0')+p('w'))*p('C')-p('F'))
    cut('U', p('i')*p('c')**2)
    cut('UE', p('U')*p('Dtau'))
    cut('Delta', p('Am1')*p('Ap1'))
    cut('DpI2', p('Delta')*p('UE')*p('U'))
    cut('Df', 1+p('DpI2'))
    cut('trace_f', p('DpI2')+p('Df'))
    cut('Q', 4*p('Delta')*p('DpI2')*p('Df'))
    cut('cTR', p('c')*p('T')-p('R'))
    cut('V', p('trace_f')*p('cTR')-p('c'))
    cut('V2', p('V')**2)
    if g['polynomial_center']:
        if g['center_parameter'] in ('A','quotient'): cut('A', p('Am1')+1)
        if g['center_parameter']=='quotient':
            cut('quotient_E', p('kY')*(p('V0k')+p('k')-p('kY')*(p('Y')+1)))
            cut('center_root', 2*p('A')*p('UE')-p('U')*p('quotient_E'))
        else:
            cut('center_root', p(g['center_parameter'])*p('UE'))
        center = p('n')-p('V')*(p('cTR')*p('Bt')+p('center_root'))
    else:
        cut('L', p('cTR')**2 if g['transport_weight'] == 'b2' else p('cTR')*p('V'))
        center = p('n')-p('L')*p('Bt')
    cut('center', center)
    cut('Kpos', p('X')*(3*p('c')-2*p('X'))+2)
    cut('Znum', p('bJ')*p('sixq6')*(p('Hp')*p('center')+p('Kpos'))
         -p('Hp')*(p('sixq6')*p('Bt')+p('bJ')*p('eclear')))
    cut('Mtot', p('bJ')*p('sixq6')*p('Hp'))
    cut('Dg', p('Dtau')*p('Df'))
    if g['root_scale']==2:cut('scaledG',4*p('Dg'))
    rg = p('Mtot')**2*p('scaledG' if g['root_scale']==2 else 'Dg')
    cut('N', p('Q')*(p('Znum')**2-rg*p('V2'))+rg-p('Znum')**2)
    require(used == set(definitions), 'all actual graph gates covered')
    return receipts


def identities():
    A, U, E = map(Poly.v, ('A', 'U', 'E'))
    delta = A*A-1
    a = delta*U*U*E
    G = E*(1+a)
    C = A*U*E
    S = (U*E)**2-E
    require(C*C-G == S, 'center defect identity')
    require(((A-1)*U*E)**2-G == -2*(A-1)*(U*E)**2-E,
            'lower center defect identity')
    QE=Poly.v('QE');RE=E-A*QE
    C2=2*A*U*E-U*QE
    require(C2*C2-4*G==4*U*U*E*RE+U*U*QE*QE-4*E,
            'quotient center defect identity')
    X,Y,k=map(Poly.v,('X','Y','k'))
    aa=Y*(X+1)+1;ell=X*Y*Y*k;ee=1+ell*(ell+k)
    qq=Y*k*(ell+k-Y*k*(Y+1))
    rr=1+k*k*Y*(Y+1)*(Y*(Y+1)-1)
    require(ee==aa*qq+rr,'exact quotient and positive remainder')
    Q, M, Z, V, CC, SS = map(Poly.v, ('Q', 'M', 'Z', 'V', 'C', 'S'))
    GG = CC*CC-SS
    shifted = Z-M*CC*V
    old = Q*(shifted*shifted-M*M*GG*V*V)+M*M*GG-shifted*shifted
    expanded = ((Q-1)*Z*Z - 2*(Q-1)*M*CC*V*Z
                +M*M*((Q-1)*SS-GG)*V*V+M*M*GG)
    require(old == expanded, 'whole shifted output identity')
    return {'center_defect': True, 'lower_center_defect': True,
            'quotient_remainder':True,'quotient_center_defect':True,'whole_output': True}


def leading(g):
    # For a centered graph, restore the unshifted center in this auxiliary
    # top-form computation. The complete-output identity above then treats
    # the exact cancellation, instead of trusting an unreduced DAG bound.
    rows = []
    for r in g['source']:
        if g['polynomial_center'] and r[0] == 'center':
            rows.append(['degree_L','*','cTR','V'])
            rows.append(['degree_LB','*','degree_L','Bt'])
            rows.append(['center', '-', 'n', 'degree_LB'])
        else:
            rows.append(r)
    env = {x: (1, Poly.v(x)) for x in INPUTS}
    env.update({x: (0, Poly.v(x)) for x in PORTS})
    def arg(x):
        return (0, Poly(x)) if type(x) is int else env[x]
    for name, op, x, y in rows:
        dx, px = arg(x); dy, py = arg(y)
        if op == '*': d, pp = dx+dy, px*py
        elif dx > dy: d, pp = dx, px
        elif dy > dx: d, pp = dy, py if op == '+' else -py
        else: d, pp = dx, px+py if op == '+' else px-py
        require(bool(pp.d), 'unexpected top cancellation at ' + name)
        env[name] = (d, pp)
    q = Poly.v('beta')*Poly.v('J')
    k = Poly.v('eta')+Poly.v('zeta')
    w,s,i,T,F = map(Poly.v, ('w','s','i','T','F'))
    B = k*s*T-q*q*(q-F)
    if not g['polynomial_center']:
        degree, top = env['N']
        expected = -9*2**10*q**100*w**26*s**58*i**10*k**32*B**2
        require(degree == 232, 'uncentered exact degree')
        require(top == expected, 'uncentered full leading form')
        require(env['Znum'][0] == (21 if g['transport_weight'] == 'b2' else 57),
                'uncentered carrier degree')
    else:
        dQ,tQ=env['Q'];dM,tM=env['Mtot'];dC,tC=env['center_root']
        dV,tV=env['V'];dZ,tZ=env['Znum'];dG,tG=env['Dg'];dUE,tUE=env['UE']
        if g['center_parameter']=='quotient':
            dU,tU=env['U'];dE,tE=env['Dtau'];dY,tY=env['Y'];dk,tk=env['k']
            dS,tS=2*dU+dE+2*dk+4*dY,4*tU**2*tE*tk**2*tY**4
        elif g['center_parameter']=='A':
            dS,tS = 2*dUE,tUE**2
        else:
            dAm1,tAm1=env['Am1']
            dS,tS=dAm1+2*dUE,-2*tAm1*tUE**2
        bounds=[dQ+2*dZ,dQ+dM+dC+dV+dZ,
                2*dM+dQ+dS+2*dV,2*dM+dG+2*dV,2*dM+dG]
        degree={'quotient':220,'A':224,'Am1':228}[g['center_parameter']]
        require(bounds == [194,213,degree,152,72], 'centered summand degrees')
        top=tM**2*tQ*tS*tV**2
        if degree==220:expected=9*2**12*q**94*w**22*s**56*i**10*k**32*B**2
        elif degree==224:expected=9*2**10*q**96*w**24*s**56*i**10*k**32*B**2
        else:expected=-9*2**11*q**98*w**25*s**57*i**10*k**32*B**2
        require(top == expected, 'centered full leading component')
    require(g['exact_degree'] == degree, 'declared exact degree')
    return {'degree':degree,'leading_form':top.serial(),
            'uncentered_carrier_degree':env['Znum'][0],
            'nonvanishing_reason':'The displayed top form is a product of nonzero polynomials over the integers, with beta a fixed positive integer.'}


def parent_delta(g):
    parent_path=ROOT/g['parent']['path']
    require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==g['parent']['sha256'],
            'pinned parent hash')
    parent=json.loads(parent_path.read_text())
    restored=[]
    for name,op,x,y in g['source']:
        if name in ('A','center_root','center_bB','center_inner','center_product',
                    'Yp1','quotient_product','quotient_difference','quotient_E',
                    'upper_root','twice_upper','U_quotient','scaledG'): continue
        if name=='trace_f': restored.append(['Fsqr','+','fouraF0',1])
        elif name=='L': restored.append(['L','*','cTR','V'])
        elif name=='center':
            if g['polynomial_center']:
                restored.extend([['L','*','cTR','V'],['LBt','*','L','Bt']])
            restored.append(['center','-','n','LBt'])
        else: restored.append([name,op,'Fsqr' if x=='trace_f' else x,
                                      'Fsqr' if y=='trace_f' else 'Dg' if y=='scaledG' else y])
    require(restored==parent['source'], 'entire parent graph recovered')
    require(g['coefficient_binding']['ports']==parent['coefficient_binding']['ports'],
            'whole coefficient tuple preserved')
    return True


def coefficients(g):
    results=[]
    values={}
    for name,item in g['coefficient_binding']['ports'].items():
        data=(ROOT/g['coefficient_binding']['path']/item['file']).read_bytes()
        raw=gzip.decompress(data)
        require(hashlib.sha256(data).hexdigest()==item['gzip_sha256'],name+' gzip hash')
        require(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],name+' integer hash')
        n=int.from_bytes(raw,'little')
        require(n.bit_length()==item['bits'],name+' bits')
        values[name]=n;results.append({'port':name,'bits':n.bit_length(),'raw_sha256':item['raw_sha256']})
    require(values['beta']>=31 and values['beta']%2==1 and values['K0']>0, 'coefficient bounds')
    require(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'mask interval')
    return results


def corruption_controls(g):
    rejected=0
    for target in ('trace_f','center' if g['polynomial_center'] else 'L','eclear','Q','V','Znum','N'):
        for op in ('+','-','*'):
            bad=copy.deepcopy(g)
            row=next(r for r in bad['source'] if r[0]==target)
            if row[1]==op: continue
            row[1]=op
            try: cuts(bad)
            except (ValueError,KeyError): rejected+=1
            else: raise ValueError('undetected operator corruption '+target)
    if g['polynomial_center']:
        bad=copy.deepcopy(g)
        next(r for r in bad['source'] if r[0]=='center_root')[3]='U'
        try: cuts(bad)
        except (ValueError,KeyError): rejected+=1
        else: raise ValueError('undetected missing-E center corruption')
    return rejected


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path)
    ap.add_argument('--skip-coefficients',action='store_true',
                    help='Development-only mode; does not authenticate the fixed integers.')
    args=ap.parse_args()
    ledger=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
    for item in ledger['sources']:
        require(hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest()==item['sha256'],
                'source ledger: '+item['local'])
    trace=json.loads((ROOT/'parents/trace87.json').read_text())
    inverse=json.loads((ROOT/'parents/inverse85.json').read_text())
    for port in PORTS:
        require(trace['coefficient_binding']['ports'][port]['raw_sha256']==
                inverse['coefficient_binding']['ports'][port]['raw_sha256'],
                'both parent proofs bind the same fixed tuple')
    result={'identities':identities(),'source_files_authenticated':len(ledger['sources']),
            'coefficient_authentication':not args.skip_coefficients,'equations':[]}
    for path in sorted((ROOT/'equations').glob('*.json')):
        g=json.loads(path.read_text())
        item={'path':str(path.relative_to(ROOT)),'operations':g['operations'],
              'operation_classes':topology(g),'parent_delta':parent_delta(g),
              'cuts':cuts(g),'degree':leading(g),
              'rejected_operator_corruptions':corruption_controls(g)}
        if not args.skip_coefficients: item['fixed_integers']=coefficients(g)
        result['equations'].append(item)
    if args.receipt: args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'coefficient_authentication':not args.skip_coefficients,
                     'equations':[{'path':x['path'],'operations':x['operations'],
                                   'exact_degree':x['degree']['degree'],
                                   'cuts':len(x['cuts']),
                                   'rejected_corruptions':x['rejected_operator_corruptions']}
                                   for x in result['equations']]},indent=2))


if __name__=='__main__':main()
