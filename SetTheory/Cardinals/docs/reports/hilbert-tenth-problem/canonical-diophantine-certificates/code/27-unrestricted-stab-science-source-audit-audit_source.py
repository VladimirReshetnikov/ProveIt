#!/usr/bin/env python3
"""Independent, exact source-to-equations audit. Standard library only.
Does not import or execute the builder or any other checker. It treats input
files as inert data. Explicit checks remain effective under Python -O.
"""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path


def require(condition, description):
    if not condition:
        raise ValueError(description)


class Polynomial:
    def __init__(self, value=0):
        self.terms = value if isinstance(value, dict) else ({():value} if value else {})
    @staticmethod
    def coerce(value):
        return value if isinstance(value, Polynomial) else Polynomial(value)
    def __add__(self, value):
        other = self.coerce(value)
        result = self.terms.copy()
        for monomial, coefficient in other.terms.items():
            result[monomial] = result.get(monomial, 0) + coefficient
            if not result[monomial]: del result[monomial]
        return Polynomial(result)
    __radd__ = __add__
    def __neg__(self): return Polynomial({m:-c for m,c in self.terms.items()})
    def __sub__(self, value): return self + -self.coerce(value)
    def __rsub__(self, value): return self.coerce(value) + -self
    def __mul__(self, value):
        other = self.coerce(value)
        result = {}
        for m,c in self.terms.items():
            for n,d in other.terms.items():
                key = tuple(sorted(m+n))
                result[key] = result.get(key, 0) + c*d
        return Polynomial({m:c for m,c in result.items() if c})
    __rmul__ = __mul__
    def __eq__(self, other): return self.terms == self.coerce(other).terms
    def degree(self): return max((len(m) for m in self.terms), default=-1)


def audit(path, builder_path):
    encoded = path.read_bytes()
    dag = json.loads(encoded)
    canonical = (json.dumps(dag, sort_keys=True, separators=(',',':'))+'\n').encode()
    require(encoded == canonical, 'canonical DAG bytes')
    require(dag['schema'] == 'fixed-positive-integer-polynomial-dag-v1', 'schema')
    require(dag['input'] == 'InputPlus', 'single ordinary input')
    names = dag['witnesses']
    require(len(names) == len(set(names)), 'distinct witness names')
    require(all(isinstance(s, str) and s for s in names), 'named witnesses')
    symbols = ['InputPlus'] + names
    symbol_ids = {name:i for i,name in enumerate(symbols)}
    def variable(name):
        require(name in symbol_ids, 'unknown variable '+name)
        return Polynomial({(symbol_ids[name],):1})
    def natural(name): return variable(name+'.Plus')-1
    values = {'input:InputPlus':variable('InputPlus')}
    values.update({'witness:'+name:variable(name) for name in names})
    upper_degrees = {name:1 for name in values}
    def resolve(ref):
        require(isinstance(ref,str), 'string reference')
        if ref.startswith('constant:'):
            number = int(ref[9:])
            require(str(number) == ref[9:], 'canonical integer literal')
            return Polynomial(number)
        require(ref in values, 'valid acyclic reference '+ref)
        return values[ref]
    def upper(ref):
        return 0 if ref.startswith('constant:') else upper_degrees[ref]
    body = dag['body_gate_count']
    require(type(body) is int and 0 < body < len(dag['gates']), 'valid body length')
    # Normalize body gates only. The complete final polynomial is evaluated by
    # exact univariate arithmetic below; its SOS shape is checked structurally.
    for index,(operator,left,right) in enumerate(dag['gates']):
        require(operator in ('+','-','*'), 'polynomial gate whitelist')
        a,b = resolve(left),resolve(right)
        upper_degrees['gate:'+str(index)] = (upper(left)+upper(right) if operator=='*'
                                              else max(upper(left),upper(right)))
        if index < body:
            value = a+b if operator=='+' else a-b if operator=='-' else a*b
        else:
            # Placeholder values suffice for reference topology after body.
            value = Polynomial()
        values['gate:'+str(index)] = value
    eqs = {}
    for left,right,name in dag['equalities']:
        require(name not in eqs, 'distinct equality '+name)
        require(not left.startswith('gate:') or int(left[5:]) < body, 'equality inside body')
        require(not right.startswith('gate:') or int(right[5:]) < body, 'equality inside body')
        eqs[name] = resolve(left)-resolve(right)
    macros = {}
    for macro in dag['macros']:
        name = macro['name']
        require(name not in macros, 'distinct macro '+name)
        macros[name] = macro
    checked_eqs, checked_macros, used_variables = set(),set(),set()
    def v(name):
        used_variables.add(name)
        return variable(name)
    def n(name): return v(name+'.Plus')-1
    def check_eq(name,left,right):
        require(name not in checked_eqs, 'expected equality duplicate '+name)
        require(name in eqs, 'missing equality '+name)
        require(eqs[name] == left-right, 'exact residual mismatch '+name)
        checked_eqs.add(name)
    def check_macro(kind,name,**ports):
        require(name not in checked_macros, 'expected macro duplicate '+name)
        require(name in macros, 'missing macro '+name)
        actual = macros[name]
        require(set(actual) == {'kind','name'} | set(ports), 'macro keys '+name)
        require(actual['kind'] == kind, 'macro kind '+name)
        for key,value in ports.items():
            require(resolve(actual[key]) == value, 'macro port '+name+'.'+key)
        checked_macros.add(name)

    def power(base,exponent,name):
        """Independent transcription of the 15 integer Pell constraints."""
        z = v(name+'.out')
        a = v(name+'.aMinus1')+1
        beta = v(name+'.betaMinus1')+1
        w,M,g,x,y,u,vv,s,t,qb,qv,strict = [v(name+'.'+k) for k in
            ('w','M','g','x','y','u','v','s','t','qb','qv','strict')]
        delta_b,delta_k,delta_y,alpha1,alpha2,sigma1,sigma2,tau1,tau2,rho1,rho2 = [n(name+'.'+k) for k in
            ('dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2')]
        k = exponent+1
        equations = [
            (x*x-1,(a*a-1)*y*y),
            (u*u-1,(a*a-1)*vv*vv),
            (s*s-1,(beta*beta-1)*t*t),
            (beta-1,4*y*qb),
            (beta-a,u*(alpha2-alpha1)),
            (vv,y*y*qv),
            (s-x,u*(sigma2-sigma1)),
            (t-k,4*y*(tau2-tau1)),
            (y-k,delta_y),
            (w-base,delta_b),
            (w-k,delta_k),
            (M-base*z,strict),
            (a*a-1,((w+1)*(w+1)-1)*w*w*g*g),
            (2*a*base-base*base-1,M),
            (x-y*(a-base)-base*z,M*(rho2-rho1)),
        ]
        for index,(left,right) in enumerate(equations,1):
            check_eq(name+'.eq'+str(index),left,right)
        check_macro('power',name,base=base,exponent=exponent,out=z)
        return z

    def subset(mask,value,name):
        radix = power(2,mask+1,name+'.radix')
        place = power(radix,value,name+'.position')
        expansion = power(radix+1,mask,name+'.expansion')
        quotient,half,remainder = [n(name+'.'+key) for key in ('quotient','half','remainder')]
        digit_slack,remainder_slack = [v(name+'.'+key) for key in ('digitSlack','remainderSlack')]
        check_eq(name+'.extract',expansion-quotient*radix*place,(2*half+1)*place+remainder)
        check_eq(name+'.digitBound',2*half+1+digit_slack,radix)
        check_eq(name+'.remainderBound',remainder+remainder_slack,place)
        check_macro('subset',name,mask=mask,value=value)

    def conjunction(left,right,name):
        common,a,c = [n(name+'.'+key) for key in ('common','leftOnly','rightOnly')]
        check_eq(name+'.partitionLeft',left,common+a)
        check_eq(name+'.partitionRight',right,common+c)
        subset(left,common,name+'.left')
        subset(right,common,name+'.right')
        subset(a+c,a,name+'.disjoint')
        check_macro('and',name,left=left,right=right,out=common)
        return common

    def geometric(base,length,name):
        end = power(base,length,name+'.power')
        out = n(name+'.value')
        check_eq(name+'.geometric',base*out-out+1,end)
        check_macro('geometric',name,base=base,length=length,out=out)
        return out

    def spread(value,base,length,stride,name):
        gap = n(name+'.strideGap')
        slack = v(name+'.rangeSlack')
        check_eq(name+'.strideBound',stride-length-1,gap)
        limit = power(base,length,name+'.range')
        check_eq(name+'.rangeBound',value+slack,limit)
        copybase = power(base,stride-1,name+'.copyBase')
        end = power(copybase,length,name+'.copyEnd')
        copying,masking = n(name+'.copying'),n(name+'.masking')
        check_eq(name+'.copyGeom',copybase*copying-copying+1,end)
        check_eq(name+'.maskGeom',base*copybase*masking-masking+1,end*limit)
        out = conjunction(value*copying,base*masking-masking,name+'.select')
        check_macro('spread',name,value=value,base=base,length=length,stride=stride,out=out)
        return out

    def stable(mask,name,stream=None):
        low,mid,high = [n(name+'.bit'+str(j)) for j in range(3)]
        for j,plane in enumerate((low,mid,high)): subset(mask,plane,name+'.allow'+str(j))
        subset(mask,mid+high,name+'.exclude67')
        result = low+mid+mid+4*high
        if stream is not None: check_eq(name+'.reconstruct',stream,result)
        check_macro('stable',name,mask=mask,out=result)
        return result

    p,q,r,d,e,f = [v('descriptor.'+key) for key in ('p','q','r','d','e','f')]
    tile,patch = n('descriptor.tile'),n('descriptor.patch')
    fields = [p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]
    suffix = patch
    for j in reversed(range(7)):
        code = v('InputPlus')-1 if j == 0 else n('descriptor.pair'+str(j))
        total = fields[j]+suffix
        check_eq('descriptor.cantor'+str(j),2*code,total*total+total+2*suffix)
        suffix = code
    tile_volume,patch_volume = p*q*r,d*e*f
    tile_mask = geometric(32,tile_volume,'tile.externalMask')
    stable(tile_mask,'tile.externalDigits',tile)
    patch_mask = geometric(32,patch_volume,'patch.externalMask')
    subset(15*patch_mask,patch,'patch.externalDigits')
    precision = v('radix.precision')
    base = power(32,precision,'radix.base')
    sixteenth = v('radix.sixteenth')
    check_eq('radix.sixteenthEquation',16*sixteenth,base)
    wide_tile = spread(tile,32,tile_volume,precision,'tile.convert')
    wide_patch = spread(patch,32,patch_volume,precision,'patch.convert')
    tx,ty,tz = [v('box.t'+axis)+1 for axis in 'xyz']
    hx,hy,hz = p*d*tx,q*e*ty,r*f*tz
    A,B,C = 2*hx,2*hy,2*hz
    tile_step_x,tile_step_y,tile_step_z = 2*d*tx,2*e*ty,2*f*tz
    patch_step_x,patch_step_y = 2*p*tx,2*q*ty
    tile_row_base = power(base,p,'tile.rowBase')
    tile_rows = spread(wide_tile,tile_row_base,q*r,tile_step_x,'tile.rows')
    tile_plane_base = power(base,A*q,'tile.planeBase')
    tile_embedded = spread(tile_rows,tile_plane_base,r,tile_step_y,'tile.planes')
    repeat_x = geometric(tile_row_base,tile_step_x,'tile.repeatX')
    repeat_y = geometric(tile_plane_base,tile_step_y,'tile.repeatY')
    tile_z_base = power(base,A*B*r,'tile.zBase')
    repeat_z = geometric(tile_z_base,tile_step_z,'tile.repeatZ')
    background = tile_embedded*repeat_x*repeat_y*repeat_z
    patch_row_base = power(base,d,'patch.rowBase')
    patch_rows = spread(wide_patch,patch_row_base,e*f,patch_step_x,'patch.rows')
    patch_plane_base = power(base,A*e,'patch.planeBase')
    patch_embedded = spread(patch_rows,patch_plane_base,f,patch_step_y,'patch.planes')
    patch_shift = power(base,hx+A*hy+A*B*hz,'patch.shift')
    additions = patch_embedded*patch_shift
    X = power(base,A,'box.X')
    Y = power(X,B,'box.Y')
    Q = power(Y,C,'box.Q')
    J = n('box.J')
    check_eq('box.JEquation',base*J-J+1,Q)
    jx,jy,jz = [n('box.j'+axis) for axis in 'xyz']
    check_eq('box.jxEquation',base*base*((base-1)*jx+1),X)
    check_eq('box.jyEquation',X*X*((X-1)*jy+1),Y)
    check_eq('box.jzEquation',Y*Y*((Y-1)*jz+1),Q)
    interior = base*X*Y*jx*jy*jz
    capacity = sixteenth-1
    U = n('supersolution.U')
    subset(capacity*interior,U,'supersolution.support')
    nx,ny,nz = [n('supersolution.negative'+axis) for axis in 'xyz']
    check_eq('supersolution.divX',base*nx,U)
    check_eq('supersolution.divY',X*ny,U)
    check_eq('supersolution.divZ',Y*nz,U)
    endpoint = stable(J,'endpoint')
    balance_left = background+additions+(base+X+Y)*U+nx+ny+nz
    balance_right = 6*U+endpoint
    check_eq('sandpile.balance',balance_left,balance_right)
    ports = dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=tile,patch=patch,
        tile_size=tile_volume,patch_size=patch_volume,precision=precision,
        radix=base,sixteenth=sixteenth,capacity=capacity,tile_converted=wide_tile,
        patch_converted=wide_patch,half_x=hx,half_y=hy,half_z=hz,A=A,B=B,C=C,
        X=X,Y=Y,Q=Q,background=background,additions=additions,all_slots=J,
        interior_mask=interior,supersolution=U,endpoint=endpoint,
        balance_left=balance_left,balance_right=balance_right)
    require(set(ports) == set(dag['ports']), 'complete port inventory')
    for key,polynomial in ports.items(): require(resolve(dag['ports'][key]) == polynomial, 'port '+key)
    require(checked_eqs == set(eqs), 'all equalities audited')
    require(checked_macros == set(macros), 'all macros audited')
    require(used_variables == set(symbols), 'all variables independently reconstructed')

    gates = dag['gates']
    next_gate = body
    squares = []
    for left,right,name in dag['equalities']:
        require(gates[next_gate] == ['-',left,right], 'SOS residual '+name)
        residual = 'gate:'+str(next_gate)
        require(gates[next_gate+1] == ['*',residual,residual], 'SOS square '+name)
        squares.append('gate:'+str(next_gate+1))
        next_gate += 2
    running = squares[0]
    for square in squares[1:]:
        require(gates[next_gate] == ['+',running,square], 'SOS sum shape')
        running = 'gate:'+str(next_gate)
        next_gate += 1
    require(next_gate == len(gates) and running == dag['output'], 'complete SOS and output')
    live,pending = set(),[dag['output']]
    while pending:
        reference = pending.pop()
        if reference in live: continue
        live.add(reference)
        if reference.startswith('gate:'): pending.extend(gates[int(reference[5:])][1:])
    require(all('gate:'+str(i) in live for i in range(len(gates))), 'all gates live')
    require(all('witness:'+name in live for name in names), 'all witnesses live')
    require('input:InputPlus' in live, 'input live')

    # Exact degree lower bound: preserve nine variables as a common formal t;
    # all other variables, including input, specialize to zero. These values
    # need not lie in the positive domain for this algebraic identity test.
    selected = ['descriptor.'+axis for axis in ('p','q','r','d','e','f')] + ['box.t'+axis for axis in 'xyz']
    uni = {'input:InputPlus':Polynomial()}
    uni.update({'witness:'+name:(Polynomial({(0,):1}) if name in selected else Polynomial()) for name in names})
    def ur(ref): return Polynomial(int(ref[9:])) if ref.startswith('constant:') else uni[ref]
    for index,(operator,left,right) in enumerate(gates):
        a,b = ur(left),ur(right)
        uni['gate:'+str(index)] = a+b if operator=='+' else a-b if operator=='-' else a*b
    polynomial = uni[dag['output']]
    degree = polynomial.degree()
    require(upper_degrees[dag['output']] == degree == 18, 'exact degree eighteen')
    residual_max = max(residual.degree() for residual in eqs.values())
    require(residual_max == 9, 'maximum exact residual degree')
    maximal = {name:len(residual.terms) for name,residual in eqs.items() if residual.degree()==9}
    top_parts = {name:[{'coefficient':coefficient,'variables':[symbols[i] for i in monomial]}
                       for monomial,coefficient in residual.terms.items() if len(monomial)==9]
                 for name,residual in eqs.items() if residual.degree()==9}
    expected_top = tuple(sorted(symbol_ids[name] for name in selected))
    require(set(top_parts) == {'patch.shift.eq8','patch.shift.eq9','patch.shift.eq11'}, 'precise maximal residual inventory')
    require(all({m:c for m,c in eqs[name].terms.items() if len(m)==9} == {expected_top:-4} for name in top_parts), 'exact degree-nine leading forms')
    # At least one nonzero degree-nine residual also proves the lower bound,
    # because a sum of squares of real homogeneous forms cannot cancel.
    require(bool(maximal), 'degree-nine residual exists')
    tree = ast.parse(builder_path.read_text())
    imports = sorted({node.module if isinstance(node,ast.ImportFrom) else item.name
                      for node in ast.walk(tree) if isinstance(node,(ast.Import,ast.ImportFrom))
                      for item in (node.names if isinstance(node,ast.Import) else [None])})
    require(imports == ['argparse','collections','hashlib','json','pathlib'], 'builder imports only expected standard library')
    construction_nodes = [node for node in tree.body if isinstance(node,(ast.ClassDef,ast.FunctionDef)) and node.name in ('Expr','Source','construct')]
    require(not any(isinstance(node,ast.BinOp) and isinstance(node.op,(ast.Pow,ast.Div,ast.FloorDiv,ast.Mod,ast.LShift,ast.RShift,ast.BitAnd,ast.BitOr,ast.BitXor)) for root in construction_nodes for node in ast.walk(root)), 'no unpaid arithmetic operators in construction')
    forbidden = {'eval','exec','compile','__import__','pow'}
    require(not any(isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id in forbidden for node in ast.walk(tree)), 'no dynamic execution or hidden power')
    receipt = {
        'status':'PASS', 'dag_sha256':hashlib.sha256(encoded).hexdigest(),
        'builder_sha256':hashlib.sha256(builder_path.read_bytes()).hexdigest(),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'checked_equalities_exact_sparse':len(checked_eqs),
        'checked_macro_calls_exact_sparse':len(checked_macros),
        'checked_ports_exact_sparse':len(ports), 'positive_witnesses':len(names),
        'macro_inventory':dict(sorted(Counter(m['kind'] for m in macros.values()).items())),
        'body_gates':body, 'body_counts':dict(sorted(Counter(g[0] for g in gates[:body]).items())),
        'sos_gates':len(gates)-body, 'sos_counts':dict(sorted(Counter(g[0] for g in gates[body:]).items())),
        'gates':len(gates), 'full_counts':dict(sorted(Counter(g[0] for g in gates).items())),
        'dead_gates':0, 'dead_witnesses':0, 'input_live':True,
        'max_exact_residual_degree':residual_max,'degree_nine_residuals':maximal,
        'degree_nine_homogeneous_parts':top_parts,
        'degree_eighteen_homogeneous_part':{'coefficient':48,'variables':[symbols[i] for i in expected_top+expected_top]},
        'degree_upper_bound':upper_degrees[dag['output']], 'exact_degree':degree,
        'specialization_variables':selected,
        'specialized_output_coefficients':{str(len(m)):c for m,c in sorted(polynomial.terms.items(),key=lambda term:len(term[0]))},
        'builder_imports':imports,
        'dependency_note':'Pell theorem, bit-mask semantics, geometry, and least action require mathematical proofs. Exact symbolic equation matching and degree are unconditional finite algebra checks.'
    }
    return receipt


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dag', type=Path, required=True)
    parser.add_argument('--builder', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    receipt = audit(args.dag,args.builder)
    text = json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    args.receipt.write_text(text)
    print(text,end='')


if __name__ == '__main__': main()
