#!/usr/bin/env python3
"""Construct/audit the 44-integer quartic. Python standard library only.

This proves finite algebra/degree/tuple checks, not the unbounded semantic
equivalence stated in PROOF44.md. All checks use explicit exceptions.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def require(cond, msg):
    if not cond:
        raise ValueError(msg)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def build_coefficients():
    tiles = json.loads((ROOT/'upstream/wang943_tiles.json').read_text())
    require(len(tiles) == 943, 'tile count')
    b, width, d = 121, 8801, 1064921
    require(b * width == d, 'native block exponent')
    rho = 1 << b
    B = 1 << d
    weights = [1 << (10 + 2*j) for j in range(44)]
    offsets = [1020,1000,980,960]
    coefficients = {}
    for j, tile in enumerate(tiles):
        require(len(tile) == 4 and all(0 <= x < 512 for x in tile), 'tile labels')
        value = 1 + sum(weights[40:44])
        for t, x in enumerate(tile):
            value += sum(weights[10*t+k] for k in range(10) if ((x+512)>>k)&1)
        coefficients[j] = value
    for t, offset in enumerate(offsets):
        for j in range(10):
            coefficients[offset+2*j] = weights[10*t+j]
    for e,j in zip([1095,1096,2195,3296],range(40,44)):
        coefficients[e] = weights[j]
    coefficients[1063] = coefficients[1064] = 0
    require(len(coefficients) == 989, 'native basis size')
    DC = sum(1 << (b*e) for e in [40,41,1100,2200])
    for e,c in coefficients.items():
        DC += c * ((1 << (b*(4393-e))) + (1 << (b*(5495-e))))
    DR = rho
    beta = B-1
    MC = beta - sum(1 << (b*e) for e in coefficients if e != 1) - (2 << (b*1063))
    mu = 1022 + sum(weights)
    Z = ((1<<119)-1) * sum(1 << (b*e) for e in range(8792,8799))
    Z += ((1<<27)-1) << (b*8799)
    MF_native = 4 + mu*((1 << (b*4393)) + (1 << (b*5495)))
    MF_native += sum((1 << (b*(1000+2*j))) + (1 << (b*(1021+2*j))) for j in range(10))
    MF_native += (1 << (b*2195)) + (1 << (b*3296)) + Z
    values = dict(beta=beta, K=DC+B*DR, MC=MC, MF_source=MF_native+beta)
    manifest = json.loads((ROOT/'upstream/PAYLOAD_BINDING.json').read_text())
    facts = {}
    for name,value in values.items():
        raw = value.to_bytes((value.bit_length()+7)//8, 'little')
        expected = manifest['payloads'][name]
        require(value.bit_length() == expected['bits'], name+' bits')
        require(len(raw) == expected['bytes'], name+' bytes')
        require(digest(raw) == expected['sha256'], name+' exact numeral SHA256')
        payload = gzip.compress(raw, mtime=0)
        (ROOT/'coefficients'/(name+'.bin.gz')).write_bytes(payload)
        facts[name] = dict(bits=value.bit_length(), bytes=len(raw), sha256=digest(raw))
    require(0 < MC < beta, 'low mask bound')
    require(0 < MF_native < beta, 'native high mask bound')
    require(beta < values['MF_source'] < 2*beta, 'shifted high mask bound')
    require(values['K'] >= 0, 'transport constant sign')
    require(MC % 4 == 2 and MF_native % 8 == 4, 'native mask parity')
    require(MC.bit_count()+MF_native.bit_count() == d, 'native mask population')
    facts['new_proof_hypotheses'] = dict(d=d, d_at_least_3=d>=3, beta_at_least_17=beta>=17,
        low_mask_strictly_between_zero_and_beta=True,
        shifted_high_mask_strictly_between_beta_and_two_beta=True,
        K_nonnegative=True)
    return values, facts

class Poly:
    """Sparse exact multivariate polynomial; ports counted separately later."""
    def __init__(self, variables):
        self.variables=variables
        self.n=len(variables)
        self.zero=(0,)*self.n
        self.index={v:i for i,v in enumerate(variables)}
    def add(self,a,b,sign=1):
        out=dict(a)
        for k,v in b.items():
            out[k]=out.get(k,0)+sign*v
            if not out[k]: del out[k]
        return out
    def mul(self,a,b):
        out={}
        for x,c in a.items():
            for y,d in b.items():
                k=tuple(u+v for u,v in zip(x,y))
                out[k]=out.get(k,0)+c*d
                if not out[k]: del out[k]
        return out
    def power(self,a,e):
        out={self.zero:1}
        for _ in range(e): out=self.mul(out,a)
        return out
    def parse(self,text):
        def rec(node):
            if isinstance(node,ast.Constant) and isinstance(node.value,int):
                return {} if node.value==0 else {self.zero:node.value}
            if isinstance(node,ast.Name):
                k=list(self.zero); k[self.index[node.id]]=1
                return {tuple(k):1}
            if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
                return {k:-v for k,v in rec(node.operand).items()}
            if isinstance(node,ast.BinOp):
                if isinstance(node.op,ast.Add): return self.add(rec(node.left),rec(node.right))
                if isinstance(node.op,ast.Sub): return self.add(rec(node.left),rec(node.right),-1)
                if isinstance(node.op,ast.Mult): return self.mul(rec(node.left),rec(node.right))
                if isinstance(node.op,ast.Pow):
                    require(isinstance(node.right,ast.Constant) and isinstance(node.right.value,int)
                            and 0<=node.right.value<=8,'fixed exponent')
                    return self.power(rec(node.left),node.right.value)
            raise ValueError('unrecognized polynomial AST: '+ast.dump(node))
        return rec(ast.parse(text,mode='eval').body)

def build_candidate():
    source_raw=(ROOT/'upstream/quartic45.json').read_bytes()
    source=json.loads(source_raw)
    require(source['variable_count']==45 and source['equation_count']==28,'source counts')
    variables=[x for x in source['variables'] if x!='q_half_root']
    require(len(variables)==44,'new count')
    residuals=list(source['residuals'])
    require(residuals[22]=='-u**2 + w','old square-w row')
    residuals[22]='X - 2*u**2'
    require(residuals[25]=='beta*J+1-2*q_half_root**2','old dyadic-q row')
    del residuals[25]
    require(len(residuals)==27,'new row count')
    out=dict(name='quartic44_global_power_scale', domain='unrestricted integers',
        variables=variables,variable_count=len(variables),equation_count=len(residuals),
        fixed_numerals=['beta','K0','MC','MF'],residuals=residuals,
        single_polynomial='sum of squares of the 27 listed residuals', exact_degree=4,
        coefficient_binding=dict(backend='mixed-parity-unrounded-1064921',
            inherited_manifest='upstream/PAYLOAD_BINDING.json',
            ports={'beta':'coefficients/beta.bin.gz','K0':'coefficients/K.bin.gz',
                   'MC':'coefficients/MC.bin.gz','MF':'coefficients/MF_source.bin.gz'},
            format='gzip of minimal unsigned little-endian integer bytes',
            mask_convention='MF is already shifted by beta'),
        parent_sha256=digest(source_raw), source_pin='beb0192cb8dc36f78c369c080f2adfbc1887a486',
        proof='PROOF44.md', status='Ordinary mathematical proof using named inherited compiler/Pell dependencies; not a new kernel certificate')
    write_json(ROOT/'quartic44.json',out)
    return source,out

def audit(source,out):
    variables=out['variables']
    algebra=Poly(variables+out['fixed_numerals'])
    polynomials=[algebra.parse(row) for row in out['residuals']]
    n=len(variables)
    degrees=[max((sum(k[:n]) for k in p),default=0) for p in polynomials]
    require(degrees==[2]*27,'each residual quadratic')
    live={variables[i] for p in polynomials for k in p for i in range(n) if k[i]}
    require(live==set(variables),'all 44 unknowns live')
    sos={}
    for p in polynomials: sos=algebra.add(sos,algebra.mul(p,p))
    require(max(sum(k[:n]) for k in sos)==4,'quartic degree')
    key=list(algebra.zero); key[algebra.index['tau']]=4
    require(sos.get(tuple(key),0)==1,'literal coefficient of tau^4')
    # The packed R residual independently matches k-1-hE-R, on L=q²-1,N=q³.
    q='(beta*J+1)'
    R=f'(({q}-1)*({q}-F)+alpha)*L+(MC+{q}*MF)*J'
    direct=algebra.parse('eta+zeta-1-h*E-('+R+')')
    row=polynomials[12]
    relation=algebra.parse('N-('+q+')*(L+1)')
    # The source row used cubic-free packing (q-F)(N-q)-C L.
    require(algebra.add(row,direct,-1)==algebra.mul(algebra.parse('F-'+q),relation),
        'packing row ideal identity')
    # Literal transport row is (K+w)C-z(q-1)-F; inherited prose had z-1.
    transport=algebra.parse('(K0+w)*('+q+'-F-alpha)-z*('+q+'-1)-F')
    require(polynomials[13]==transport,'transport identity')
    # Boundary/bounds diagnostics: universal proofs are in PROOF44.md.
    bounds=0
    for Q in range(16,71):
        for F in range(1,Q-1):
            for C in range(1,Q-F):
                Gpos=Q*(Q-F)-C
                Gneg=Q*(Q-F)+C
                require(Gpos>=Q+2 and Gpos<=Q*Q-Q-1,'positive G bounds')
                require(Gneg>=2*Q+1 and Gneg<=Q*Q-2,'negative G bounds')
                require(Gpos*(Q*Q-1)>Q*(Q*Q-1),'positive R lower')
                require(Gneg*(Q*Q-1)>Q*(Q*Q-1),'negative R lower')
                require(Gpos*(Q*Q-1)+(2*Q+1)*(Q-1)<Q**4-2,'positive R upper')
                require(Gneg*(Q*Q-1)+2*Q*(Q+1)<Q**4-2,'negative R upper')
                bounds+=2
    dyadic=0
    for d in range(3,101):
        M=(1<<d)-1
        for r in range(d):
            require((1<<r)!=M-1,'negative dyadic residue excluded')
            require(pow(2,r,M)==(1<<r),'positive dyadic remainder')
            dyadic+=1
    return dict(variable_count=n,residual_count=len(polynomials),residual_degrees=degrees,
        exact_single_polynomial_degree=4,tau_fourth_coefficient=1,
        expanded_monomials_with_symbolic_ports=len(sos),
        all_variables_live=True,packing_identity=True,transport_identity=True,
        finite_bound_cases=bounds,finite_dyadic_cases=dyadic,
        semantic_proof='PROOF44.md; finite checks do not replace universal Pell/compiler results')

def main():
    (ROOT/'coefficients').mkdir(exist_ok=True)
    (ROOT/'certificates').mkdir(exist_ok=True)
    source_pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for record in source_pins:
        raw=(ROOT/record['file']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob==record['git_blob'], 'source Git blob: '+record['file'])
    _,coefficients=build_coefficients()
    source,out=build_candidate()
    checks=audit(source,out)
    write_json(ROOT/'certificates/COEFFICIENT_CHECKS.json',coefficients)
    write_json(ROOT/'certificates/QUARTIC44_CHECKS.json',checks)
    print(json.dumps(checks,indent=2))

if __name__=='__main__':
    main()
