#!/usr/bin/env python3
"""Construct and independently check the 42-integer quartic.

Python 3 standard library only. This program checks finite polynomial data;
the unbounded solvability theorem is proved in the accompanying manuscript.
"""
from __future__ import annotations

import argparse
import ast
import collections
import gzip
import hashlib
import itertools
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
VARS = [
    'J','F','alpha','z','f','h','r','v_scale','w','tau','eta','zeta',
    'y','gamma','o','j','N','E','P','c','a','X','D','C2','L','F2',
    'V','g','I','Baux','Delta','u','q_half_root',
    'FA_pos1','FA_pos2','FA_pos3','FC_pos1','FC_pos2','FC_pos3',
    'EZ_pos1','EZ_pos2','EZ_pos3',
]
PORTS = ['beta','K0','MC','MF']
AFFINE = {
    'q':'beta*J+1', 'k':'eta+zeta', 'C':'q-F-alpha',
    'H':'4*a+3', 's':'2*v_scale+1', 'i':'2*r+1',
}
ROWS = [
    'L-q**2+1',
    'N-q*(L+1)',
    'X-q*w',
    'a-E-s*N',
    'E-X*(a-E)',
    'c-k*(a-E)-eta',
    'P-E*(c-eta)-k',
    'tau**2-P*(P-k)-1',
    'D-X-a*c-gamma*H',
    'Delta-a**2-H',
    'C2-c**2',
    'D**2-Delta*C2-1',
    'k-1-h*E-((q-F)*(N-q)-C*L+(MC+q*MF)*J)',
    '(K0+w)*C-F-z*(q-1)',
    'F2-f**2',
    'V+c-f*o',
    'V-c*j+k-1-h*E',
    'g+V**2-y**2',
    'I-i*C2',
    'Baux-I**2',
    'Baux-Delta*(F2-1)',
    'y**2-Baux*g-1',
    'w-4*u**2',
    'q-2*q_half_root**2',
    'F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)',
    'F*C-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)',
    'eta*zeta-1-EZ_pos1**2-EZ_pos2**2-EZ_pos3*(EZ_pos3+1)',
]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

class Ring:
    """Exact sparse polynomials; the fixed ports remain symbolic."""
    def __init__(self, names):
        self.names = names
        self.index = {n:i for i,n in enumerate(names)}
        self.zero = (0,)*len(names)
        self.aliases = {}

    def const(self, n):
        return {self.zero:n} if n else {}

    def add(self, a, b):
        out = dict(a)
        for m,c in b.items():
            out[m] = out.get(m,0)+c
            if not out[m]: del out[m]
        return out

    def neg(self, a):
        return {m:-c for m,c in a.items()}

    def mul(self, a, b):
        out = {}
        for u,c in a.items():
            for v,d in b.items():
                e = tuple(x+y for x,y in zip(u,v))
                out[e] = out.get(e,0)+c*d
        return {m:c for m,c in out.items() if c}

    def power(self, a, n):
        require(type(n) is int and n>=0, 'invalid exponent')
        out = self.const(1)
        for _ in range(n): out = self.mul(out,a)
        return out

    def parse(self, text):
        return self.node(ast.parse(text,mode='eval').body)

    def node(self, n):
        if isinstance(n,ast.Constant) and type(n.value) is int:
            return self.const(n.value)
        if isinstance(n,ast.Name):
            if n.id in self.aliases: return self.aliases[n.id]
            e = list(self.zero); e[self.index[n.id]]=1
            return {tuple(e):1}
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
            return self.neg(self.node(n.operand))
        if isinstance(n,ast.BinOp):
            a=self.node(n.left)
            if isinstance(n.op,ast.Pow):
                require(isinstance(n.right,ast.Constant),'nonliteral exponent')
                return self.power(a,n.right.value)
            b=self.node(n.right)
            if isinstance(n.op,ast.Add): return self.add(a,b)
            if isinstance(n.op,ast.Sub): return self.add(a,self.neg(b))
            if isinstance(n.op,ast.Mult): return self.mul(a,b)
        raise ValueError('unsupported syntax: '+ast.dump(n))

    def evaluate(self, a, values, modulus=None):
        total=0
        for m,c in a.items():
            t=c
            for name,e in zip(self.names,m):
                if e:
                    t *= pow(values[name],e,modulus) if modulus else values[name]**e
                    if modulus: t %= modulus
            total += t
            if modulus: total %= modulus
        return total

def literal_eval(text, values, modulus=None):
    """Separate scalar AST evaluator, independent of sparse multiplication."""
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int: v=n.value
        elif isinstance(n,ast.Name): v=values[n.id]
        elif isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub): v=-go(n.operand)
        elif isinstance(n,ast.BinOp):
            a=go(n.left)
            if isinstance(n.op,ast.Pow):
                require(isinstance(n.right,ast.Constant),'bad power')
                v=pow(a,n.right.value,modulus) if modulus else a**n.right.value
            else:
                b=go(n.right)
                if isinstance(n.op,ast.Add):v=a+b
                elif isinstance(n.op,ast.Sub):v=a-b
                elif isinstance(n.op,ast.Mult):v=a*b
                else:raise ValueError('bad scalar operation')
        else:raise ValueError('bad scalar syntax')
        return v%modulus if modulus else v
    return go(ast.parse(text,mode='eval').body)

def fixed_values():
    p=ROOT/'coefficients/payloads'
    manifest=json.loads((p/'COEFFICIENT_BINDING.json').read_text())
    out={}
    for alias,name in zip(PORTS,['beta','K','MC','MF_source']):
        raw=(p/(name+'.bin')).read_bytes()
        gz=(p/(name+'.bin.gz')).read_bytes()
        entry=manifest['payloads'][name]
        require(digest(raw)==entry['sha256'],'raw coefficient hash: '+name)
        require(digest(gz)==entry['gzip_sha256'],'compressed coefficient hash: '+name)
        require(gzip.decompress(gz)==raw,'coefficient decompression: '+name)
        out[alias]=int.from_bytes(raw,'little')
        require(out[alias].bit_length()==entry['bits'],'coefficient bit length')
    require(out['beta']==(1<<1064921)-1,'whole tuple identity')
    require(0<out['MC']<out['beta'],'MC range')
    require(out['beta']<out['MF']<2*out['beta'],'shifted MF range')
    return out

def pos(a,b,t):
    return 1+a*a+b*b+t*(t+1)

def check_guard_diagnostics():
    # Supplementary finite checks of the new universal inequalities.
    count=0
    for eta,zeta,Y in itertools.product(range(-7,8),range(-7,8),[-20,-4,4,20]):
        if eta*zeta<=0:continue
        K=abs(eta)+abs(zeta); c=(eta+zeta)*Y+eta; Z=abs(Y)
        if Y>0:require(K*Z<abs(c)<K*(Z+1),'positive-Y interval')
        else:require(K*(Z-1)<abs(c)<K*Z,'negative-Y interval')
        count+=1
    # A negative index residue is larger than R when M>3R+1.
    residue_cases=0
    for R in range(1,80):
        for M in range(3*R+2,3*R+12):
            for n in range(1,2*M):
                if (-2*n-R-1)%M==0:
                    require(n>R,'negative sign index separation')
                    residue_cases+=1
    represented={pos(a,b,t) for a,b,t in itertools.product(range(-18,19),repeat=3)}
    require(set(range(1,300))<=represented,'finite Pos surjectivity diagnostic')
    require(all(pos(a,b,t)>0 for a,b,t in itertools.product(range(-10,11),repeat=3)), 'Pos positivity diagnostic')
    return {'signed_interval_cases':count,'negative_index_cases':residue_cases,
            'positive_representations_checked':299}

def build():
    require(len(VARS)==42 and len(set(VARS))==42,'42 distinct variables')
    ring=Ring(VARS+PORTS)
    for name,expr in AFFINE.items():ring.aliases[name]=ring.parse(expr)
    polys=[ring.parse(x) for x in ROWS]
    degrees=[max(sum(m[:42]) for m in p) for p in polys]
    require(degrees==[2]*27,'27 quadratic residuals')
    parent=json.loads((ROOT/'upstream/quartic45.json').read_text())
    parent_polys=[ring.parse(r) for r in parent['residuals'][:23]]
    require(polys[:22]==parent_polys[:22],'all 22 arithmetic residuals preserved')
    require(polys[22]==ring.add(parent_polys[22],ring.parse('-3*u**2')),'exact even-square restriction')
    require(polys[23:26]==[ring.parse(r) for r in parent['residuals'][25:]], 'dyadic and simplex guards preserved')
    require(polys[26]==ring.parse('eta*zeta-1-EZ_pos1**2-EZ_pos2**2-EZ_pos3**2-EZ_pos3'),'new product guard')
    # Audit the transport convention independently against the actual data.
    require(parent_polys[13]==ring.parse('(K0+w)*(beta*J+1-F-alpha)-F-z*beta*J'),'shifted transport convention')
    wrong=ring.parse('(K0+w)*C-F-(z-1)*(q-1)')
    require(wrong!=parent_polys[13],'off-by-one transport negative control')
    for i,name in enumerate(VARS):
        require(any(any(m[i] for m in p) for p in polys),'unused variable: '+name)
    total={}
    for p in polys:total=ring.add(total,ring.mul(p,p))
    require(max(sum(m[:42]) for m in total)==4,'quartic degree')
    tau4=list(ring.zero);tau4[VARS.index('tau')]=4
    require(total.get(tuple(tau4))==1,'exact nonzero tau^4 coefficient')
    # Independent evaluation with actual fixed coefficients modulo large primes.
    vals=fixed_values();rng=random.Random(421027)
    comparisons=0
    for modulus in (1000003,2147483647,2**127-1):
        for _ in range(60):
            assignment={v:rng.randrange(-20,21) for v in VARS}
            assignment.update({k:v%modulus for k,v in vals.items()})
            for name,expr in AFFINE.items():assignment[name]=literal_eval(expr,assignment,modulus)
            residuals=[literal_eval(x,assignment,modulus) for x in ROWS]
            for p,r in zip(polys,residuals):require(ring.evaluate(p,assignment,modulus)==r,'residual transcription')
            a=sum(r*r for r in residuals)%modulus
            b=ring.evaluate(total,assignment,modulus)
            require(a==b,'expanded quartic agreement')
            comparisons+=1
    packet={
        'name':'quartic42_even_square_sign_recovery',
        'domain':'unrestricted integers','variables':VARS,'variable_count':42,
        'fixed_numerals':PORTS,'affine_abbreviations':AFFINE,
        'residuals':ROWS,'equation_count':27,'residual_degrees':degrees,
        'single_polynomial':'sum of the squares of the 27 listed residuals',
        'exact_degree':4,'degree_certificate':{'monomial':'tau^4','coefficient':1},
        'coefficient_binding':'../coefficients/payloads/COEFFICIENT_BINDING.json',
        'coefficient_aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
        'transport_convention':'(K0+w)*C=F+z*(q-1); old unshifted coordinate is z+1',
        'source_pin':'beb0192cb8dc36f78c369c080f2adfbc1887a486',
        'proof':'../report/report.pdf',
        'status':'ordinary mathematical proof using explicitly cited inherited compiler/Pell theorems; no new kernel certificate',
    }
    expanded={'coordinate_order':VARS+PORTS,'fixed_port_count':4,
              'terms':[{'coefficient':c,'exponents':list(m)} for m,c in sorted(total.items())]}
    audit={'status':'PASS','variables':42,'quadratic_residuals':27,'exact_degree':4,
           'tau4_coefficient':1,'symbolic_terms_with_fixed_ports_indeterminate':len(total),
           'arithmetic_rows_preserved':22,'coefficient_payloads_authenticated':4,
           'modular_expanded_evaluator_comparisons':comparisons,
           'negative_controls':['off-by-one shifted transport is rejected'],
           'diagnostics':check_guard_diagnostics(),
           'boundary':'finite checks verify arithmetic data, not consistency or unbounded semantic equivalence'}
    return {'quartic42.json':packet,'quartic42_expanded.json':expanded,'AUDIT.json':audit}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true')
    args=ap.parse_args();outputs=build()
    for name,obj in outputs.items():
        raw=(json.dumps(obj,indent=2) if name!='quartic42_expanded.json' else json.dumps(obj,separators=(',',':')))+'\n'
        if args.write:(HERE/name).write_text(raw)
        else:require((HERE/name).read_text()==raw,'deterministic reproduction: '+name)
    print(json.dumps(outputs['AUDIT.json'],indent=2))

if __name__=='__main__':main()
