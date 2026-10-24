#!/usr/bin/env python3
"""Research synthesis: projected C222 source and positive arithmetic graphs.

The literal source reduction and arithmetic specialization have different
proof obligations. See proofs/SOURCE_AND_DOMAIN_AUDIT.md. No consistency assumption is used.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import signed_backend as build
import polynomial as sparse


def positive_class(base):
    class PositiveSigned(build.signed_class(base, True)):
        def __init__(self):
            super().__init__()
            self.power_cache = {}
            self.binomial_cache = {}
            self.factorial_cache = {}

        def var(self, label):
            shifted = label == 'N' or label.startswith('encoded row coordinate ')
            value = super().var(label + (' minus one' if shifted else ''))
            return self.addc(value, 1) if shifted else value

        def pow(self, n, k):
            key = (n, k)
            if key in self.power_cache:
                return self.power_cache[key]
            self.calls['power'] += 1
            self.calls['pell'] += 1
            before = (len(self.vars), len(self.eqs), len(self.nodes))
            tag = 'positive_power' + str(self.calls['power'])
            new = lambda label: self.fresh(tag + '.' + label)
            m = new('output')
            self.power_cache[key] = m
            W, A, T, Z, X, Y = [new(s) for s in ('W','A','T','Z','X','Y')]
            U, V, S, R, B = [new('pell.' + s) for s in ('U','V','S','R','B')]
            a2, yk, b2 = [new('slack.' + s) for s in ('a2','yk','b2')]
            self.eq(A, self.addc(a2, 2), tag + '.A_at_least_two')
            self.eq(Y, self.add(k, yk), tag + '.index_at_most_Y')
            self.eq(B, self.addc(b2, 2), tag + '.B_at_least_two')
            self.assertpoly(self.norm(A, X, Y), tag + '.norm1')
            self.assertpoly(self.norm(A, U, V), tag + '.norm2')
            self.assertpoly(self.norm(B, S, R), tag + '.norm3')
            q4 = new('q4')
            fourY = self.mul(self.c(4), Y)
            self.eq(B, self.addc(self.mul(fourY, q4), 1), tag + '.B_mod_4Y')
            vd = new('Vquotient_minus1')
            self.eq(V, self.mul(self.mul(Y,Y), self.addc(vd,1)), tag + '.V_positive_multiple')
            for left, right, modulus, label in [
                (B,A,U,'B_mod_U'), (S,X,U,'S_mod_U'),
                (R,k,fourY,'R_mod_4Y'),
                (self.add(X,self.mul(Y,n)),self.add(self.mul(Y,A),m),T,'power_congruence')]:
                self.assertpoly(self.mod(left,right,modulus,tag+'.'+label), tag+'.'+label)
            self.eq(self.prod([self.c(2),A,n]), self.sum([T,self.mul(n,n),self.c(1)]), tag+'.T_definition')
            gap, wn, wk = [new('slack.'+s) for s in ('gap','wn','wk')]
            self.eq(T,self.sum([m,gap,self.c(1)]),tag+'.output_bound')
            self.eq(W,self.add(n,wn),tag+'.base_bound')
            self.eq(W,self.add(k,wk),tag+'.exponent_bound')
            self.assertpoly(self.norm(self.addc(W,1),A,self.mul(W,Z)),tag+'.last_norm')
            self.ledger.append({'kind':'positive_power','arguments':(n,k),'result':m,
                                'before':before,'after':(len(self.vars),len(self.eqs),len(self.nodes))})
            return m

        def choose(self, n, k):
            key=(n,k)
            if key in self.binomial_cache:
                return self.binomial_cache[key]
            self.calls['binomial'] += 1
            before=(len(self.vars),len(self.eqs),len(self.nodes))
            tag='binomial'+str(self.calls['binomial'])
            out=self.fresh(tag+'.output')
            self.binomial_cache[key]=out
            q=self.addc(self.pow(self.c(2),n),1)
            numerator=self.pow(self.addc(q,1),n)
            denominator=self.pow(q,k)
            h,r,rs,os=[self.fresh(tag+'.'+s) for s in ('high','remainder','remainder_slack','output_slack')]
            quotient=self.add(self.mul(q,h),out)
            self.eq(numerator,self.add(self.mul(denominator,quotient),r),tag+'.digit_division')
            self.eq(denominator,self.sum([r,rs,self.c(1)]),tag+'.remainder_bound')
            self.eq(q,self.sum([out,os,self.c(1)]),tag+'.digit_bound')
            self.ledger.append({'kind':'positive_binomial','arguments':(n,k),'result':out,
                                'before':before,'after':(len(self.vars),len(self.eqs),len(self.nodes))})
            return out

        def fact(self,n):
            if n in self.factorial_cache:
                return self.factorial_cache[n]
            self.calls['factorial'] += 1
            before=(len(self.vars),len(self.eqs),len(self.nodes))
            tag='factorial'+str(self.calls['factorial'])
            out=self.fresh(tag+'.output')
            self.factorial_cache[n]=out
            shifted=self.addc(n,2)
            radius=self.pow(shifted,shifted)
            choose=self.choose(self.add(radius,n),n)
            numerator=self.pow(self.addc(radius,1),n)
            remainder,slack=[self.fresh(tag+'.'+s) for s in ('remainder','slack')]
            self.eq(self.add(numerator,choose),self.sum([self.mul(choose,out),remainder,self.c(1)]),tag+'.ceiling')
            self.eq(choose,self.sum([remainder,slack,self.c(1)]),tag+'.remainder_bound')
            self.ledger.append({'kind':'positive_factorial','arguments':(n,),'result':out,
                                'before':before,'after':(len(self.vars),len(self.eqs),len(self.nodes))})
            return out
    return PositiveSigned


def construct():
    src=Path(__file__).parent/'source'/'build_direct.py'
    spec=importlib.util.spec_from_file_location('synthesis_source',src)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    c,row,P,binding=module.build_circuit(positive_class(module.Compiler))
    return c,row,P,binding


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'equations')
    parser.add_argument('--affine-cap',type=int,default=16)
    args=parser.parse_args()
    c,row,P,binding=construct()
    circuit=build.prune(c)
    rows,polynomial,summary=build.flatten(circuit,args.affine_cap)
    args.output.mkdir(parents=True,exist_ok=True)
    raw={'format':'mixed-integer-arithmetic-dag-v1','variable_names':c.vars,
         'unrestricted_inputs':sorted(c.unrestricted),'nodes':c.nodes,'equalities':c.eqs,
         'source_binding':binding,'call_ledger':c.ledger}
    for name,obj in [('circuit_integer.json',circuit),('residuals_integer.json',rows),
                     ('equation_integer.json',polynomial),('summary_integer.json',summary),
                     ('source_circuit_before_pruning.json',raw),
                     ('row_source.json',{'variables':row.vars,'nodes':row.nodes,'output':P})]:
        sparse.dump(args.output/name,obj)
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
