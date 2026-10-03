#!/usr/bin/env python3
"""Optional SOS-only removal of the last natural phase selector.

This extension preserves the separately frozen original compiler artifacts.
"""
from dataclasses import dataclass
from exact_phase_quartic import Poly,Certificate,integer,compile_charts


@dataclass(frozen=True)
class ReducedSOS:
    source: Certificate
    certificate: Certificate
    branches: int
    removed_witness_index: int

    def __post_init__(self):
        if type(self.source) is not Certificate or type(self.certificate) is not Certificate:
            raise TypeError('exact immutable Certificate objects required')
        integer(self.branches,'branch count',True)
        integer(self.removed_witness_index,'removed witness index',True)
        if self.branches<1 or self.removed_witness_index!=self.branches-1:
            raise ValueError('last retained-source selector must be removed')
        if len(self.certificate.witness_names)+1!=len(self.source.witness_names):
            raise ValueError('exactly one witness must be removed')

    def evaluate(self,external,witness):
        return self.certificate.evaluate(external,witness)

    def drop_selector(self,source_witness):
        source_witness=tuple(source_witness)
        if len(source_witness)!=len(self.source.witness_names):
            raise ValueError('wrong source witness arity')
        for x in source_witness:
            integer(x,'source witness coordinate',True)
        if sum(source_witness[:self.branches])!=1:
            raise ValueError('source selectors must be one-hot')
        k=self.removed_witness_index
        return source_witness[:k]+source_witness[k+1:]

    def witness(self,chart_index,parameters):
        return self.drop_selector(self.source.witness(chart_index,parameters))


def eliminate_last_selector(source,branches=None):
    if type(source) is not Certificate or source.mode!='sos' or source.nonnegative_products:
        raise ValueError('selector elimination accepts SOS certificates only')
    b=len(source.charts) if branches is None else integer(branches,'branch count',True)
    if b<1 or b>len(source.witness_names):
        raise ValueError('positive branch count required')
    if source.charts and b!=len(source.charts):
        raise ValueError('branch count disagrees with charts')
    q=source.external_count
    oldarity=source.expression.arity
    oldvars=[Poly.var(oldarity,k) for k in range(oldarity)]
    if not source.residuals or source.residuals[0] != sum(oldvars[q:q+b],Poly.const(oldarity,0))-1:
        raise ValueError('source first residual is not the asserted one-hot constraint')
    arity=oldarity-1
    variables=[Poly.var(arity,k) for k in range(arity)]
    E=sum(variables[q:q+b-1],Poly.const(arity,0))
    omitted=q+b-1
    replacements=[variables[k] if k<omitted else 1-E if k==omitted else variables[k-1]
                  for k in range(oldarity)]
    def substitute(poly):
        result=Poly.const(arity,0)
        for powers,coefficient in poly.terms:
            term=Poly.const(arity,coefficient)
            for power,replacement in zip(powers,replacements):
                if power:
                    term=term*(replacement**power)
            result=result+term
        return result
    residuals=(E*(E-1),)+tuple(substitute(r) for r in source.residuals[1:])
    if any(r.degree>2 for r in residuals):
        raise ValueError('substitution exceeded quadratic residual degree')
    expression=sum((r*r for r in residuals),Poly.const(arity,0))
    names=source.witness_names[:b-1]+source.witness_names[b:]
    certificate=Certificate((),q,names,(),residuals,(),expression,'sos',source.natural_external_indices)
    return ReducedSOS(source,certificate,b,b-1)


def compile_reduced_charts(charts):
    return eliminate_last_selector(compile_charts(charts,'sos'))
