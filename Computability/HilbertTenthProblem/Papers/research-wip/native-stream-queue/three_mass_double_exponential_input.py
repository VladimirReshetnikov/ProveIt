#!/usr/bin/env python3
"""Paid double-exponential loading for four complete unbounded mass histories.

Reads authenticated JSON only; no parent Python source executes.
program_multiplier is a fixed positive compiler numeral, not an input port.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

if not __debug__:
    raise RuntimeError('run without -O')
PINS = {
 'pell_fixed_affine_exponent52.py':'64893c621c538a8f5dba8a0fc417fd46aae7c607da996dd5f304ca13642f1486',
 'pell_fixed_affine_exponent52.json':'ebf7cafaa1f19c77c72302e5fee2e2c41c19b76a1ab72942758478ab1dd1adf1',
 'pell_fixed_affine_exponent52.md':'891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec',
 'three_mass_exponential_input_bridge.py':'fe892d2920a866c723ad648ea52ac467d0f531c6aabe13c000f3cd53fef57ef2',
 'three_mass_exponential_input_bridge.json':'976e75fc90da362949774ee5cfae2e1b48f35bf351203825b82b3dfba7353296',
 'three_mass_exponential_input_bridge.md':'0d839b4661cad99e37c19a590e9e14840d1d2961383a111c107f2957ccd87187',
}
VARIANTS=('incdec','zero3','nop','positive3')
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def sha(b): return hashlib.sha256(b).hexdigest()
def parents(root):
    root=Path(root) if root is not None else Path(__file__).resolve().parent
    for name,pin in PINS.items():
        if sha((root/name).read_bytes())!=pin: raise ValueError('source authentication: '+name)
    e=json.loads((root/'pell_fixed_affine_exponent52.json').read_text())
    p=json.loads((root/'three_mass_exponential_input_bridge.json').read_text())
    return e,{f['variant']:f['packet'] for f in p['forms'] if f['finalizer']=='sos'}

def renamed(v): return v if type(v) is int or v=='x' else 'first__'+v
def ledger(rows,free,roots):
    degrees={v:1 for v in free}; table={}; M=0
    for n,op,a,b in rows:
        if type(n) is not str or n in degrees or op not in ('+','-','*'): raise ValueError('DAG row')
        for v in (a,b):
            if type(v) is not int and (type(v) is not str or v not in degrees): raise ValueError('operand')
        da=0 if type(a) is int else degrees[a]; db=0 if type(b) is int else degrees[b]
        degrees[n]=da+db if op=='*' else max(da,db); table[n]=(a,b); M+=op=='*'
    live=set();todo=list(roots)
    while todo:
        v=todo.pop()
        if type(v) is str and v not in live:
            live.add(v);todo.extend(table.get(v,()))
    if not set(table)<=live or not set(free)<=live: raise ValueError('unused gate or coordinate')
    return {'operations':len(rows),'M':M,'A':len(rows)-M,'all_gates_and_coordinates_live':True,
            'literal_degree_upper_bound':max(0 if type(v) is int else degrees[v] for v in roots)}

def compose(e,p,C):
    if p['finalizer']!='sos' or p['parameters']!=['x','y','T']: raise ValueError('parent interface')
    if e['source'][-1]!=['output','-','factor_product_5',1]: raise ValueError('exponent output')
    if [r for r in p['polynomial_source'] if 'x' in r[2:]]!=[['exp__r','*',48,'x']]: raise ValueError('sole input consumer')
    if any('x' in pair for pair in p['comparisons']): raise ValueError('input comparison consumer')
    first=[['first__'+n,op,renamed(a),renamed(b)] for n,op,a,b in e['source'][:-1]]
    def inner(rows):
        ans=copy.deepcopy(rows)
        for row in ans:
            if row[0]=='exp__r': row[2:]=[48*C,'first__Q']
        return ans
    source=first+inner(p['source'])
    poly=first+inner(p['polynomial_source'])+[
        ['first_residual','-','first__factor_product_5',1],
        ['first_square','*','first_residual','first_residual'],
        ['double_output','+','first_square',p['output']]]
    comps=[['first__factor_product_5',1]]+copy.deepcopy(p['comparisons'])
    aux=['first__'+v for v in e['auxiliaries']]+p['auxiliaries']
    params=['x','y','T'];free=params+aux
    cl=ledger(source,free,[v for pair in comps for v in pair]);pl=ledger(poly,free,['double_output'])
    return {'variant':p['variant'],'program_multiplier':C,'parameters':params,'auxiliaries':aux,
      'domains':copy.deepcopy(p['domains']),'source':source,'comparisons':comps,'polynomial_source':poly,
      'output':'double_output','certificate_ledger':cl,'polynomial_ledger':pl,
      'positive_private_witnesses':len(aux),'degree':{'exact_degree_claimed':False,'upper_bound':max(108,p['degree']['upper_bound'])},
      'interfaces':{'first_power':'first__Q','second_power':'exp__Q','first_unit':'first__factor_product_5',
        'second_unit':'exp__factor_product_5','parent_polynomial':p['output'],'initial_payload':'exp__Q'},
      'relation':'(U1-1)^2 + F_single(C*Q1,y,T)',
      'positive_zero_projection':'Q1=2^(96*x); initial payload=2^(96*C*2^(96*x)); initial valuations=(96*C*2^(96*x),0)',
      'fixed_coefficient_recipe':{'second_r_coefficient':48*C,'second_virtual_input':'C*Q1','C_is_a_supplied_variable':False},
      'fixed_machine':copy.deepcopy(p['fixed_machine']),
      'scope':'Four nonuniversal fixed machines. Divider and Morita simulation tables are not compiled into these counts.'}

def build(variant='incdec',*,program_multiplier=1,root=None):
    if type(variant) is not str or variant not in VARIANTS: raise ValueError('variant')
    if type(program_multiplier) is not int or program_multiplier<=0: raise ValueError('fixed multiplier')
    e,ps=parents(root);return compose(e,ps[variant],program_multiplier)
def checked(packet,*,root=None):
    if type(packet) is not dict: raise ValueError('packet')
    p=build(packet.get('variant'),program_multiplier=packet.get('program_multiplier'),root=root)
    if not exact(packet,p): raise ValueError('noncanonical packet')
    return p
def values_of(rows,values):
    d=dict(values)
    for n,op,a,b in rows:
        a=a if type(a) is int else d[a];b=b if type(b) is int else d[b]
        d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d
def evaluate(packet,values,*,signed=False,root=None):
    p=checked(packet,root=root)
    if type(signed) is not bool or type(values) is not dict or set(values)!=set(p['parameters']+p['auxiliaries']): raise ValueError('assignment')
    for k,v in values.items():
        if type(v) is not int or (not signed and (v<0 or (k not in ('y','T') and v==0))): raise ValueError('domain')
    return values_of(p['polynomial_source'],values)[p['output']]

class Intern:
    def __init__(self):self.nodes={}
    def node(self,k):
        if k not in self.nodes:self.nodes[k]=len(self.nodes)
        return self.nodes[k]
    def atom(self,v):return self.node(('atom',type(v).__name__,v))
    def op(self,op,a,b):return self.node((op,a,b))
    def run(self,rows,values,cut=None):
        d=dict(values)
        for n,op,a,b in rows:
            d[n]=self.op(op,self.atom(a) if type(a) is int else d[a],self.atom(b) if type(b) is int else d[b])
            if cut and n in cut:d[n]=cut[n]
        return d
def structural(e,parent,p):
    C=p['program_multiplier'];I=Intern();leaves={v:I.atom(v) for v in p['parameters']+p['auxiliaries']}
    # Actual sole-consumer rows express 48*(C*Q1) and (48*C)*Q1.
    old=[r for r in parent['source'] if r[0]=='exp__r'];new=[r for r in p['source'] if r[0]=='exp__r']
    assert old==[['exp__r','*',48,'x']] and new==[['exp__r','*',48*C,'first__Q']]
    assert old[0][2]*C==new[0][2]
    cut=I.atom(('proved_r_coefficient',48*C))
    d=I.run(p['polynomial_source'],leaves,{'exp__r':cut})
    a=I.run(e['source'][:-1],{'x':leaves['x'],**{v:leaves['first__'+v] for v in e['auxiliaries']}})
    for n,_,_,_ in e['source'][:-1]:assert a[n]==d['first__'+n]
    v={'x':I.op('*',I.atom(C),a['Q']),'y':leaves['y'],'T':leaves['T'],**{v:leaves[v] for v in parent['auxiliaries']}}
    b=I.run(parent['polynomial_source'],v,{'exp__r':cut})
    for n,_,_,_ in parent['polynomial_source']:assert b[n]==d[n]
    for pair in parent['comparisons']:
        for v in pair:assert (I.atom(v) if type(v) is int else b[v])==(I.atom(v) if type(v) is int else d[v])
    res=I.op('-',a['factor_product_5'],I.atom(1))
    assert d[p['output']]==I.op('+',I.op('*',res,res),b[parent['output']])
    return {'first_certificate_registers':51,'parent_register_identities':len(parent['polynomial_source']),
            'parent_comparison_identities':len(parent['comparisons']),'whole_polynomial_identity':True,'r_coefficient':48*C}

def verify(root):
    e,ps=parents(root);forms=[];rng=random.Random(9610896)
    counts={'full_structural_identities':0,'comparison_identities':0,'numeric_whole_identities':0,
            'signed_cases':0,'rational_cases':0,'literal_SOS_evaluations':0,'public_evaluations':0,
            'guard_rejections':0,'copy_isolation':0}
    for C in (1,3):
        for variant in VARIANTS:
            parent=ps[variant];p=build(variant,program_multiplier=C,root=root);proof=structural(e,parent,p)
            counts['full_structural_identities']+=1;counts['comparison_identities']+=21
            assert [p['polynomial_ledger'][k]-parent['polynomial_ledger'][k] for k in ('operations','M','A')]==[54,32,22]
            assert len(p['auxiliaries'])==len(parent['auxiliaries'])+12 and len(p['comparisons'])==22
            assert p['degree']['upper_bound']==parent['degree']['upper_bound']==p['polynomial_ledger']['literal_degree_upper_bound']
            for case in range(20):
                vals={v:rng.randint(-2,3) if case<10 else rng.randint(1,3) for v in p['parameters']+p['auxiliaries']}
                if case>=18:vals={v:Fraction(z,2) for v,z in vals.items()}
                av=values_of(e['source'][:-1],{'x':vals['x'],**{v:vals['first__'+v] for v in e['auxiliaries']}})
                bv=values_of(parent['polynomial_source'],{'x':C*av['Q'],'y':vals['y'],'T':vals['T'],**{v:vals[v] for v in parent['auxiliaries']}})
                nv=values_of(p['polynomial_source'],vals)
                assert nv[p['output']]==(av['factor_product_5']-1)**2+bv[parent['output']]
                get=lambda v:v if type(v) is int else nv[v]
                assert nv[p['output']]==sum((get(a)-get(b))**2 for a,b in p['comparisons'])
                assert nv['first__Q']==48*vals['x']+vals['first__delta']
                assert nv['exp__Q']==48*C*nv['first__Q']+vals['exp__delta']
                counts['numeric_whole_identities']+=1;counts['literal_SOS_evaluations']+=1
                counts['signed_cases']+=case<10;counts['rational_cases']+=case>=18
                if case in (0,10):
                    assert evaluate(p,vals,signed=case==0,root=root)==nv[p['output']];counts['public_evaluations']+=1
            one={v:1 for v in p['parameters']+p['auxiliaries']}
            bads=[]
            for field,value in [('variant',True),('program_multiplier',True),('program_multiplier',float(C)),('program_multiplier',0),('output','x')]:
                q=copy.deepcopy(p);q[field]=value;bads.append(q)
            for field in ('source','polynomial_source'):
                q=copy.deepcopy(p);q[field][51][2]+=48;bads.append(q)
            q=copy.deepcopy(p);q['comparisons']=q['comparisons'][1:];bads.append(q)
            for q in bads:
                try:checked(q,root=root)
                except ValueError:counts['guard_rejections']+=1
                else:raise AssertionError('bad packet accepted')
            for key,value in [('x',0),('x',True),('y',-1),('T',-1),('first__delta',0),('exp__delta',0)]:
                vals=dict(one);vals[key]=value
                try:evaluate(p,vals,root=root)
                except ValueError:counts['guard_rejections']+=1
                else:raise AssertionError('bad assignment accepted')
            q=build(variant,program_multiplier=C,root=root);q['auxiliaries'].clear()
            assert exact(build(variant,program_multiplier=C,root=root),p);counts['copy_isolation']+=1
            forms.append({'variant':variant,'program_multiplier':C,'packet':p,'proof':proof})
    # C is an arbitrary positive fixed numeral in the loader theorem. Only
    # C=3^e is the optional universal-source program slice.
    for C in (2,5,27):
        p=build('nop',program_multiplier=C,root=root);structural(e,ps['nop'],p)
        assert p['polynomial_ledger']['operations']==578
    for C in (True,1.0,0,-1):
        try:build(program_multiplier=C,root=root)
        except ValueError:counts['guard_rejections']+=1
        else:raise AssertionError('bad compiler multiplier')
    return {'status':'PASS_DOUBLE_EXPONENTIAL_MASS_INPUT','source_sha256':sha(Path(__file__).read_bytes()),
      'pins':PINS,'counts':counts,'forms':forms,'additional_multiplier_shapes':[2,5,27],
      'scope':'Paid double-exponential interface for four fixed nonuniversal histories. No divider/simulator table is hidden in the costs; no gigantic positive Pell or loaded payload is materialized.'}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args();r=verify(args.root)
    if args.expect and not exact(r,json.loads(args.expect.read_text())):raise ValueError('receipt mismatch')
    if args.output:args.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':r['status'],'counts':r['counts'],'ledgers':[(f['variant'],f['program_multiplier'],f['packet']['polynomial_ledger']) for f in r['forms']]},sort_keys=True))
if __name__=='__main__':main()
