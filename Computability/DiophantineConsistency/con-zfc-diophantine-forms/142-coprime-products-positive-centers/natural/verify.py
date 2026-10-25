#!/usr/bin/env python3
"""Independent changed-row and exact nonnegative-contraction audit.

This checker does not import build.py. Rebuild, when requested, invokes it
as a separate process into a temporary directory and compares every byte.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True


def need(condition,message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def collect(terms):
    result={}
    for coefficient,monomial in terms:
        need(type(coefficient) is int,'integer coefficient required')
        key=tuple(sorted(monomial))
        result[key]=result.get(key,0)+coefficient
    return tuple((m,c) for m,c in sorted(result.items()) if c)


def named_rows(equation):
    names=[entry['name'] for entry in equation['variables']]
    need(len(set(names))==len(names),'duplicate variable names')
    need(equation['domain']=='nonnegative integers','source domain')
    result=[]
    for row in equation['residuals']:
        terms=[]
        for coefficient,monomial in row['terms']:
            need(len(monomial)<=2 and all(type(i) is int and 0<=i<len(names) for i in monomial),'quadratic coordinate range')
            terms.append((coefficient,[names[i] for i in monomial]))
        result.append((row['label'],collect(terms)))
    return result


def expected_source(parent):
    old=named_rows(parent)
    need(len(parent['variables'])==334 and len(old)==284,'pinned source dimensions')
    groups=[
        ('t0',['choose0','crt.range.index'],'pow3.output'),
        ('t',['crt.range.'+s for s in ('a','b','c','d','derived_label_sum')],'mul.422'),
        ('y',['crt.range.S','crt.range.Sp'],'pow4.output'),
        ('x',['crt.range.u','crt.range.vq'],'pow5.output')]
    replacement={}
    bound_labels={'choose0.digit_bound'}
    slack_rename={}
    for label,requests,den in groups:
        new_name='pooled_digits.'+label+'.slack'
        terms=[(1,[den]),(-1,[new_name]),(-1,[])]
        terms.extend((-1,[r+'.modular_remainder']) for r in requests)
        replacement[requests[0]+'.remainder_bound']=('pooled_digits.'+label,collect(terms))
        bound_labels.update(r+'.remainder_bound' for r in requests)
        slack_rename[requests[0]+'.modular_rslack']=new_name
    square='index_cap.auxiliary_trace_square'
    inserted=[
        ('index_cap.auxiliary_trace_square',collect([(1,[square]),(-1,['index_cap.U','index_cap.U'])])),
        ('index_cap.positive_comparison_center',collect([
            (1,['mul.437']),(-1,['shared.lower_A']),(-1,['shared.A_slack']),(1,[]),
            (-4,['index_cap.Y',square]),(-1,[square]),
            (1,['shared.lower_A',square]),(1,['shared.A_slack',square])]))]
    even_multiple=('index_cap.V_even_positive_multiple',collect([
        (1,['index_cap.V']),(-2,['mul.444'])]))
    need(old[153]==('multiplication',collect([
        (-4,['index_cap.Y']),(-4,['index_cap.Y','index_cap.q4minus1']),(1,['mul.437'])])),'old comparison parameter')
    need(old[162]==('index_cap.V_positive_multiple',collect([
        (1,['index_cap.V']),(-1,['mul.444'])])),'old auxiliary multiple')
    need(old[163]==('multiplication',collect([
        (-1,['index_cap.U','index_cap.Bquotient']),(1,['mul.445'])])),'old comparison quotient gate')
    need(old[164]==('index_cap.B_mod_U',collect([
        (1,[]),(-1,['shared.lower_A']),(-1,['shared.A_slack']),(1,['mul.437']),(-1,['mul.445'])])),'old comparison congruence')
    result=[]
    for number,(label,terms) in enumerate(old):
        if number==153:
            result.extend(inserted)
        elif number in (163,164):
            continue
        elif number==162:
            result.append(even_multiple)
        elif label in replacement:
            result.append(replacement[label])
        elif label not in bound_labels:
            result.append((label,collect([(c,[slack_rename.get(n,n) for n in m]) for m,c in terms])))
    used={name for _,terms in result for monomial,c in terms for name in monomial}
    variables=[]
    for entry in parent['variables']:
        entry=deepcopy(entry)
        entry['name']=slack_rename.get(entry['name'],entry['name'])
        if entry['name'] in used:
            variables.append(entry)
    if square in used:
        variables.append({'name':square,'kind':'gate'})
    return variables,result


def verify_source(parent,source):
    variables,rows=expected_source(parent)
    need(source['variables']==variables,'complete ordered variable list')
    need(named_rows(source)==rows,'complete changed-row transcription')
    need(len(variables)==324 and len(rows)==275,'new raw source size')
    live={i for row in source['residuals'] for c,m in row['terms'] for i in m}
    need(live==set(range(len(variables))),'raw coordinate liveness')
    return {'variables':len(variables),'quadratic_rows':len(rows),'complete_source_rows_checked':len(rows)}


def load_contraction_checker():
    path=ROOT/'inherited/psd_contract/check.py'
    spec=importlib.util.spec_from_file_location('independent_contraction_checker',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def pell_pair(A,index):
    # Exact multiplication in Z[sqrt(A²-1)], using binary powering.
    D=A*A-1
    x,y=1,0
    u,v=A,1
    while index:
        if index&1:
            x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v
        index//=2
    return x,y


def center_controls():
    results=[]
    corruptions_rejected=0
    for A in range(2,6):
        for H in (2,3):
            x,y=pell_pair(A,H)
            modulus=2*y*y
            u0,v0=1,0
            period=None
            for step in range(1,modulus*modulus+1):
                u0,v0=(A*u0+(A*A-1)*v0)%modulus,(u0+A*v0)%modulus
                if (u0,v0)==(1,0):
                    period=step
                    break
            need(period is not None,'finite determinant-one period')
            u,v=pell_pair(A,period)
            need(v%modulus==0 and v>=modulus,'positive even multiple')
            C=A+(4*y+1-A)*u*u
            s,r=pell_pair(C,H)
            need(C>A and C%u==A%u and (C-1)%(4*y)==0,'center congruences')
            need((s-x)%u==0 and s>=x and (r-H)%(4*y)==0 and r>=H,'comparison witnesses')
            e=v//modulus-1
            d=(C-1)//(4*y)-1
            f=(4*y+1-A)*u
            need(min(e,d,f)>=0,'old natural witnesses')
            need(C==1+4*y*(d+1)==A+u*f,'full old comparison restoration')
            if (A+(3*y+1-A)*u*u-1)%(4*y)!=0:
                corruptions_rejected+=1
            results.append({'A':A,'H':H,'period':period,'auxiliary_bits':u.bit_length(),'comparison_bits':C.bit_length()})
    need(corruptions_rejected>0,'center mutation must be caught by a real congruence control')
    return {'cases':results,'incorrect_coefficient_three_rejected_cases':corruptions_rejected}


def mutation_checks(parent,source,checker,target,certificate):
    count=0
    def rejected(action,label):
        nonlocal count
        try:
            action()
        except (ValueError,KeyError,TypeError):
            count+=1
            return
        raise ValueError('Mutation escaped: '+label)
    for label in ('pooled_digits.t','index_cap.positive_comparison_center','index_cap.V_even_positive_multiple'):
        bad=deepcopy(source)
        row=next(r for r in bad['residuals'] if r['label']==label)
        row['terms'][0][0]+=1
        rejected(lambda:verify_source(parent,bad),label)
    bad=deepcopy(source)
    bad['variables'][0]['name']='incorrect_variable'
    rejected(lambda:verify_source(parent,bad),'variable binding')
    bad=deepcopy(target)
    bad['residuals'][0]['terms'][0][0]+=1
    cert=deepcopy(certificate)
    cert['target_equation_sha256']=hashlib.sha256(checker.canonical(bad)).hexdigest()
    rejected(lambda:checker.verify(source,bad,cert),'changed endpoint even after rehashing')
    cert=deepcopy(certificate)
    cert['steps'][0]['restoration'][0][0]+=1
    rejected(lambda:checker.verify(source,target,cert),'changed restoration')
    cert=deepcopy(certificate)
    for step in cert['steps']:
        if step['nonnegative_certificate']['squares']:
            step['nonnegative_certificate']['squares'][0]['weight']=[-1,1]
            break
    rejected(lambda:checker.verify(source,target,cert),'negative square certificate weight')
    return {'deliberate_corruptions_rejected':count}


def verify(rebuild=False):
    provenance=read(ROOT/'PROVENANCE.json')
    for name,digest in provenance['files'].items():
        need(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'inherited byte identity: '+name)
    parent=read(ROOT/'inherited/architecture/strict_natural229/raw/equation.json')
    source=read(ROOT/'equations/raw/equation.json')
    result={'inherited_files_authenticated':len(provenance['files']),
            'raw':verify_source(parent,source),'endpoints':{}}
    checker=load_contraction_checker()
    for number in (221,222):
        folder=ROOT/'equations'/('natural'+str(number))
        target=read(folder/'equation.json')
        certificate=read(folder/'elimination_certificate.json')
        polynomial=read(folder/'expanded_polynomial.json')
        receipt,terms=checker.verify(source,target,certificate)
        need(polynomial['terms']==terms,'complete coefficient collection')
        need(receipt==read(folder/'VERIFICATION.json'),'recorded verification metrics')
        need(receipt['variables']==number and receipt['exact_degree']==4,'endpoint domain and degree')
        need({i for c,m in terms for i in m}==set(range(number)),'expanded coordinate liveness')
        result['endpoints'][str(number)]=receipt
        if number==221:
            result['mutations']=mutation_checks(parent,source,checker,target,certificate)
    result['small_exact_center_controls']=center_controls()
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='natural221-rebuild-') as temporary:
            output=Path(temporary)/'equations'
            command=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'build.py'),'--output',str(output)]
            completed=subprocess.run(command,check=True,capture_output=True,text=True)
            expected=sorted(p.relative_to(ROOT/'equations').as_posix() for p in (ROOT/'equations').rglob('*.json'))
            actual=sorted(p.relative_to(output).as_posix() for p in output.rglob('*.json'))
            need(expected==actual,'complete rebuilt artifact inventory')
            for relative in expected:
                need((ROOT/'equations'/relative).read_bytes()==(output/relative).read_bytes(),'byte reconstruction: '+relative)
            result['rebuild']={'byte_identical_files':len(expected),'exit_code':completed.returncode}
    result['passed']=True
    result['python_optimization']=sys.flags.optimize
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--rebuild',action='store_true')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    result=verify(args.rebuild)
    payload=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(payload)
    print(payload)
