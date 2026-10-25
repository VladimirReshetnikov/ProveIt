#!/usr/bin/env python3
"""Reconstruct the two new natural quartics from the pinned literal parent."""
from pathlib import Path
from copy import deepcopy
import importlib.util
import json
import hashlib
import argparse

ROOT = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


pc = module('positive_monic_contractor', ROOT/'inherited/psd_contract/contract.py')
checker = module('independent_monic_checker', ROOT/'inherited/psd_contract/check.py')


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n')


def source_transform():
    parent_path = ROOT/'inherited/architecture/strict_natural229/raw/equation.json'
    provenance = json.loads((ROOT/'PROVENANCE.json').read_text())
    expected_hash = provenance['files'][parent_path.relative_to(ROOT).as_posix()]
    if hashlib.sha256(parent_path.read_bytes()).hexdigest() != expected_hash:
        raise ValueError('Pinned raw source changed')
    original = json.loads(parent_path.read_text())
    source = deepcopy(original)
    index = {record['name']:i for i,record in enumerate(source['variables'])}
    def v(name): return index[name]
    ordinate, trace = v('index_cap.Y'), v('index_cap.U')
    lower, scale_slack, center_minus_one = [v(name) for name in
        ('shared.lower_A','shared.A_slack','mul.437')]
    trace_square = len(source['variables'])
    source['variables'].append({'name':'index_cap.auxiliary_trace_square','kind':'gate'})
    square_row = {'label':'index_cap.auxiliary_trace_square',
        'terms':pc.dump(pc.loadpoly([[1,[trace_square]],[-1,[trace,trace]]]))}
    center_row = {'label':'index_cap.positive_comparison_center', 'terms':pc.dump(pc.loadpoly([
        [1,[center_minus_one]],[-1,[lower]],[-1,[scale_slack]],[1,[]],
        [-4,[ordinate,trace_square]],[-1,[trace_square]],
        [1,[lower,trace_square]],[1,[scale_slack,trace_square]]]))}
    rows = []
    for row_number,row in enumerate(source['residuals']):
        if row_number == 153:
            rows.extend([square_row,center_row])
        elif row_number in (163,164):
            continue
        elif row_number == 162:
            rows.append({'label':'index_cap.V_even_positive_multiple',
                'terms':pc.dump(pc.loadpoly([[1,[v('index_cap.V')]],[-2,[v('mul.444')]]]))})
        else:
            rows.append(row)
    source['residuals'] = rows
    groups = [
        ('t0',['choose0','crt.range.index'],'pow3.output'),
        ('t',['crt.range.'+name for name in ('a','b','c','d','derived_label_sum')],'mul.422'),
        ('y',['crt.range.S','crt.range.Sp'],'pow4.output'),
        ('x',['crt.range.u','crt.range.vq'],'pow5.output')]
    replacement = {}
    deleted_labels = {'choose0.digit_bound'}
    for label,requests,denominator in groups:
        slack = v(requests[0]+'.modular_rslack')
        terms = [[1,[v(denominator)]],[-1,[slack]],[-1,[]]]
        terms.extend([-1,[v(name+'.modular_remainder')]] for name in requests)
        replacement[requests[0]+'.remainder_bound'] = {
            'label':'pooled_digits.'+label,'terms':pc.dump(pc.loadpoly(terms))}
        source['variables'][slack]['name'] = 'pooled_digits.'+label+'.slack'
        deleted_labels.update(name+'.remainder_bound' for name in requests)
    source['residuals'] = [replacement.get(row['label'],row)
        for row in source['residuals']
        if row['label'] in replacement or row['label'] not in deleted_labels]
    used = sorted({i for row in source['residuals'] for c,m in row['terms'] for i in m})
    rename = {old:new for new,old in enumerate(used)}
    source['variables'] = [source['variables'][i] for i in used]
    for row in source['residuals']:
        row['terms'] = pc.dump(pc.loadpoly([[c,[rename[i] for i in m]] for c,m in row['terms']]))
    source['variant'] = 'positive_center_four_pooled_self_sized_digit_budgets'
    source['metrics'],polynomial = pc.metrics_and_polynomial(source)
    certificate = {'schema':'positive_center_pooled_digit_transformation_v1',
        'parent':'inherited/architecture/strict_natural229/raw/equation.json',
        'parent_sha256':expected_hash, 'groups':groups,
        'retained_extended_parent_indices':used,
        'new_extended_parent_coordinate':trace_square,
        'deleted_private_output_bound':'choose0.digit_bound',
        'proof':'PROOF.md'}
    return source,polynomial,certificate


def build(output):
    output = Path(output).resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError('Choose an empty output directory')
    source,expanded,transformation = source_transform()
    for name,value in [('raw/equation.json',source),('raw/expanded_polynomial.json',expanded),
                       ('raw/transformation.json',transformation)]:
        write(output/name,value)
    summary = {}
    for target_size,support_cap in [(221,48),(222,32)]:
        target,certificate,polynomial = pc.contract(source,support_cap=support_cap)
        receipt,independent = checker.verify(source,target,certificate)
        if polynomial['terms'] != independent or len(target['variables']) != target_size:
            raise ValueError('Independent coefficient check or target dimension failed')
        destination = output/('natural'+str(target_size))
        for name,value in [('equation.json',target),('elimination_certificate.json',certificate),
                           ('expanded_polynomial.json',polynomial),('VERIFICATION.json',receipt)]:
            write(destination/name,value)
        summary[str(target_size)] = receipt
    write(output/'SUMMARY.json',summary)
    return summary


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(build(args.output),indent=2))
