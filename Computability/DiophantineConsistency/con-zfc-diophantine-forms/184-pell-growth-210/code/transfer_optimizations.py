#!/usr/bin/env python3
"""Transfer eligible integral charts from the frozen parent, recording every map."""
from pathlib import Path
import argparse, copy, hashlib, json, sys
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'inherited/anchor'
sys.path.insert(0, str(SOURCE / 'code'))
import audit_optimizations as a
from polynomial import canonical


def build(inp, dest, profile_index=1):
    raw, doc, rows = a.read_equation(inp)
    original = copy.deepcopy(rows)
    n = len(doc['variables'])
    plan = json.loads((SOURCE / 'OPTIMIZATION_CHAIN.json').read_bytes())['profiles'][profile_index]
    old_doc = json.loads((SOURCE / plan['source']).read_bytes())
    if profile_index == 1:
        gone_vars = {138,139,180,181,182,183}
        gone_rows = {96,97,126,127,129}
    elif profile_index == 0:
        gone_vars = {184}
        gone_rows = {129}
    else:
        raise ValueError('Unsupported comparison profile')
    vr = {i:j for j,i in enumerate(i for i in range(len(old_doc['variables'])) if i not in gone_vars)}
    rr = {i:j for j,i in enumerate(i for i in range(len(old_doc['residuals'])) if i not in gone_rows)}
    for i,j in vr.items():
        if i >= 130 and old_doc['variables'][i]['name'] != doc['variables'][j]['name']:
            raise ValueError(('coordinate transfer mismatch',i,j))
    for i,j in rr.items():
        if old_doc['residuals'][i]['label'] != doc['residuals'][j]['label']:
            raise ValueError(('row transfer mismatch',i,j))
    all_ops = []
    stages = []
    for stage in plan['stages']:
        cert = json.loads((SOURCE / stage['certificate']).read_bytes())
        ops = a.get_ops(stage['kind'], cert, len(old_doc['variables']))
        translated, skipped = [], []
        for op in ops:
            if op['type'] == 'row':
                if op['target'] not in rr or op['source'] not in rr:
                    skipped.append(op); continue
                translated.append(dict(op,target=rr[op['target']],source=rr[op['source']]))
            else:
                support = {i for _, mon in op['image'] for i in mon}
                if op['coordinate'] not in vr or not support <= set(vr):
                    skipped.append(op); continue
                translated.append(dict(op,coordinate=vr[op['coordinate']],
                    image=[[c,sorted(vr[i] for i in mon)] for c,mon in op['image']]))
        before = copy.deepcopy(rows)
        rows = a.apply(rows, translated, n)
        if a.apply(rows, translated, n, inverse=True) != before:
            raise ValueError('Inverse failure')
        all_ops += translated
        met, expanded = a.metrics(doc, rows)
        stages.append({'kind':stage['kind'], 'parent_certificate':stage['certificate'],
                       'operations':translated, 'skipped':skipped, 'metrics':met})
        print(stage['kind'],len(translated),met,flush=True)
    if a.apply(rows, all_ops, n, inverse=True) != original:
        raise ValueError('Composed inverse failure')
    result = copy.deepcopy(doc)
    result['variant'] += ':integral_charts'
    for r,p in zip(result['residuals'], rows):
        r['terms'] = [[c,list(m)] for m,c in sorted(p.items())]
    met, expanded = a.metrics(result, rows)
    cert = {'schema':'elementary-integral-operations-v1',
            'input_sha256':hashlib.sha256(raw).hexdigest(),
            'output_sha256':hashlib.sha256(canonical(result)).hexdigest(),
            'operations':all_ops,'stages':stages,
            'variable_map':[[i,j] for i,j in vr.items()], 'row_map':[[i,j] for i,j in rr.items()]}
    dest.mkdir(parents=True,exist_ok=True)
    for name,obj in [('equation.json',result),('metrics.json',met),('certificate.json',cert),
      ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':n,
        'terms':[[c,list(m)] for m,c in sorted(expanded.items())]})]:
        (dest/name).write_bytes(canonical(obj))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--profile',choices=['principal','balanced'],default='principal')
    args=parser.parse_args()
    build(args.input,args.output,profile_index=1 if args.profile=='principal' else 0)
