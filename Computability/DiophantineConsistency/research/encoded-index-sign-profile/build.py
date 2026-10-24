#!/usr/bin/env python3
"""Fresh74-predicate profiles; delete only raw59 from frozen75 parents."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
CONFIGS = {
    'compact': [('unprojected',0,None),('support4',4,None),('support8',8,None),
                ('support16',16,None),('support32',32,None)],
    'raw': [('retained',0,None),('support2_affine1',2,1),('support2_affine2',2,2),
            ('support4_affine2',4,2),('support8_affine2',8,2),('support16_affine2',16,2),
            ('support32_affine2',32,2),('support8_affine3',8,3),('support16_affine3',16,3),
            ('support32_affine3',32,3),('support8_default',8,None),('support16_default',16,None)]}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(data):
    return sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def generate():
    pins = load(HERE/'SOURCE_PINS.json')
    for name,expected in pins['files'].items():
        need(digest((ROOT/name).read_bytes()) == expected,'whole frozen source '+name)
    archive = REPO/pins['archive']
    need(digest(archive.read_bytes()) == pins['archive_sha256'],'whole arithmetic archive')
    files,census = {},{}
    with tempfile.TemporaryDirectory(prefix='encoded-index74-profile-') as tmp,zipfile.ZipFile(archive) as z:
        for name,expected in pins['members'].items():
            need(digest(z.read(name)) == expected,'whole arithmetic member '+name)
        member = next(name for name in pins['members'] if name.endswith('/terminal_elimination.py'))
        engine_path = Path(tmp)/'engine.py'
        engine_path.write_bytes(z.read(member))
        engine = module('pinned_encoded_index74_optimizer',engine_path)
        for family,configs in CONFIGS.items():
            predecessor = ROOT/'research/factorial-radius-output-sign-profile'/family
            old,old_domain = load(predecessor/'parent.json'),load(predecessor/'domain.json')
            n,nr = old_domain['baseline_body_variables'],old_domain['baseline_body_rows']
            eq = dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',
                variant='encoded_index_sign74_'+family,variables=deepcopy(old['variables'][:n]),
                residuals=deepcopy(old['residuals'][:nr]))
            guards,deleted = [],[]
            for old_index,g in enumerate(old_domain['guards']):
                predicate = deepcopy(g['predicate'])
                if predicate['kind'] == 'retained_scalar' and predicate['raw_variables'] == [59]:
                    deleted.append(old_index)
                    continue
                a,b,c = range(len(eq['variables']),len(eq['variables'])+3)
                # Preserve the remaining predicate and its existing names/labels
                # verbatim, changing only the private triple's coordinate indices.
                eq['variables'].extend(deepcopy(old['variables'][v]) for v in g['auxiliary'])
                eq['residuals'].append(dict(label=old['residuals'][nr+old_index]['label'],
                    terms=deepcopy(predicate['terms'])+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
                guards.append(dict(predicate=predicate,auxiliary=[a,b,c]))
            need(len(old_domain['guards']) == 75 and len(guards) == 74 and len(deleted) == 1,
                 'delete exactly original scalar59 from75 predicates')
            files[family+'/parent.json'] = encoded(eq)
            files[family+'/domain.json'] = encoded(dict(baseline_body_variables=n,baseline_body_rows=nr,
                baseline_raw_indices=deepcopy(old_domain['baseline_raw_indices']),guards=guards,
                removed_original_scalar_guard=59,retained_parent_predicates=74,
                inherited_parent_removed_original_scalar_guard=old_domain['removed_original_scalar_guard'],
                deleted_parent_guard_index=deleted[0]))
            for name,cap,affine in configs:
                out,cert,metrics = engine.optimize(eq,max_support=cap,affine_support=affine)
                need(cert['unconstrained_removed'] == [],'every omitted integer uniquely restored')
                engine.verify(eq,out,cert)
                path = family+'/'+name
                files[path+'/equation.json'] = encoded(out)
                files[path+'/projection.json'] = encoded(cert)
                files[path+'/polynomial.json'] = encoded(engine.expand(out))
                census[path] = dict(metrics=out['metrics'],support_cap=cap,affine_cap=affine,
                    unique_signed_restorations=len(cert['steps']),unconstrained_removed=[])
                print(path,out['metrics']['variables'],out['metrics']['expanded_monomials'],
                      out['metrics']['max_abs_expanded_coefficient'],flush=True)
    files['CENSUS.json'] = encoded(census)
    files['BUILD.json'] = encoded(dict(generator_sha256=digest(Path(__file__).read_bytes()),
        files={name:digest(data) for name,data in files.items()},
        scope='Fresh74-predicate ordinary-source research profiles. No accepted metric promotion, native/internal-ZFC/Lean result.'))
    return files,census


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    files,census = generate()
    for name,data in files.items():
        path = HERE/name
        if args.check:
            need(path.read_bytes() == data,'complete deterministic profile '+name)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,profiles=len(census)),indent=2))


if __name__ == '__main__':
    main()
