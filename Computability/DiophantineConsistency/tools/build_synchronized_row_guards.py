#!/usr/bin/env python3
"""Integer companions certified by actual synchronized natural row equations."""
import argparse
from collections import defaultdict
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
DEST=ROOT/'candidates/synchronized-row-guards'
ARCHIVE=REPO/'docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip'
ARCHIVE_SHA='ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'
FRAMEWORK=ROOT/'tools/build_shared_crt_row_guards.py'
FRAMEWORK_SHA='dee810ff01606cdaa91e477360bd7106f3405e9adc4e026c549e9ed80bb2fbf5'
VARIANTS=[('natural522','integer1224'),('natural529','integer1231'),
          ('natural596','integer1298'),('source895','integer1597')]


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return sha256(raw).hexdigest()


def encoded(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()


def build_variant(parent_raw,source_name,target_name,rules_from_rows,close):
    parent=json.loads(parent_raw);n=len(parent['variables'])
    need(parent['domain']=='nonnegative integers','natural parent domain')
    rules=rules_from_rows(parent['residuals'])
    outputs={r['output']for r in rules}
    guards=set(range(n))-outputs
    complete,proof=close(guards,rules,n,record=True)
    need(complete and len(guards)==234 and len(guards)+len(proof)==n,'complete forced-seed row derivation')
    variables=list(parent['variables']);rows=list(parent['residuals']);bindings=[]
    for i in sorted(guards):
        a,b,c=range(len(variables),len(variables)+3)
        for suffix in ['a','b','c']:variables.append(dict(name=f'rowguard.{i}.{suffix}',kind='integer_guard_auxiliary'))
        rows.append(dict(label=f'row-derived nonnegativity seed {i}',
                         terms=[[1,[i]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        bindings.append(dict(input=i,auxiliaries=[a,b,c]))
    polynomial=defaultdict(int)
    for row in rows:
        for a,ma in row['terms']:
            for b,mb in row['terms']:polynomial[tuple(sorted(ma+mb))]+=a*b
    terms=[[c,list(m)]for m,c in sorted(polynomial.items())if c]
    count=len(variables)
    metrics=dict(variables=count,natural_parent_variables=n,seed_guards=len(guards),
                 nonnegativity_auxiliaries=3*len(guards),row_certificate_steps=len(proof),
                 quadratic_rows=len(rows),exact_degree=max(len(m)for c,m in terms),
                 expanded_monomials=len(terms),max_abs_expanded_coefficient=max(abs(c)for c,m in terms),
                 max_abs_row_coefficient=max(abs(c)for row in rows for c,m in row['terms']))
    need(target_name=='integer'+str(count),'actual integer count in variant name')
    eq=dict(schema='finite_quadratic_residuals_v1',domain='unrestricted integers',
            polynomial='sum(square(row) for row in residuals)',variables=variables,residuals=rows,
            natural_parent_sha256=sha(parent_raw),seed_guards=bindings,metrics=metrics)
    expanded=dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=count,terms=terms)
    certificate=dict(schema='integer_row_nonnegativity_v1',parent_variables=n,
        parent_equation_sha256=sha(parent_raw),seed_variables=sorted(guards),derivation=proof,
        available_elementary_rules=len(rules),available_rule_outputs=sorted(outputs),
        rule='c*x=P, c>0, output absent from RHS, all RHS coefficients nonnegative; odd powers require prior nonnegativity, even powers require no premise',
        seed_choice='Exactly coordinates with no conclusion rule; no variable-kind metadata is used.',
        minimum_for_this_explicit_rule_class=True,global_minimum_guard_claim=False)
    member=f'con_zfc_synchronized_certificates/equations/{source_name}/equation.json'
    pins=dict(archive=str(ARCHIVE.relative_to(REPO)),archive_sha256=ARCHIVE_SHA,
              parent_member=member,parent_sha256=sha(parent_raw),source_name=source_name,
              framework_path=str(FRAMEWORK.relative_to(ROOT)),framework_sha256=FRAMEWORK_SHA)
    files={'natural_parent.json':parent_raw,'equation.json':encoded(eq),
           'expanded_polynomial.json':encoded(expanded),'NONNEGATIVITY.json':encoded(certificate),
           'PARENT_PINS.json':encoded(pins)}
    receipt=dict(status='PASS',metrics=metrics,
        generator_sha256=sha(Path(__file__).read_bytes()),
        sha256={name:sha(raw)for name,raw in files.items()},
        scope='Actual integer row closure, exact Legendre seed guards and complete quartic. Parent ordinary semantics is separate; no Lean/internal-ZFC derivation.')
    files['BUILD.json']=encoded(receipt)
    return files,metrics


def build():
    need(sha(ARCHIVE.read_bytes())==ARCHIVE_SHA,'whole original archive')
    need(sha(FRAMEWORK.read_bytes())==FRAMEWORK_SHA,'frozen elementary row-closure framework')
    spec=importlib.util.spec_from_file_location('frozen_row_framework',FRAMEWORK)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    files={};metrics={}
    with zipfile.ZipFile(ARCHIVE)as z:
        for source_name,target_name in VARIANTS:
            member=f'con_zfc_synchronized_certificates/equations/{source_name}/equation.json'
            new,measure=build_variant(z.read(member),source_name,target_name,module.rules_from_rows,module.close)
            files.update({target_name+'/'+name:raw for name,raw in new.items()});metrics[target_name]=measure
    files['PROBES.json']=encoded(dict(status='PASS',variants=metrics,
        seed_count=234,seed_choice='Complement of all admissible conclusion variables; closure is complete.',
        metadata_used_for_sign_proof=False,framework_sha256=FRAMEWORK_SHA))
    return files,metrics


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,metrics=build()
    for name,raw in files.items():
        target=DEST/name
        if args.check:need(target.read_bytes()==raw,'deterministic '+name)
        else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics=metrics),indent=2))


if __name__=='__main__':main()
