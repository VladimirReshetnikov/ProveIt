#!/usr/bin/env python3
"""Compose exact candidate-output radii with the accepted projected/radix engine."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
DEST=ROOT/'candidates/projected-factorial-radius'
ARCHIVE=REPO/'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
BASE='ConZFC_407_888_Quartics/'


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def encoded(x):return(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()


def build():
    need(digest(ARCHIVE.read_bytes())==PIN,'whole accepted incoming archive')
    with tempfile.TemporaryDirectory(prefix='projected-radius-engine-')as temporary:
        temp=Path(temporary);members={}
        with zipfile.ZipFile(ARCHIVE)as z:
            for entry in z.infolist():
                name=entry.filename
                if not name.startswith(BASE):continue
                rel=name[len(BASE):]
                # Only inspected arithmetic code plus its one source JSON.
                wanted=((rel.startswith('code/')or rel.startswith('upstream/code/')or
                         rel in {'upstream/provenance/upstream/build_equation.py',
                                 'upstream/provenance/upstream/direct_calculus.py','reproduce.py'})and rel.endswith('.py'))
                wanted|=rel=='upstream/provenance/upstream/wire_eliminated_source.json'
                if wanted:
                    raw=z.read(entry);target=temp/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
                    members[rel]=digest(raw)
        sys.path[:0]=[str(DEST),str(temp/'code'),str(temp/'code/psd_contract'),str(temp)]
        import build_projected as compiler
        import reproduce
        from radius_builder import ProjectedRadiusBuilder
        from contract import contract
        files={};census={}
        for mode,prefix in [('both','both'),('H-only','H_only')]:
            class Actual(ProjectedRadiusBuilder):pass
            Actual.radius_mode=mode;compiler.AdditiveReusedRadixBuilder=Actual
            b,source,label,local=compiler.construct()
            eq,pol,metrics=b.export(digest(source),'projected.'+prefix+'.candidate_factorial_radius',True)
            raw=reproduce.raw_record(b,label,local)
            raw.update(new_factorial_data=b.new_factorial_data,radius_mode=mode)
            source_name=prefix+'_source'
            def save(folder,e,p,extra):
                census[folder]=e['metrics']
                for name,obj in dict({'equation.json':e,'expanded_polynomial.json':p},**extra).items():files[folder+'/'+name]=encoded(obj)
            gate=dict(square_difference_gates=b.sqd_ledger,all_variables=b.variables,all_rows=b.rows,gates=b.gates)
            save(source_name,eq,pol,{'raw_builder.json':raw,'gate_ledger.json':gate})
            caps=[(4,'natural453'),(16,'natural402'),(64,'natural399')]if mode=='both'else[(64,'natural403')]
            for cap,name in caps:
                child,cert,poly=contract(eq,support_cap=cap)
                save(name,child,poly,{'elimination_certificate.json':cert})
            census[source_name]['power_index_census']={'power_calls':len(b.powers),'exponent_groups':len(b.shared_indices),
                'seed_indices':len(b.seed_indices),'derived_indices':len(b.index_derivations)}
        pins=dict(archive=str(ARCHIVE.relative_to(REPO)),archive_sha256=PIN,read_source_members=members,
                  local_override_sha256=digest((DEST/'radius_builder.py').read_bytes()),
                  ordinary_parent_review='PROPOSAL_REVIEW_QUARTICS407888.md',
                  ordinary_parent_review_sha256=digest((ROOT/'PROPOSAL_REVIEW_QUARTICS407888.md').read_bytes()),
                  changes=['Factorial radius f*n^2 for H or both calls.','For both calls radix is B*(V_H+V_t+1); for H-only it is B*(V_H+1).'],
                  frozen_parent_files_changed=False)
        files['SOURCE_PINS.json']=encoded(pins);files['CENSUS.json']=encoded(census)
        files['BUILD.json']=encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
            sha256={name:digest(raw)for name,raw in files.items()},scope='Complete literal siblings; independent identities and ordinary proof remain separate. No Lean.'))
        return files,census


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    files,census=build()
    for name,raw in files.items():
        path=DEST/name
        if args.check:need(path.read_bytes()==raw,'deterministic complete sibling '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={name:{k:v for k,v in m.items()if k in
        ['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient','exact_degree','power_index_census']}for name,m in census.items()}),indent=2))


if __name__=='__main__':main()
