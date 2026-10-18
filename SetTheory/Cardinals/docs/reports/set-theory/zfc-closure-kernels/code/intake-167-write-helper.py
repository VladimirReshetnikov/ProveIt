#!/usr/bin/env python3
"""Stage the pinned batch167 reconciliation in a NEW external directory.

Only copies reviewed prose and existing evidence. Never runs supplied programs,
proofs, builds, searches, Git mutations or repository installation. Root reviews
and installs the explicit output map separately. Only host README is replaceable.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json

HOST = 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
def require(ok, message):
    if not ok: raise ValueError(message)
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path): return json.loads(Path(path).read_text())
def relative(name):
    p = PurePosixPath(name)
    require(p.parts and not p.is_absolute() and '..' not in p.parts and
            not any(x in name for x in ['\\', ':', '\n', '\r']), 'Unsafe target ' + name)
    return p

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--inputs', type=Path, default=Path(__file__).with_name('write-inputs.json'))
    ap.add_argument('--inputs-sha', required=True)
    args = ap.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    require(not output.exists() and output != repo and repo not in output.parents, 'Output must be new and external')
    require(sha(args.inputs) == args.inputs_sha, 'Wrong frozen inputs manifest')
    p = read(args.inputs)
    require(p['status'] == 'READY_FOR_ROOT_SOURCE_REVIEW' and p['batch'] == 167 and p['host_source'] == 71, 'Wrong write scope')
    require(p['placement'].startswith('5513e77ff1'), 'Wrong placement')
    require(sha(repo / p['base_article']['path']) == p['base_article']['sha256'], 'Base article changed')
    require(sha(p['placement_map']['path']) == p['placement_map']['sha256'], 'Placement map changed')
    plan = read(p['placement_map']['path'])
    rows = [r for r in plan['files'] if r['disposition'] == 'place_unchanged']
    require(len(rows) == 1007 and len(plan['files']) == 1044, 'Wrong placement census')
    for row in rows:
        require(sha(repo / row['target']) == row['sha256'], 'Placed ancillary changed: ' + row['target'])
    targets = set()
    for row in p['files']:
        src = Path(row['source'])
        require(src.is_file() and sha(src) == row['sha256'] and src.stat().st_size == row['bytes'], 'Changed input ' + str(src))
        relative(row['target'])
        require(row['target'].startswith(HOST + '/') and row['target'] not in targets, 'Out-of-scope or duplicate target')
        targets.add(row['target'])
        dest = repo / row['target']
        require(repo in dest.resolve().parents, 'Escaping repository target')
        if 'replace_before_sha256' in row:
            require(row['target'] == HOST + '/README.md' and sha(dest) == row['replace_before_sha256'], 'README baseline changed')
        else:
            require(not dest.exists() and not dest.is_symlink(), 'New target exists: ' + str(dest))
    # The manifest pins every record read here; gates retain distinct executed scopes.
    for desc in p['records'].values():
        require(sha(desc['path']) == desc['sha256'], 'Record changed: ' + desc['path'])
    records = {k: read(v['path']) for k,v in p['records'].items()}
    q = records['primary']
    require(q['status'] == 'PASS_ROOT_ROTATION244_PRIMARY_REPLAY' and len(q['jobs']) == 7 and
            all(j['returncode'] == 0 and not j['timeout'] for j in q['jobs']) and
            q['cases'] == 8390 and q['symbolic_rules'] == 2312438 and q['blank_steps'] == 407931, 'Wrong primary outcome')
    x = records['expanded']
    require(x['status'] == 'PASS_UNIVERSAL_EXPANDED_RUNTIME' and x['complete'] and x['positive_progress_checked'] and
            x['arbitrary_primary_registers'] and x['arbitrary_nonempty_finite_spare_suffix'] and
            x['counts'] == {'cases':8390,'symbolic_rules':2312438} and x['literal_rows_covered'] == 487 and
            x['unused_rows'] == [[27,1]], 'Wrong expanded scope')
    a = records['auxiliary']; l = records['logical']
    require(len(a['jobs']) == 15 and all(j['exit_code'] == 0 and not j['timed_out'] for j in a['jobs']) and
            l['status'] == 'PASS' and l['returncode'] == 0 and not l['timeout'], 'Auxiliary command incomplete')
    for key,status in [('primary_review','EXISTING_ROOT_PRIMARY_REPLAY_REVIEW_PASS'),
                       ('auxiliary_review','EXISTING_ROOT_AUXILIARY_OUTPUT_REVIEW_PASS'),
                       ('combined_review','EXISTING_EXPANDED_REPLAY_EVIDENCE_REVIEW_PASS')]:
        require(records[key]['status'] == status and records[key]['findings'] == [], 'Review did not pass: ' + key)
    for review_key, record_key, field in [('primary_review','primary','verification'),
                                         ('auxiliary_review','auxiliary','execution'),
                                         ('combined_review','combined','verification')]:
        require(records[review_key][field]['sha256'] == p['records'][record_key]['sha256'], 'Review/record binding differs')
    c = records['combined']
    require(c['status'] == 'PASS_COMBINED243_EXPANDED_RUNTIME' and c['counts'] == {'cases':8390,'symbolic_rules':2314868}
            and c['rows_covered'] == 485 and c['unused_rows'] == [[27,1]] and c['before'] == c['after'] and
            all(j['exit_code'] == 0 and not j['timeout'] for j in c['commands']), 'Combined record incomplete')
    for path,digest in c['before'].items(): require(sha(path) == digest, 'Combined input changed: ' + path)
    r = records['recovery']
    require(r['status'] == 'RECOVERED_AND_PLACED_BYTES_MATCH' and r['files_recovered'] == 1044 and
            r['placed_pairs_compared'] == 1007 and r['archive_only'] == 37, 'Wrong recovery outcome')
    output.mkdir()
    result = []
    for row in p['files']:
        dest = output / 'files' / row['target']; dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(Path(row['source']).read_bytes())
        require(sha(dest) == row['sha256'], 'Staged byte mismatch')
        result.append(dict(row, source=str(dest)))
    target = HOST + '/data/intake-167-write-inputs.json'
    require(target not in targets and not (repo / target).exists(), 'Inputs provenance target exists')
    dest = output / 'files' / target; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(args.inputs.read_bytes())
    result.append({'source':str(dest),'target':target,'sha256':args.inputs_sha,'bytes':dest.stat().st_size,
                   'role':'exact frozen write inputs, original paths and history mapping'})
    for row in p['files']: require(sha(row['source']) == row['sha256'], 'Source changed during staging')
    require(sha(args.inputs) == args.inputs_sha, 'Inputs changed during staging')
    record = {'status':'STAGED_FOR_ROOT_REVIEW_NOT_INSTALLED','batch':167,'placement':p['placement'],
              'host_sources':71,'collection_reports':290,'files':result,'input_manifest_sha256':args.inputs_sha,
              'builder_sha256':sha(__file__),'base_article':p['base_article'],'maintained_mutations':False,
              'supplied_or_proof_execution':False,'catalogue_pending_separate_step':True}
    (output/'publication-map.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'files':len(result),'map':str(output/'publication-map.json')}))

if __name__ == '__main__': main()
