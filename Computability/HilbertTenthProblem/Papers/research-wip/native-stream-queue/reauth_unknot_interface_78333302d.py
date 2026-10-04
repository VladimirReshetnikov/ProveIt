#!/usr/bin/env python3
"""Fresh read-only authentication; no original review/recognizer code is loaded."""
from pathlib import Path
import argparse, hashlib, json, subprocess

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
SOURCE=Path('/tmp/review_unknot_interface_78333302d')
OUTPUT=Path('/tmp/reauth_unknot_interface_78333302d.json')
PINS={'md':'3b90ea02fa0b192d30c3d2c72036e25a672eaed293a00e459d7a365cbbf7b6a8',
      'json':'da5e6ed5a8ef9c507197957739cec761e24790ff5694db75757386e3ae667930',
      'py':'802ae783c28d8b9024d3bd157c577f4e56139195c6a97e346cb2d07e44caea91'}

def require(ok,message):
    if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--expect',type=Path);args=ap.parse_args()
    frozen=[]
    for suffix,expected in PINS.items():
        p=SOURCE.with_suffix('.'+suffix);b=p.read_bytes()
        require(sha(b)==expected,'frozen '+suffix+' pin')
        frozen.append({'path':str(p),'bytes':len(b),'sha256':sha(b)})
    r=json.loads(SOURCE.with_suffix('.json').read_bytes())
    require(r['collector_sha256']==PINS['py'],'receipt binds original collector')
    commit=r['revision'];parent=git('rev-parse',commit+'^').decode().strip()
    require(parent==r['parent'],'parent commit')
    require(commit=='78333302d9babf0efb1a5d218e122f13c35bb306','immutable revision')
    records=[];line_total=span_total=span_bytes=0
    for rec in r['records']:
        path=rec['path'];b=git('show',commit+':'+path)
        oid=git('rev-parse',commit+':'+path).decode().strip()
        require(oid==rec['blob'],'blob '+path)
        require(len(b)==rec['bytes'],'bytes '+path)
        require(sha(b)==rec['sha256'],'hash '+path)
        lines=b.splitlines(keepends=True)
        require(len(lines)==rec['lines'],'line count '+path)
        reads=[]
        for s in rec['read_spans']:
            a,z=s['first'],s['last'];require(1<=a<=z<=len(lines),'span bounds')
            part=b''.join(lines[a-1:z])
            require(len(part)==s['bytes'] and sha(part)==s['sha256'],'span bytes/hash '+path)
            reads.append({'first':a,'last':z,'bytes':len(part),'sha256':sha(part)})
            line_total+=z-a+1;span_total+=1;span_bytes+=len(part)
        records.append({'commit':commit,'path':path,'blob':oid,'bytes':len(b),'sha256':sha(b),
                        'lines':len(lines),'read_spans':reads})
    require(len(records)==3 and span_total==6,'three files/six spans')
    require(line_total==r['read_line_total']==546,'546 lines')
    require(r['scope']=={'read_guides':2,'selected_report_spans':4,'complete_report_read':False,
                        'source_implementation_read':False,'archive_inventory':False,'external_source_verification':False,
                        'builds_or_predecessor_execution':False},'scope flags')
    result={'schema':'independent bounded knot-interface reauthentication v1','status':'PASS',
            'reviewer_helper_sha256':sha(Path(__file__).read_bytes()),'frozen_inputs':frozen,
            'revision':commit,'parent':parent,'reauthenticated_records':records,
            'totals':{'files':len(records),'spans':span_total,'read_lines':line_total,'span_bytes':span_bytes,
                      'full_file_bytes':sum(x['bytes'] for x in records)},
            'human_scope':'Full frozen review MD and all six recorded immutable source spans read; original collector bytes only.',
            'mathematical_assessment':{'conditional_total_decider_composition':'PASS',
              'conditional_quasipolynomial_iteration_count':'PASS',
              'topology_or_implementation_certification':False},
            'limits':['No proof audit of topology, recognizer implementations, external papers or omitted report sections.',
                      'No archive inventory, cross-validation, benchmark, PDF/build or prior-helper execution.',
                      'Original historical working-byte equality is not independently reconstructed; this pass authenticates immutable blobs and recorded spans.',
                      'No new ordinary-integer compiler or universal-operation bound.'],
            'execution':'Only this new standard-library metadata program ran, with read-only Git calls; no report or predecessor program imported/executed and no repository mutation.'}
    data=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
    if args.expect:require(args.expect.read_bytes()==data,'exact receipt replay')
    else:OUTPUT.write_bytes(data)
    print(json.dumps({'status':'PASS','receipt_sha256':sha(data),**result['totals']},sort_keys=True))

if __name__=='__main__':main()
