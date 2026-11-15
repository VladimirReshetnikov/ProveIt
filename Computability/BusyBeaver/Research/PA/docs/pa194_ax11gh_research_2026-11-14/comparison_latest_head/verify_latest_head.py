#!/usr/bin/env python3
"""Check the late-HEAD graph delta offline; execute no archived generator.

The baseline comparison directory must be the retained110-class comparison.
The complete new source ZIP is read as inert data. Optional --repository
also rechecks the four-packet relocation and the110 HEAD retention witnesses.
"""
from pathlib import Path
import argparse, collections, hashlib, importlib.util, io, json, subprocess, sys, zipfile
ROOT=Path(__file__).resolve().parent

def sha(b): return hashlib.sha256(b).hexdigest()
def load(name): return json.loads((ROOT/name).read_text())
def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def main():
    assert __debug__, 'Run without -O or PYTHONOPTIMIZE.'
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline',type=Path,default=ROOT.parent/'comparison')
    p.add_argument('--repository',type=Path)
    p.add_argument('--receipt',type=Path)
    args=p.parse_args();base=args.baseline;a=module(base/'audit.py','historical_audit')
    for r in load('MANIFEST.json')['files']:
        data=(ROOT/r['path']).read_bytes()
        assert len(data)==r['bytes'] and sha(data)==r['sha256'],r['path']
    expected=load('summary.json');prov=load('PROVENANCE.json')
    archive=(ROOT/'source_archive'/prov['archive_path'].split('/')[-1]).read_bytes()
    assert sha(archive)==prov['archive_sha256']
    assert hashlib.sha1(b'blob '+str(len(archive)).encode()+b'\0'+archive).hexdigest()==prov['archive_git_blob_sha1']
    rows_by_hash={};occ=[];errors=[];payloads=0;seen_zip=set()
    def add(loc,item,source_sha):
        rows,states,start,declared=item;normalized=a.table_bytes(rows);h=sha(normalized)
        rows_by_hash.setdefault(h,(rows,states))
        occ.append({'locator':loc,'normalized_sha256':h,'source_sha256':source_sha})
    def inspect(data,loc):
        nonlocal payloads
        payloads+=1;h=sha(data)
        if loc.endswith('.zip'):
            if h in seen_zip:return
            seen_zip.add(h)
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for n in z.namelist():
                    if n.endswith(('.tm','.json','.zip')):inspect(z.read(n),loc+'!'+n)
        elif loc.endswith('.tm'):
            try:add(loc,a.parse(data),h)
            except (ValueError,UnicodeError) as e:errors.append({'locator':loc,'error':repr(e)})
        elif loc.endswith('.json'):
            for sub,item in a.json_tables(json.loads(data)):add(loc+'#'+sub,item,h)
    inspect(archive,prov['archive_path'])
    assert payloads==420 and len(occ)==116 and len(rows_by_hash)==110
    assert errors==expected['errors']
    bindings=load('source_table_bindings.json')
    expected_occ={(x['locator'],x['normalized_sha256'],x['source_sha256']) for x in bindings if not x.get('excluded')}
    assert {(x['locator'],x['normalized_sha256'],x['source_sha256']) for x in occ}==expected_occ
    for x in bindings:
        b=(ROOT/x['bundled_file']).read_bytes()
        assert sha(b)==x['source_sha256'] and len(b)==x['bytes']
    historical=json.loads((base/'classes.json').read_text());designs=json.loads((base/'designs194.json').read_text())
    historical_paths={x['canonical_class']:base/x['representative_file'] for x in designs}
    classes={};old_tuples={};broad=[]
    for i,(h,(rows,states)) in enumerate(rows_by_hash.items()):
        ordinary=a.canonical(rows,states);assert ordinary is not None
        ch=sha(a.encode(ordinary))
        assert ch in historical and historical[ch]['states']==len(states),(ch,len(states))
        if ch in classes:continue
        classes[ch]=len(states)
        if len(states)==194:
            old_rows,old_states,_,_=a.parse(historical_paths[ch].read_bytes())
            old=a.canonical(old_rows,old_states)
            assert ordinary==old,'Exact ordinary tuple differs from retained historical representative'
            strong=min(a.canonical(rows,states,mirror=m,flip=f,loose=True)
                       for m in (False,True) for f in (False,True))
            broad.append(strong)
        if len(classes)%25==0:print('Delta graph classes checked:',len(classes),flush=True)
    assert len(classes)==102 and collections.Counter(classes.values())=={193:2,194:96,201:4}
    candidate_results={}
    for name in ('PA194AX11GH','PA194AX11GHS'):
        data=(base/'candidates'/(name+'.tm')).read_bytes();rows,states,start,declared=a.parse(data)
        ordinary=a.canonical(rows,states)
        strong=min(a.canonical(rows,states,mirror=m,flip=f,loose=True)
                   for m in (False,True) for f in (False,True))
        assert strong not in broad
        assert sha(data)==expected['candidates'][name]['sha256']
        candidate_results[name]={'states':len(states),'sha256':sha(data),'matches_new_archive':[]}
    persistence=load('head_persistence.json')
    original194={k for k,v in historical.items() if v['states']==194}
    assert set(persistence['witnesses'])==original194 and len(original194)==110
    assert not persistence['missing']
    packets=load('packets87.json')
    assert len(packets)==87 and collections.Counter(x['filed_or_incoming'] for x in packets)=={'filed':86,'incoming':1}
    git_rechecked=False
    if args.repository:
        relocation=module(ROOT/'check_latest_delta_relocation.py','relocation_check')
        fresh=relocation.audit(args.repository,expected['original_pin'],expected['latest_head'])
        assert fresh==load('latest_delta_relocation_audit.json')
        tree={}
        for line in subprocess.check_output(['git','ls-tree','-r',expected['latest_head']],cwd=args.repository,text=True).splitlines():
            meta,path=line.split('\t',1);tree[path]=meta.split()[2]
        for x in persistence['witnesses'].values():
            assert tree[x['head_top_level_path']]==x['head_git_blob']
        git_rechecked=True
    result={'status':'PASS','original_pin':expected['original_pin'],'late_head':expected['latest_head'],
            'baseline_194_classes':110,'baseline_deliveries':86,'latest_194_classes':110,'latest_deliveries':87,
            'latest_filed':86,'latest_incoming':1,'new_archive_recognized_occurrences':116,
            'new_archive_labeled_tables':110,'new_archive_classes':102,'new_archive_194_classes':96,
            'new_archive_193_classes':2,'new_archive_new_classes':0,'exact_194_tuple_subset_checked':True,
            'candidate_broad_tuple_comparisons_checked':True,'candidates':candidate_results,
            'arithmetic_calibration_checked':False,'archived_generators_executed':False,
            'git_relocation_and_retention_rechecked':git_rechecked}
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
