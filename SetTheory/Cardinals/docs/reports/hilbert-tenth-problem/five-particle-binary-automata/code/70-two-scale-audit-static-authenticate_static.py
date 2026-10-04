#!/usr/bin/env python3
"""Fresh hash/inventory/numeric audit only; no imported packet code, no CA steps."""
import hashlib, io, json, pathlib, stat, zipfile
BASE = pathlib.Path('/workspace/shared/radius-frontier-20261004')
OUT = BASE/'fresh-audit-static'
PACKET = BASE/'proof-packet'
def sha(b): return hashlib.sha256(b).hexdigest()
def load(b):
    def pairs(kv):
        result={}
        for k,v in kv:
            if k in result: raise ValueError('duplicate JSON key '+k)
            result[k]=v
        return result
    return json.loads(b,object_pairs_hook=pairs)
def snapshot():
    roots=[PACKET,BASE/'two-scale-recognition-proof-packet-20261004.zip',BASE/'archive',BASE/'inert',BASE/'proof-packet-freeze-receipt.json']
    out={}
    for root in roots:
        for p in [root]+(sorted(root.rglob('*')) if root.is_dir() else []):
            s=p.lstat()
            assert not stat.S_ISLNK(s.st_mode)
            entry={'type':'directory' if p.is_dir() else 'file','mode_octal':oct(stat.S_IMODE(s.st_mode)),'mtime_ns':s.st_mtime_ns}
            if p.is_file(): entry.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
            out[str(p.relative_to(BASE))]=entry
    return out
before=snapshot()
baseline=OUT/'original-state-before.json'
if baseline.exists(): assert load(baseline.read_bytes())==before, 'original metadata/bytes changed since prior audit snapshot'
else: baseline.write_text(json.dumps(before,indent=2,sort_keys=True)+'\n')
expected={'two-scale-recognition-proof-packet-20261004.zip':'a3739bdd0d9015ea4c69f3a0b8b8fb6f0bd6828a6aa5251a08e902a1ca3d04b6','proof-packet/PROOF.md':'9eb76ef7142a98b67e90cceb209f16af0b1f1057adfb30ddedfcb6e97b6616c2','proof-packet/INDEPENDENT_AUDIT.md':'076de66d7e6ffba255df3d64f58a0e2df48ac215b6a781718efd070c18b300f6','proof-packet/original/report26.zip':'20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4'}
for rel,d in expected.items(): assert sha((BASE/rel).read_bytes())==d,rel
manifest=load((PACKET/'manifest.json').read_bytes())
for rel,data in manifest['files'].items():
    b=(PACKET/rel).read_bytes(); assert sha(b)==data['sha256'] and len(b)==data['bytes'],rel
assert {str(p.relative_to(PACKET)) for p in PACKET.rglob('*') if p.is_file()}==set(manifest['files'])|{'manifest.json'}
outer=zipfile.ZipFile(BASE/'two-scale-recognition-proof-packet-20261004.zip')
def entries(z):
    names=z.namelist(); assert len(names)==len(set(names))
    for info in z.infolist():
        p=pathlib.PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert not stat.S_ISLNK(info.external_attr>>16)
    return {i.filename:z.read(i.filename) for i in z.infolist() if not i.is_dir()}
outer_files=entries(outer)
print('Outer first member:',next(iter(outer_files)))
# Locate the packet prefix by PROOF plus content digest, not guessed archive layout.
prefixes=[n[:-len('PROOF.md')] for n,b in outer_files.items() if n.endswith('/PROOF.md') and sha(b)==expected['proof-packet/PROOF.md']]
assert len(prefixes)==1
prefix=prefixes[0]
assert set(outer_files)=={prefix+str(p.relative_to(PACKET)) for p in PACKET.rglob('*') if p.is_file()}
for n,b in outer_files.items(): assert b==(PACKET/n[len(prefix):]).read_bytes(),n
original_bytes=(PACKET/'original/report26.zip').read_bytes()
assert original_bytes==(BASE/'archive/Two_Parallel_Conservative_Involutions_Package.zip').read_bytes()
z=zipfile.ZipFile(io.BytesIO(original_bytes)); oz=entries(z); pre='parallel-involution-report26/'
release=load(oz[pre+'release-manifest.json'])
assert set(oz)=={pre+n for n in release['files']}|{pre+'release-manifest.json',pre+'release-manifest.json.sha256'}
for n,data in release['files'].items():
    b=oz[pre+n]; assert sha(b)==data['sha256'] and len(b)==data['bytes'],n
seal=oz[pre+'release-manifest.json.sha256'].decode().split()[0]
assert sha(oz[pre+'release-manifest.json'])==seal
pins=load(oz[pre+'source-pins.json'])['files']
for n,d in pins.items(): assert sha(oz[pre+n])==d,n
scientific=load(oz[pre+'scientific/manifest.json'])['files']
for n,data in scientific.items():
    b=oz[pre+'scientific/'+n]; assert sha(b)==data['sha256'] and len(b)==data['bytes'],n
for line in oz[pre+'scientific/SHA256SUMS'].decode().splitlines():
    d,n=line.split(); assert sha(oz[pre+'scientific/'+n])==d,n
mapping={'COMPILER_PROOF.md':'scientific/COMPILER_PROOF.md','PROOF.md':'scientific/PROOF.md','audit-preservation.md':'scientific/audit-preservation.md','prior-art-audit.md':'references/prior-art-audit.md','release-manifest.json':'release-manifest.json','report19-audit-universal-count.json':'references/report19-audit-universal-count.json','report19-universal-receipt.json':'references/report19-universal-receipt.json','resource-ledger.json':'scientific/resource-ledger.json','source-pins.json':'source-pins.json'}
for n,on in mapping.items(): assert (PACKET/'dependencies'/n).read_bytes()==oz[pre+on],n
# Independent resource arithmetic only, no template generation or source interpreter.
ledger=load((PACKET/'resource-ledger.json').read_bytes())
checks={}
for name,row in ledger['examples'].items():
    D,J=row['D'],row['J']; b=4*D+5; a=3*b+1; Z=10*b+10+2*J; r=Z+J
    H=max(2*(b+a),b+r)
    calculated={'b':b,'recognition_radius':a,'control_radius':r,'Z':Z,'new_exclusion':H,'new_edge_radius':b+a+H,'unchanged_phase_radius':12*b+3,'new_total_radius':108*D+149+3*J,'report26_total_radius':180*D+258+9*J,'reduction':72*D+109+6*J}
    for k,v in calculated.items(): assert row[k]==v,(name,k,v,row[k])
    assert calculated['new_total_radius']==calculated['new_edge_radius']+calculated['unchanged_phase_radius']
    checks[name]=calculated
receipt=load(oz[pre+'references/report19-universal-receipt.json'])
u=receipt['ledger']; D=2*u['m']+4*u['p']; assert D==u['D']==509508
assert 8*u['p']*D+29*u['p']+u['m']+u['a']==u['factors']==269291358255
assert receipt['source_sha256']=='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'
assert all(sha(b)!=receipt['source_sha256'] for b in oz.values())
after=snapshot(); assert before==after
(OUT/'original-state-after.json').write_text(json.dumps(after,indent=2,sort_keys=True)+'\n')
report={'passed':True,'kind':'fresh-inert-authentication-and-numeric-ledger-only','trusted_expected_digests':expected,'originals_unchanged_bytes_modes_mtimes':True,'snapshot_entries':len(before),'packet_manifest_files_verified':len(manifest['files']),'outer_zip_files_verified':len(outer_files),'original_zip_files_verified':len(oz),'original_release_manifest_files_verified':len(release['files']),'original_source_pins_verified':len(pins),'original_scientific_manifest_files_verified':len(scientific),'dependency_byte_copies_verified':len(mapping),'universal_source_table_present':False,'universal_source_sha256_in_inherited_receipt':receipt['source_sha256'],'resource_checks':checks,'executed_archive_or_packet_programs':False}
(OUT/'authentication-receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2))
