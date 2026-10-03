"""Verify every copied/adapted delivered file against its recorded byte hashes.

Original hashes are authenticated against retained frozen source manifests where
available. This is an internal consistency check, not publisher authentication.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ValueError(message)

def main():
    provenance=json.loads((ROOT/'delivery-provenance.json').read_bytes())
    manifests={}
    for label,path,pin in (
        ('canonical-history-height-20261003','canonical-height/original-MANIFEST.json','3546ec269df10808a2067cea9df325709df11966b346857271e66ab4855cadce'),
        ('native-fixed-scale-fibers-20261003','native-fibers/original-MANIFEST.json','d716d6dc668547ee5d64dfe77620b66f93ab839f95e0261250c2a387b5338dca')):
        raw=(ROOT/path).read_bytes();require(sha256(raw).hexdigest()==pin,'original manifest pin: '+label)
        manifests[label]=(path,pin,json.loads(raw)['files'])
    copied=adapted=0
    for name,row in provenance['files'].items():
        require(not Path(name).is_absolute() and '..' not in Path(name).parts,'invalid provenance path')
        raw=(ROOT/name).read_bytes();require(sha256(raw).hexdigest()==row['delivered_sha256'] and len(raw)==row['delivered_bytes'],'delivered provenance mismatch: '+name)
        require(row['adapted']==(row['original_sha256']!=row['delivered_sha256']),'adaptation classification differs: '+name)
        if row['source_packet'] in manifests:
            manifest_path,pin,entries=manifests[row['source_packet']]
            original=row['source_relative_path']
            if original=='MANIFEST.json':require(row['original_sha256']==pin,'original manifest provenance differs')
            else:
                entry=entries[original];require(row['original_sha256']==entry['sha256'] and row['original_bytes']==entry['bytes'],'original source manifest differs: '+name)
        elif row['source_packet']=='Report21 reproducibility/source':
            if row['source_relative_path']!='provenance.json':
                entry=json.loads((ROOT/'inherited-source/provenance.json').read_bytes())['sources'][row['source_relative_path']]
                require(row['original_sha256']==entry['sha256'] and row['original_bytes']==entry['bytes'],'inherited source provenance differs: '+name)
        else:raise ValueError('unknown source packet')
        adapted+=int(row['adapted']);copied+=int(not row['adapted'])
    for name,row in provenance['omitted_canonical_files'].items():
        entry=manifests['canonical-history-height-20261003'][2][name]
        require(row['original_sha256']==entry['sha256'] and row['bytes']==entry['bytes'],'omitted source metadata differs')
    for sub in ('canonical-height','native-fibers'):
        folder=ROOT/sub;manifest=json.loads((folder/'MANIFEST.json').read_bytes())
        entries=manifest['files'];actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p.relative_to(folder).as_posix()!='MANIFEST.json'}
        require(actual==set(entries),'portable payload file inventory differs: '+sub)
        for name,entry in entries.items():
            raw=(folder/name).read_bytes();require(sha256(raw).hexdigest()==entry['sha256'] and len(raw)==entry['bytes'],'portable payload hash differs: '+sub+'/'+name)
    print(json.dumps({'status':'passed','byte_identical_copies':copied,'documented_portable_adaptations':adapted,'explicitly_omitted_duplicate_canonical_files':len(provenance['omitted_canonical_files']),'portable_payload_manifests':2},indent=2))

if __name__=='__main__':main()
