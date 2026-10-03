"""Authenticate every delivered source copy/adaptation without executing source code."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import json
from verify_release import ROOT, check_pins, load_json, require, relative_name


def main():
    check_pins(ROOT)
    provenance = load_json((ROOT/'delivery-provenance.json').read_bytes())
    require(set(provenance) == {'schema','date','scope','source_packets','files','omitted','evidence_boundary'}, 'provenance shape')
    require(provenance['schema'] == 'report25-delivery-provenance-v1', 'provenance schema')
    manifests = {}
    manifest_names = {}
    for packet, info in provenance['source_packets'].items():
        relative_name(info['manifest'])
        raw = (ROOT/info['manifest']).read_bytes()
        require(sha256(raw).hexdigest() == info['manifest_sha256'], 'original manifest hash: '+packet)
        manifest_names[packet] = info['manifest']
        if info['format'] == 'json-files':
            manifests[packet] = load_json(raw)['files']
        elif info['format'] == 'sha256-lines':
            entries = {}
            for line in raw.decode('utf-8').splitlines():
                digest, name = line.split('  ',1)
                relative_name(name)
                require(name not in entries, 'duplicate original SHA entry')
                require(len(digest)==64 and all(c in '0123456789abcdef' for c in digest),'bad original SHA')
                entries[name] = {'sha256': digest}
            manifests[packet] = entries
        else:
            raise ValueError('unknown original manifest format')
    delivered = set()
    for record in provenance['files']:
        require(set(record)=={'packet','original_name','delivered_name','original_sha256','delivered_sha256','original_bytes','delivered_bytes','adaptation'},'copy record shape')
        name = relative_name(record['delivered_name'])
        original_name = relative_name(record['original_name'])
        require(name not in delivered, 'duplicate delivered provenance record: '+name)
        delivered.add(name)
        raw = (ROOT/name).read_bytes()
        require(len(raw)==record['delivered_bytes'] and sha256(raw).hexdigest()==record['delivered_sha256'],'delivered provenance mismatch: '+name)
        packet = record['packet']
        if name == manifest_names[packet]:
            require(record['original_sha256']==record['delivered_sha256'] and record['original_bytes']==record['delivered_bytes'],'original manifest must be unchanged')
        else:
            original = manifests[packet].get(original_name)
            require(type(original) is dict, 'source is absent from original manifest: '+original_name)
            require(original['sha256']==record['original_sha256'],'original source hash mismatch: '+original_name)
            if 'bytes' in original:
                require(original['bytes']==record['original_bytes'],'original source length mismatch')
        require(type(record['adaptation']) is str and bool(record['adaptation']), 'missing adaptation disclosure')
    from verify_release import SOURCE_PINS
    expected = set(SOURCE_PINS)-{'delivery-provenance.json','check_provenance.py','check_privacy.py'}
    require(delivered == expected, 'provenance coverage differs from mandatory scientific corpus')
    print(json.dumps({'status':'PASS','source_packets':len(manifests),'authenticated_copies_or_adaptations':len(delivered),'all_mandatory':True,'source_python_executed':False},indent=2))


if __name__ == '__main__':
    main()
