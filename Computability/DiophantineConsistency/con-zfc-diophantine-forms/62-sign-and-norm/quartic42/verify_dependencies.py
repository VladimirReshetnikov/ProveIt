#!/usr/bin/env python3
"""Offline source, coefficient, and exact lift-chain replay; standard library.

This checks finite data and identities.  It does not mechanically prove the
unbounded Pell/compiler or machine-calibration theorems.
"""
import gzip
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from build_verify import polynomial, require

ROOT = Path(__file__).resolve().parent
DEPS = ROOT / 'dependencies'


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def blob_hash(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def authentic_sources():
    records = read_json(DEPS/'SOURCE_PINS.json')
    for rec in records:
        data = (DEPS/rec['local_path']).read_bytes()
        require(len(data) == rec['size'], 'Source size: '+rec['local_path'])
        require(sha256(data) == rec['sha256'], 'Source SHA256: '+rec['local_path'])
        require(blob_hash(data) == rec['git_blob'], 'Source Git blob: '+rec['local_path'])
    parents = read_json(ROOT/'SOURCE_PINS.json')
    for rec in parents:
        data = (ROOT/rec['local_path']).read_bytes()
        require(len(data) == rec['byte_size'], 'Upstream size: '+rec['local_path'])
        require(sha256(data) == rec['sha256'], 'Upstream SHA256: '+rec['local_path'])
        require(blob_hash(data) == rec['git_blob_sha1'], 'Upstream Git blob: '+rec['local_path'])
    return len(records)+len(parents)


def coefficients():
    directory = DEPS/'source34/coefficients'
    payloads = directory/'payloads'
    binding = read_json(payloads/'COEFFICIENT_BINDING.json')
    require(binding['variant'] == 'mixed-parity-unrounded-1064921', 'Wrong whole tuple')
    require(set(binding['payloads']) == {'beta','K','MC','MF_source'}, 'Wrong tuple ports')
    sizes = {}
    for name, rec in binding['payloads'].items():
        raw = (payloads/(name+'.bin')).read_bytes()
        compressed = (payloads/(name+'.bin.gz')).read_bytes()
        require(len(raw) == rec['bytes'] and sha256(raw) == rec['sha256'], 'Raw '+name)
        require(len(compressed) == rec['gzip_bytes']
                and sha256(compressed) == rec['gzip_sha256'], 'Gzip '+name)
        require(gzip.decompress(compressed) == raw, 'Decompression '+name)
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == rec['bits'], 'Bit length '+name)
        require(value.to_bytes((value.bit_length()+7)//8, 'little') == raw,
                'Minimal unsigned little-endian '+name)
        sizes[name] = {'raw_bytes':len(raw), 'gzip_bytes':len(compressed)}
    require(int.from_bytes((payloads/'beta.bin').read_bytes(), 'little')
            == (1 << 1064921)-1, 'Fixed radix')
    with tempfile.TemporaryDirectory(prefix='q42_coeff_replay_') as tmp:
        result = subprocess.run([sys.executable, str(directory/'build_coefficients.py'),
                                 '--output', tmp], check=True, capture_output=True, text=True)
        built = json.loads(result.stdout)
        require(built['status'] == 'PASS', 'Coefficient construction')
        for name in binding['payloads']:
            require((Path(tmp)/(name+'.bin')).read_bytes()
                    == (payloads/(name+'.bin')).read_bytes(), 'Regenerated numeral '+name)
    decoded = subprocess.run([sys.executable, str(directory/'verify_independent.py'),
                              '--payloads', str(payloads)],
                             check=True, capture_output=True, text=True)
    decoder = json.loads(decoded.stdout)
    require(decoder['status'] == 'PASS' and not decoder['imports_builder'],
            'Independent actual-coefficient decoding')
    packet = read_json(ROOT/'quartic42.json')
    active = packet['coefficient_binding']
    require((ROOT/active['compiler_manifest']).resolve()
            == (payloads/'COEFFICIENT_BINDING.json').resolve(), 'Active payload path')
    require(active['ports'] == {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
            'Whole-tuple alias binding')
    require((ROOT/active['manifest']).is_file() and (ROOT/active['transfer_proof']).is_file(),
            'Active proof and interface paths')
    return {'tuple':'mixed-parity-unrounded-1064921', 'sizes':sizes,
            'raw_bytes':sum(v['raw_bytes'] for v in sizes.values()),
            'gzip_bytes':sum(v['gzip_bytes'] for v in sizes.values()),
            'all_four_numerals_regenerated_exactly':True, 'independent_decoder':decoder}


def substitute(expr, name, value):
    return re.sub(r'\b'+re.escape(name)+r'\b', '('+value+')', expr)


def lift_chain():
    q54_path = DEPS/'29-simpler-forms/integer54_quartic.json'
    q51_path = DEPS/'source34/low_degree/upstream/integer51_degree4_odd_scale.json'
    q50_path = DEPS/'source34/low_degree/quartic50.json'
    q45_path = ROOT/'upstream/quartic45.json'
    q54, q51, q50, q45 = map(read_json, (q54_path,q51_path,q50_path,q45_path))
    for child, parent_path in ((q51,q54_path),(q50,q51_path),(q45,q50_path)):
        require(child['parent_sha256'] == sha256(parent_path.read_bytes()),
                'Exact recorded parent hash: '+str(parent_path))
    ports = q51['fixed_numerals']
    symbols = q54['variables']+['v_scale']+ports
    removed = q51['deleted_parent_residual_index_zero_based']
    require(removed == 28, 'Odd-scale deleted guard')
    guard = 's-1-s_pos1**2-s_pos2**2-s_pos3*(s_pos3+1)'
    require(polynomial(q54['residuals'][removed], symbols) == polynomial(guard, symbols),
            'Exact old scale guard')
    converted = [substitute(e,'s','2*v_scale+1') for i,e in enumerate(q54['residuals'])
                 if i != removed]
    require(len(converted) == len(q51['residuals']) == 30, 'Odd-scale row count')
    for i,(a,b) in enumerate(zip(converted,q51['residuals'])):
        require(polynomial(a,symbols) == polynomial(b,symbols), 'Odd-scale row '+str(i))
    require(set(q51['variables'])
            == (set(q54['variables'])-{'s','s_pos1','s_pos2','s_pos3'})|{'v_scale'},
            'Odd-scale variable change')

    symbols = q51['variables']+ports
    q = '(beta*J+1)'
    C = '('+q+'-F-alpha)'
    gvalue = q+'*('+q+'-F)-'+C
    require(polynomial(q51['residuals'][12],symbols)
            == polynomial('G-('+gvalue+')',symbols), 'G definition')
    require(polynomial('('+substitute(q51['residuals'][13],'G',gvalue)+')-('
                       +q50['residuals'][12]+')-('+q+'-F)*('
                       +q51['residuals'][1]+')',symbols) == {}, 'Packing identity')
    for old,new in [(i,i) for i in range(12)]+[(i,i-1) for i in range(14,30)]:
        require(polynomial(q51['residuals'][old],symbols)
                == polynomial(q50['residuals'][new],symbols), 'Retained Q50 row '+str(old))
    require(q50['variables'] == [v for v in q51['variables'] if v != 'G'], 'G removal')

    symbols = list(dict.fromkeys(q50['variables']+q45['variables']+ports))
    for old,new in [(i,i) for i in range(23)]+[(27,23),(28,24)]:
        require(polynomial(q50['residuals'][old],symbols)
                == polynomial(q45['residuals'][new],symbols), 'Retained Q45 row '+str(old))
    expected = [q+'-2*q_half_root**2',
                'F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)',
                'F*'+C+'-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)']
    for i,e in enumerate(expected):
        require(polynomial(q45['residuals'][25+i],symbols) == polynomial(e,symbols),
                'Added Q45 guard '+str(i))
    # Correct the historical proof's z/z-1 spelling by checking the actual row.
    require(polynomial(q45['residuals'][13],symbols)
            == polynomial('(K0+w)*'+C+'-F-z*('+q+'-1)',symbols), 'Shifted transport z')
    return {'exact_parent_hashes':3, 'odd_scale_rows':30, 'packing_identity':True,
            'q50_unchanged_rows':28, 'q45_unchanged_rows':25,
            'q45_added_guards':3, 'literal_transport_uses_shifted_z':True,
            'scope':'Exact algebra and source relationships; guard equivalence uses the supplied proofs.'}


def main():
    receipt = {'status':'PASS', 'authenticated_source_files':authentic_sources(),
               'coefficients':coefficients(), 'lift_chain':lift_chain(),
               'scope':'Offline finite replay; no machine simulation, refutation search, or new kernel proof.'}
    (ROOT/'DEPENDENCY_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
