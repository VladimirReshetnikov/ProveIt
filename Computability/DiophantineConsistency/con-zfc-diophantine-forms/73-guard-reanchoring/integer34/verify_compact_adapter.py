#!/usr/bin/env python3
"""Finite data audit supporting COMPACT_S34_ADAPTER.md, not a semantic proof."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

HERE=Path(__file__).resolve().parent


def require(value,label):
    if not value:
        raise ValueError(label)


def blob(raw):
    return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--compact-coefficients',type=Path,default=HERE.parent/'compact_coefficients')
    args=parser.parse_args()
    root=args.compact_coefficients
    expected_proofs={
        'native/PROOF.md':'8085a4ca9baca13eea001a3c8537937c5b3f0753',
        'native/COEFFICIENT_BINDING.json':'c54f7f1ce0698a5aad3bf56722c3dde343db6dff',
        'native/source/coefficients__PROOF.md':'cd766747a2d3685800842776c3ad7437e4983837'
    }
    for path,expected in expected_proofs.items():
        require(blob((root/path).read_bytes())==expected,'proof identity: '+path)
    require(blob((HERE/'upstream'/'quartic41.json').read_bytes())==
            '521f16a310f49e736ea8ffac3fe13847ff71adcb','source Q41 skeleton')
    legacy=json.loads((HERE/'sextic34.json').read_text())
    compact=json.loads((HERE/'sextic34_compact.json').read_text())
    for key in ('domain','variables','variable_count','fixed_numerals','residuals',
                'equation_count','single_polynomial','exact_degree','degree_certificate',
                'restoration_except_positivity_witnesses','guard_change'):
        require(compact[key]==legacy[key],'unchanged symbolic sextic: '+key)
    require(compact['coefficient_binding']['backend']==
            'wang943-complement67-shared-anchor-length8807-prime581197','compact instance backend')
    require(compact['coefficient_binding']['ports']=={
        'beta':'../compact_coefficients/native/coefficients/beta.bin.gz',
        'K0':'../compact_coefficients/native/coefficients/K.bin.gz',
        'MC':'../compact_coefficients/native/coefficients/MC.bin.gz',
        'MF':'../compact_coefficients/native/coefficients/MF_source.bin.gz'},'exact compact aliases')
    native=root/'native'
    manifest=json.loads((native/'COEFFICIENT_BINDING.json').read_text())
    require(manifest['instance']=='wang943-complement67-shared-anchor-length8807-prime581197',
            'whole compact backend identity')
    values={}
    for record in manifest['materialization']['files']:
        compressed=(native/record['file']).read_bytes()
        raw=gzip.decompress(compressed)
        require(hashlib.sha256(compressed).hexdigest()==record['gzip_sha256'],'gzip hash')
        require(hashlib.sha256(raw).hexdigest()==record['sha256'],'raw hash')
        value=int.from_bytes(raw,'little')
        require(value.bit_length()==record['bits'],'bitlength')
        require(len(raw)==record['raw_bytes']==(value.bit_length()+7)//8,'minimal integer')
        values[record['port']]=value
    require(set(values)=={'beta','K','MC','MF_source'},'exact complete port set')
    beta=values['beta']; mf=values['MF_source']; native_mf=mf-beta
    checks={
        'status':'PASS','d':590069,'d_odd':590069%2==1,
        'beta_exact':beta==(1<<590069)-1,'beta_at_least_17':beta>=17,
        'low_mask_bound':0<values['MC']<beta,
        'shifted_high_mask_bound':beta<mf<2*beta,
        'K0_nonnegative':values['K']>=0,
        'native_mask_residues':[values['MC']%4,native_mf%8],
        'population_sum':values['MC'].bit_count()+native_mf.bit_count(),
        'all_payload_hashes_match':True,
        'proof_git_blobs_checked':expected_proofs,
        'source_Q41_git_blob_checked':True,
        'compact_symbolic_skeleton_equals_source34_instance':True,
        'compact_port_aliases_checked':True,
        'new_raw_bytes':manifest['materialization']['total_raw_bytes'],
        'source34_raw_bytes':532479,
        'raw_byte_reduction':532479-manifest['materialization']['total_raw_bytes'],
        'scope':'Finite tuple and provenance hypotheses for the written compact S34 adapter; not an unbounded compiler proof.'
    }
    for key in ['d_odd','beta_exact','beta_at_least_17','low_mask_bound',
                'shifted_high_mask_bound','K0_nonnegative','all_payload_hashes_match']:
        require(checks[key],key)
    require(checks['native_mask_residues']==[2,4],'native mask parity')
    require(checks['population_sum']==590069,'native population sum')
    checks['raw_byte_reduction_percent']=100*checks['raw_byte_reduction']/532479
    (HERE/'COMPACT_ADAPTER_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))


if __name__=='__main__':
    main()
