#!/usr/bin/env python3
"""UNSEALED DRAFT: coherent TWO weighted-anchor rho47/L8191 P66 producer."""
import argparse
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
PAGE=ROOT/'candidates/one-page-compact66-two-anchor8191'
PARENT=ROOT/'candidates/one-page-compact66'
INDEXED=ROOT/'research/indexed-tile-enumeration'
ADAPTER='7e1b1057b79c6790a784be7c4a6a7d6cb54492ceb5ae3a73ea24ba758c4deddf'


def bootstrap():
    def unique(items):
        out={}
        for k,v in items:
            if k in out:raise ValueError('duplicate bootstrap JSON key')
            out[k]=v
        return out
    for item in [PAGE/'SOURCE_PINS.json',PAGE/'guard.py']:
        if not item.is_file() or item.is_symlink() or any(p.is_symlink() for p in item.parents):
            raise ValueError('regular bootstrap input without symbolic path components')
    pins=json.loads((PAGE/'SOURCE_PINS.json').read_bytes(),object_pairs_hook=unique,
                    parse_constant=lambda v:(_ for _ in ()).throw(ValueError('nonfinite bootstrap JSON constant '+v)))
    path=PAGE/'guard.py';raw=path.read_bytes();name=path.relative_to(ROOT).as_posix()
    pin=pins['own_core'][name]
    if type(pin) is not dict or set(pin)!={'bytes','sha256'} or type(pin['bytes']) is not int or type(pin['sha256']) is not str or not re.fullmatch('[0-9a-f]{64}',pin['sha256']):
        raise ValueError('strict bootstrap guard byte/hash schema')
    if pin!={'bytes':len(raw),'sha256':sha256(raw).hexdigest()}:
        raise ValueError('whole reviewed guard before first local import')
    spec=importlib.util.spec_from_file_location('held_two_anchor8191_build_guard',path)
    if spec is None or spec.loader is None:raise ValueError('reviewed guard import specification')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def construct(g):
    tiles=g.load(INDEXED/'TILES.json')
    g.need(type(tiles) is list and len(tiles)==943 and all(type(t) is list and len(t)==4 and
           all(type(c) is int for c in t) and 0<=t[0]<=249 and 0<=t[2]<=249 and
           0<=t[1]<=438 and 0<=t[3]<=438 for t in tiles),'entire canonical943 typed old tile datum')
    rho=1<<47;B=1<<(47*8191);beta=B-1
    complemented=[[255-w,511-n,255-e,511-s] for w,n,e,s in tiles]
    g.need(all(6<=t[0]<=255 and 6<=t[2]<=255 and 73<=t[1]<=511 and 73<=t[3]<=511
               for t in complemented),'every genuine complemented label is strictly positive')
    phi={i:1+(1<<10)*(1+w+(n<<8)+(e<<17)+(s<<25))
         for i,(w,n,e,s) in enumerate(tiles)}
    triples=[(10,1023,8),(27,1003,8),(18,1013,9),(35,983,9),
             (44,1095,1),(45,2195,1)]
    for b,e,m in triples:
        for j in range(m):
            g.need(e+j not in phi,'disjoint complete producer control support');phi[e+j]=1<<(b+j)
    g.need(len(phi)==979 and all(0<c<=rho//4 for c in phi.values()) and
           all(phi[j]<rho//8 for j in range(943)) and phi[1095]==rho//8 and phi[2195]==rho//4,
           'complete producer Phi bounds and TWO exact weighted anchors')
    support=set(range(943))|set(range(983,992))|set(range(1003,1011))|set(range(1013,1022))|set(range(1023,1031))|{1063,1064,1095,2195}
    g.need(len(support)==981 and set(phi)==support-{1063,1064},'all producer981 support slots')
    # Positive reversed coefficients: no rational evaluation or printed parser.
    DC=sum(1<<(47*e) for e in [30,62,1100])
    for e,c in phi.items():DC+=c*((1<<(47*(4393-e)))+(1<<(47*(5495-e))))
    K0=DC+(1<<(47*8233))
    MC=beta-sum(1<<(47*e) for e in support-{1})-2*(1<<(47*1063))
    Lambda=(1<<(47*4393))+(1<<(47*5495))
    core=sum(1<<(47*e) for e in list(range(1013,1022))+list(range(1065,1073))+[2195])
    padding=((rho-1)*sum(1<<(47*e) for e in range(8176,8191))
             +(rho-1)*sum(1<<(47*e) for e in range(7691,7694))+(2**26-1)*(1<<(47*7694)))
    native=4+(2**46-2)*Lambda+core+padding
    MF=native+beta
    g.need(0<DC<B and 0<MC<beta and 0<native<beta and MC%4==2 and native%8==4,
           'whole producer scalar boxes and source shift')
    g.need(MC.bit_count()==47*8191-981 and native.bit_count()==981 and padding.bit_count()==872,
           'whole producer mask populations and872 LOW26 padding bits')
    certificate=g.controller_context()
    outputs={};ports={};total=0
    for name,value,file in [('beta',beta,'beta.bin.gz'),('K0',K0,'K.bin.gz'),('MC',MC,'MC.bin.gz'),('MF',MF,'MF_source.bin.gz')]:
        raw=value.to_bytes((value.bit_length()+7)//8,'little');blob=gzip.compress(raw,compresslevel=9,mtime=0)
        outputs['coefficients/'+file]=blob;total+=len(raw)
        ports[name]={'file':file,'bits':value.bit_length(),'gzip_sha256':g.digest(blob),'raw_sha256':g.digest(raw)}
    binding={'schema':'whole_two_anchor8191_p66_binding_v1','path':'coefficients/','ports':ports,'raw_bytes':total,
             'tuple':'same indexed BFS943; coherent complemented TWO weighted-anchor47/L8191; MF_source shifted once',
             'ordinary_proof':'PROOF.md','indexed_seal':'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84',
             'native_adapter_seal':ADAPTER,'accepted_controller':certificate}
    outputs['COEFFICIENT_BINDING.json']=g.encoded(binding)
    packet=g.load(PARENT/'polynomial.json');packet['coefficient_binding']=binding
    outputs['polynomial.json']=g.encoded(packet)
    cal={'schema':'whole_two_anchor8191_p66_calibration_v1','historical_free_port_source':'fixed/source54-p66.json',
         'historical_sha256':g.digest((PAGE/'fixed/source54-p66.json').read_bytes()),'all_arithmetic_rows_unchanged':True,
         'old_and_new_specialized_polynomials_identified':False,'all_four_ports_bound_together':True,
         'source_interface':'whole complemented TWO weighted-anchor47/L8191 native source; fresh canonical R=3 mod4',
         'soundness_map':'T_old=f*T; retain every other positive input and all current two_anchor8191 ports',
         'completeness_map':'fresh V=chi_S(R)/S,y=psi_S(R),T=(V+c+R*f^2)/(c*f^2)',
         'fresh_native_and_rank_witnesses':True,'native_adapter_seal':ADAPTER,'accepted_controller':certificate,
         'binding_sha256':g.digest(outputs['COEFFICIENT_BINDING.json']),'proof_sha256':g.digest((PAGE/'PROOF.md').read_bytes()),
         'raw_port_bytes':total,'scope':'Ordinary composed calibration; finite programs bind this instance, not the unbounded proof or consistency.'}
    outputs['CALIBRATION_BINDING.json']=g.encoded(cal)
    index={'schema':'two_anchor8191_p66_source_inventory_v1','files':{n:g.pin(raw) for n,raw in outputs.items()},
           'producer_sha256':g.digest(Path(__file__).read_bytes()),'source_pins_sha256':g.digest((PAGE/'SOURCE_PINS.json').read_bytes())}
    outputs['SOURCE_INDEX.json']=g.encoded(index)
    return outputs,{'whole_raw_bytes':total,'ports':ports,'Phi_nonzero_coefficients':len(phi),'support_slots':len(support),
                    'mask_populations':[MC.bit_count(),native.bit_count()],'padding_bits':padding.bit_count()}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();g=bootstrap();g.authenticate();before=g.snapshot()
    role=('build-check-optimized' if sys.flags.optimize else 'build-check') if args.check else 'build'
    g.receipt_path(role,args.output)
    if not args.check:g.need(not sys.flags.optimize,'first producer runs in ordinary mode')
    for name in g.SOURCE_OUTPUTS:
        path=g.safe(PAGE,name);g.need(path.is_file() if args.check else not path.exists(),'fixed source artifact freshness '+name)
    outputs,record=construct(g);g.need(set(outputs)==set(g.SOURCE_OUTPUTS),'exact eight-output source plan')
    g.unchanged(before)
    for name,raw in outputs.items():
        path=g.safe(PAGE,name)
        if args.check:g.need(path.read_bytes()==raw,'pure entire two_anchor8191 source rebuild '+name)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            with path.open('xb') as out:out.write(raw)
    g.unchanged(before,allowed=g.SOURCE_OUTPUTS if not args.check else ())
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'pure complete source rebuild' if args.check else 'first coherent two_anchor8191 source build',
            'artifacts':{n:g.pin(raw) for n,raw in outputs.items()},'native_binding':record,
            'source_pins_sha256':g.digest((PAGE/'SOURCE_PINS.json').read_bytes()),'producer_sha256':g.digest(Path(__file__).read_bytes()),
            'scope':'Fixed coherent four-port specialization only; no native compiler, Lean, consistency decision, render or maintained-page change.'}
    g.receipt(role,g.encoded(result),args.output)


if __name__=='__main__':main()
