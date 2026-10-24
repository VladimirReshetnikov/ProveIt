#!/usr/bin/env python3
"""Independent stdlib-only collection of the shifted-t theorem's new source cuts."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def need(ok,why):
    if not ok:raise ValueError(why)


def polynomial(terms):
    result={}
    for coefficient,monomial in terms:
        key=tuple(sorted(monomial));result[key]=result.get(key,0)+coefficient
    return {m:c for m,c in result.items() if c}


def plus(a,b,scale=1):
    result=dict(a)
    for m,c in b.items():result[m]=result.get(m,0)+scale*c
    return {m:c for m,c in result.items() if c}


def times(a,b):
    result={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));result[key]=result.get(key,0)+c*d
    return {m:c for m,c in result.items() if c}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    load=lambda p:json.loads(p.read_bytes())
    pins=load(HERE/'SOURCE_PINS.json')
    for name,expected in pins['files'].items():
        need(sha256((ROOT/name).read_bytes()).hexdigest()==expected,'whole inherited source pin '+name)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    data=load(HERE/'CERTIFICATE.json')
    rows=[polynomial(r['terms']) for r in raw['rows']]
    need(len(rows)==1177 and len(raw['variables'])==1259,'entire original raw body')
    need([i for i,row in enumerate(rows) if any(825 in m for m in row)]==[762], 'complete original825 use boundary')
    need(825 not in data['frame_arguments'] and len(data['frame_arguments'])==43, '825 absent from actual frame')
    expected={
        'd1_radius':[[1,[109]],[-1,[107,4,4]]],
        't_shift':[[1,[110]],[-1,[4]],[-1,[109]]],
        't_base':[[1,[112]],[-1,[]],[-1,[109]]],
        'factorial1_remainder':[[1,[111]],[-1,[114]],[-1,[115]],[-1,[]]],
        'factorial1_ceiling':[[1,[107,111]],[-1,[113]],[-1,[115]]],
        'choose1_digit':[[1,[546]],[-1,[547,111]],[-1,[547,530,548]],[-1,[549]]],
        'choose1_remainder':[[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]],
        'choose1_digit_bound':[[1,[530]],[-1,[111]],[-1,[551]],[-1,[]]],
    }
    count=0
    def collect(cut,target):
        nonlocal count
        result={}
        for item in cut['row_combination']:
            result=plus(result,times(polynomial(item['multiplier']),rows[item['row']]))
        need(result==polynomial(target),'all coefficients of independent original-row cut')
        count+=1
        return result
    for name,target in expected.items():collect(data['exact_source_cuts'][name],target)
    seed=data['seeds'][3]
    need(seed['aliases']==dict(X=821,Y=822,k=110,YminusK=825,S=823,R=824,Squotient=838,Rquotient=839),'actual omitted seed3')
    for cut in seed['cuts'].values():collect(cut,cut['polynomial'])
    collect(seed['cuts']['index_at_most_Y'],[[1,[822]],[-1,[110]],[-1,[825]]])
    combined=collect(data['t1_combined_source_cut'],[[1,[107,111]],[-1,[113]],[-1,[115]],[1,[112]],[-1,[]],[-1,[107,4,4]]])
    at1={}
    for m,c in combined.items():
        key=tuple(v for v in m if v!=4);at1=plus(at1,{key:c})
    at1=plus(at1,polynomial([[1,[113]],[-1,[112]]]))
    need(at1==polynomial([[1,[107,111]],[-1,[107]],[-1,[]],[-1,[115]]]),'exact t1 ceiling under only recovered call4')
    ports={4:(112,4,113),7:(531,110,546),8:(530,4,547)}
    for index,values in ports.items():
        need(tuple(raw['powers'][index][k][1] for k in ['base','exponent','output'])==values,'actual three relevant power ports')
    early=[0,1,2,3,4,5,6,8,9]
    need(data['chronology']['interpreted_calls_before_825']==early and
         data['chronology']['calls_not_interpreted_before_825']==[7] and
         all(raw['powers'][i]['exponent'][1] in {4,86,90,122} for i in early), 'every early call uses a recovered pair')
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),independent_original_row_cuts=count,
        source_occurrences_of825=[762],actual_ports={str(i):list(v) for i,v in ports.items()},
        exact_t1_identity_without_factorial1_semantics=True,interpreted_calls_before825=early,
        whole_author_and_partial_parent_proofs_read=True,ordinary_source_equivalence_approved=True,
        author_source_pins={name:sha256((HERE/name).read_bytes()).hexdigest() for name in ['PROOF.md','CERTIFICATE.json','SOURCE_PINS.json','check.py']},
        imports_author_poly_or_checker=False,source_builder_optimizer_archive_or_lean_executed=False,
        scope='Independent exact source cuts and ordinary proof review; accepted signed-index/Pell interfaces retained. No projected metric or internal-ZFC claim.')
    text=json.dumps(report,indent=2,sort_keys=True)+'\n';args.output.write_text(text);print(text,end='')


if __name__=='__main__':main()
