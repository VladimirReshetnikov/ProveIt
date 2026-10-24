#!/usr/bin/env python3
"""Independent whole-source/frame/guard binding of the eight-only prototype."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROTOTYPE = ROOT/'research/squared-range-frame-source-prototype'
BASE = ROOT/'research/common-squared-radius-source-prototype'
PINS = {
 'source/raw_builder.json':'2d91052f7b2efd282900da4a04890a435f27423d5f28abb7aedfd2112d3b9789',
 'raw/parent.json':'27135fbb2449db66a92afd00dce984b481f3af07d1a0b16b3f9aaaaf17454bea',
 'raw/domain.json':'fdd4121f3a1dbb3511087b155ede7705c3286fbd212c0753db674fce6f654bf4',
 'FRAME_POLICY.json':'548cd8d8a3031e9b5eb5a3aec22fb75300d9adfc38cce54ea70a1bef0c7a733f',
}
OUTPUTS = [573,583,591,599,607,617,625,635]
QUOTIENTS = {575,584,592,600,609,618,627,636}
FRAME_ROWS = [1165,1167,1168,1169,1170,1172,1173,1175]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def poly(terms):
    result = {}
    for c,m in terms:
        key = tuple(sorted(m))
        result[key] = result.get(key,0)+c
    return {m:c for m,c in result.items() if c}


def add(a,b):
    result = dict(a)
    for m,c in b.items():
        result[m] = result.get(m,0)+c
    return {m:c for m,c in result.items() if c}


def multiply(a,b):
    result = {}
    for m,c in a.items():
        for n,d in b.items():
            key = tuple(sorted(m+n))
            result[key] = result.get(key,0)+c*d
    return {m:c for m,c in result.items() if c}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    args = parser.parse_args()
    for name,h in PINS.items():
        require(digest(PROTOTYPE/name)==h,'whole new basic file: '+name)
    require(digest(BASE/'MANIFEST.json')=='64bbe1b16ef87b8c339b69e2763cdf2a452ceda537765f66c5217b716fd01fdb','frozen complete base')
    manifest = read(BASE/'MANIFEST.json')['files']
    for name,h in manifest.items():
        require(digest(BASE/name)==h,'frozen base member: '+name)
    old = read(BASE/'source/raw_builder.json')
    source = read(PROTOTYPE/'source/raw_builder.json')
    expected = deepcopy(old)
    square_map = dict(zip(OUTPUTS,range(1259,1267)))
    for output,row in zip(OUTPUTS,FRAME_ROWS):
        square = square_map[output]
        require(expected['rows'][row]['terms'][0]==[-1,[output]],'exact source frame port occurrence')
        expected['rows'][row]['terms'][0]=[-1,[square]]
        expected['variables'].append({'kind':'gate','name':'frame.range_output_square.'+str(output)})
        expected['rows'].append({'gate':square,'label':'frame_range_output_square','terms':[[-1,[output,output]],[1,[square]]]})
    require(source==expected,'whole source delta: only eight frame terms and eight complete square gates')
    old_parent,old_domain = read(BASE/'raw/parent.json'),read(BASE/'raw/domain.json')
    parent,domain = read(PROTOTYPE/'raw/parent.json'),read(PROTOTYPE/'raw/domain.json')
    wanted_parent = {k:deepcopy(v) for k,v in old_parent.items() if k not in ['variables','residuals']}
    wanted_parent['variant']='squared_range_output_frame64_raw_literal_prototype'
    wanted_parent['variables']=deepcopy(source['variables'])
    wanted_parent['residuals']=[{'label':q['label'],'terms':deepcopy(q['terms'])} for q in source['rows']]
    wanted_guards = []
    removed = []
    for i,guard in enumerate(old_domain['guards']):
        if guard['predicate'].get('kind')=='retained_scalar' and guard['predicate']['raw_variables'][0] in QUOTIENTS:
            removed.append(guard['predicate']['raw_variables'][0])
            continue
        j = len(wanted_guards)
        new_auxiliary = list(range(1267+3*j,1270+3*j))
        mapping = dict(zip(guard['auxiliary'],new_auxiliary))
        wanted_guards.append({'predicate':deepcopy(guard['predicate']),'auxiliary':new_auxiliary})
        wanted_parent['variables'] += [deepcopy(old_parent['variables'][v]) for v in guard['auxiliary']]
        row = old_parent['residuals'][1177+i]
        wanted_parent['residuals'].append({'label':row['label'],'terms':[[c,[mapping.get(v,v) for v in m]] for c,m in row['terms']]})
    require(sorted(removed)==sorted(QUOTIENTS),'delete exactly eight original scalar guards')
    require(parent==wanted_parent,'all parent rows/variables/retained labels and names with exact auxiliary compaction')
    require(domain['guards']==wanted_guards and domain['baseline_raw_indices']==list(range(1267)), 'complete retained64 guard records/body map')
    require(domain['predicates']==64 and domain['original_scalar_predicates']==61 and len(parent['variables'])==1459 and len(parent['residuals'])==1249,'actual complete new parent census')
    for row,guard in zip(parent['residuals'][1185:],wanted_guards):
        a,b,c = guard['auxiliary']
        require(poly(row['terms'])==add(poly(guard['predicate']['terms']),poly([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])),'every retained Legendre graph polynomial')
    actual_ports = sorted({v[1] for call in source['powers'] for v in call.values()})
    bounding_ports = [square_map.get(v,v) for v in actual_ports]
    policy = read(PROTOTYPE/'FRAME_POLICY.json')
    require(len(actual_ports)==43 and policy['actual_power_ports']==actual_ports and policy['bounding_ports']==bounding_ports,'complete43 actual/bounding port distinction')
    require(policy['square_variables']==list(range(1259,1267)) and policy['square_rows']==list(range(1177,1185)) and policy['changed_frame_rows']==FRAME_ROWS,'all eight square aliases')
    old72path = ROOT/'research/shifted-t-index-guard/CERTIFICATE.json'
    require(digest(old72path)=='03d6e21d5dd798b117dd6a627132c46f4811ec0fd10b25f881d2bd2c25278a3c','exact inherited frame ideals')
    cuts = read(old72path)
    rows = [poly(q['terms']) for q in source['rows']]
    frame_identities = {}
    for name in ['frame_cut','weak_frame_cut']:
        actual = {}
        for item in cuts[name]['row_combination']:
            actual = add(actual,multiply(poly(item['multiplier']),rows[item['row']]))
        terms = [[c,[square_map.get(v,v) for v in m]] for c,m in cuts[name]['polynomial']]
        require(actual==poly(terms),'complete modified linear frame ideal: '+name)
        nonlinear = list(terms)
        for row in rows[1177:]:
            actual = add(actual,row)
        for term in nonlinear:
            expanded = []
            for v in term[1]:
                expanded.extend([OUTPUTS[v-1259]]*2 if 1259<=v<1267 else [v])
            term[1] = expanded
        require(actual==poly(nonlinear),'complete output-square frame ideal: '+name)
        frame_identities[name]=[[c,list(m)] for m,c in sorted(actual.items())]
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'whole_basic_file_pins':PINS,'source_coordinates':1267,'source_rows':1185,'parent_coordinates':1459,'parent_rows':1249,'retained_guards':64,'scalar_guards':61,'guard_graphs_checked':64,'changed_frame_rows':FRAME_ROWS,'appended_square_rows':list(range(1177,1185)),'actual_power_ports':actual_ports,'bounding_ports':bounding_ports,'full_frame_identities':frame_identities,'new_full_prefix_or_native_proof_claimed':False,'projected_metrics_claimed':False,'audit_sha256':digest(Path(__file__)),'scope':'Independent exact new source/parent/domain compaction and complete linear/squared weak/ordinary frame ideals only. Full unbounded theorem and projection acceptance remain separate.'}
    content=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():
        require(args.output.read_text()==content,'refuse changed receipt overwrite')
    else:
        args.output.write_text(content)
    print(content,end='')


if __name__=='__main__':
    main()
