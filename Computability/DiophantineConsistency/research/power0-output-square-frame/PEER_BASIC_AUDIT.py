#!/usr/bin/env python3
"""Independent full literal binding of raw6-only63 source and its frame ideals."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'research/squared-range-frame-source-prototype'
PROTOTYPE=ROOT/'research/power0-square-frame-source-prototype'
PINS={'source/raw_builder.json':'3d3280d0bebdafb02f7e1c6cf94d8069d6b573462aa355a9af4f578a163dbc0c','raw/parent.json':'2908d0f5d9e6ae09d7aef98bac5dd8661a6949496e61587e3f8926e8eb4debba','raw/domain.json':'1db0ea371288c95b0ec68811cc75dcadc60ebc96363cebdd0307bce86f8094aa','FRAME_POLICY.json':'5e9646bbb7ae1ee0b61348f58ff1e0c546ccc648cf4cfa8b7a02e1f792a9e267'}
OUTPUTS=[573,583,591,599,607,617,625,635]


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
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    for n,h in PINS.items():require(digest(PROTOTYPE/n)==h,'whole new basic byte pin '+n)
    require(digest(BASE/'MANIFEST.json')=='63ac958f76364edd07e8a68150d4781c0473ae6b9b8e554b1c6b46baca4ca81b','frozen full64 parent manifest')
    for n,h in read(BASE/'MANIFEST.json')['files'].items():require(digest(BASE/n)==h,'whole frozen64 member '+n)
    original=read(BASE/'source/raw_builder.json');source=read(PROTOTYPE/'source/raw_builder.json')
    expected=deepcopy(original)
    require(expected['rows'][1135]['terms']==[[-1,[6]],[-1,[1217]],[1,[1218]]],'exact old frame row')
    expected['rows'][1135]['terms']=[[-1,[7]],[-1,[1217]],[1,[1218]]]
    require(source==expected,'whole source equality except row1135 input6 becomes7')
    require(source['rows'][2]==dict(gate=7,label='multiplication',terms=[[-1,[6,6]],[1,[7]]]),'existing square remains exact')
    oldparent,olddomain=read(BASE/'raw/parent.json'),read(BASE/'raw/domain.json')
    parent,domain=read(PROTOTYPE/'raw/parent.json'),read(PROTOTYPE/'raw/domain.json')
    wanted={k:deepcopy(v) for k,v in oldparent.items() if k not in ['variables','residuals']}
    wanted['variant']='power0_existing_square_frame63_raw_literal_prototype'
    wanted['variables']=deepcopy(source['variables'])
    wanted['residuals']=[dict(label=q['label'],terms=deepcopy(q['terms'])) for q in source['rows']]
    guards=[];removed=[]
    for i,g in enumerate(olddomain['guards']):
        if g['predicate'].get('kind')=='retained_scalar' and g['predicate']['raw_variables']==[6]:removed.append(i);continue
        j=len(guards);aux=list(range(1267+3*j,1270+3*j));mapping=dict(zip(g['auxiliary'],aux))
        guards.append(dict(predicate=deepcopy(g['predicate']),auxiliary=aux))
        wanted['variables']+=[deepcopy(oldparent['variables'][v]) for v in g['auxiliary']]
        row=oldparent['residuals'][1185+i]
        wanted['residuals'].append(dict(label=row['label'],terms=[[c,[mapping.get(v,v) for v in m]] for c,m in row['terms']]))
    require(len(removed)==1 and parent==wanted,'entire parent changes only one frame row and exact scalar6 graph deletion/auxiliary compaction')
    require(len(parent['variables'])==1456 and len(parent['residuals'])==1248,'actual literal parent dimensions')
    require(domain==dict(baseline_body_variables=1267,baseline_body_rows=1185,baseline_raw_indices=list(range(1267)),guards=guards,predicates=63,original_scalar_predicates=60,inherited_absent_quotient_variables=[575,584,592,600,609,618,627,636],newly_removed_scalar_variables=[6],raw_source='source/raw_builder.json',frame_policy='FRAME_POLICY.json',radius_policy='RADIUS_POLICY.json',ordinary_source_equivalence_claimed=False,compact_bridge_assumed=False),'complete63 domain records and every metadata field')
    require(any(g['predicate'].get('raw_variables')==[106] for g in guards),'raw106 guard remains retained')
    for row,g in zip(parent['residuals'][1185:],guards):
        a,b,c=g['auxiliary']
        require(poly(row['terms'])==add(poly(g['predicate']['terms']),poly([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]])),'every retained Legendre polynomial')
    radius=deepcopy(read(BASE/'RADIUS_POLICY.json'));radius['joint_guard']=dict(index=62,predicate=guards[-1]['predicate'],auxiliary=guards[-1]['auxiliary'])
    require(read(PROTOTYPE/'RADIUS_POLICY.json')==radius,'unchanged radii and correctly compacted joint guard policy')
    ports=sorted({v[1] for q in source['powers'] for v in q.values()})
    mapping=dict(zip(OUTPUTS,range(1259,1267)));mapping[6]=7
    bounds=[mapping.get(v,v) for v in ports]
    policy=read(PROTOTYPE/'FRAME_POLICY.json')
    require(policy['actual_power_ports']==ports and policy['bounding_ports']==bounds and len(set(bounds))==43,'actual43 powers and43 bounding ports with only6 added to squared set')
    certpath=ROOT/'research/range-output-square-frame/CERTIFICATE.json'
    require(digest(certpath)=='a3259f4856df00152c26315f20d5d66e0e4d412d3564c85524224dde4ec8fe43','exact inherited64 frame certificate')
    cert=read(certpath);rows=[poly(q['terms']) for q in source['rows']]
    identities={}
    for name in ['new_frame_cut','new_weak_frame_cut']:
        cut=cert[name];out={}
        for item in cut['row_combination']:out=add(out,multiply(poly(item['multiplier']),rows[item['row']]))
        terms=[[c,[7 if v==6 else v for v in m]] for c,m in cut['polynomial']]
        require(out==poly(terms),'complete linear bounding-port frame ideal '+name)
        for row in [rows[2]]+rows[1177:1185]:out=add(out,row)
        expanded=[]
        for c,m in terms:
            new=[]
            for v in m:
                if v==7:new.extend([6,6])
                elif 1259<=v<1267:new.extend([OUTPUTS[v-1259]]*2)
                else:new.append(v)
            expanded.append([c,new])
        require(out==poly(expanded),'complete expanded9square frame ideal '+name)
        identities[name]=[[c,list(m)] for m,c in sorted(out.items())]
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),whole_basic_file_pins=PINS,source_coordinates=1267,source_rows=1185,parent_coordinates=1456,parent_rows=1248,retained_predicates=63,scalar_predicates=60,guard_graphs_checked=63,changed_source_rows=[1135],new_source_variables=0,new_source_rows=0,actual_power_ports=ports,bounding_ports=bounds,full_frame_identities=identities,raw106_guard_retained=True,audit_sha256=digest(Path(__file__)),new_full_unbounded_theorem_claimed=False,projected_metrics_claimed=False,scope='Independent full literal raw6-only source/parent/domain/radius compaction and both linear/expanded frame ideals. Whole unbounded theorem and projected coefficients remain separate.')
    content=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():require(args.output.read_text()==content,'refuse different retained receipt')
    else:args.output.write_text(content)
    print(content,end='')


if __name__=='__main__':main()
