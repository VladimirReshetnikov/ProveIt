#!/usr/bin/env python3
"""Reproducible, size-capped algebra and independent crossing-cube audit."""
from __future__ import annotations
import itertools,json,platform,sys,time,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from portkh import gf2
from portkh.complexes import analyze,expand,coupled_pair,connected_singular_pair
from portkh.explicit import from_dense
from portkh.minimize import minimize_ports
from portkh.languages import fixed_weight,analyze_restricted
from cube_oracle import cube,homology,components,low_pivot_rank


def main():
    if not __debug__:
        raise RuntimeError('Audit assertions require Python without -O')
    started=time.perf_counter()
    rank_checks=singular_middle=0
    for r in (1,2):
        for a in itertools.product(range(4),repeat=2):
            for u in itertools.product(range(1 << r),repeat=2):
                for v in itertools.product(range(4),repeat=r):
                    ans=gf2.rank_update(a,2,u,v)
                    assert ans['rank']==low_pivot_rank(gf2.add(a,gf2.mul(u,v)))
                    singular_middle += gf2.rank(ans['middle_rows'])<r
                    rank_checks+=1
    records=[];knots=0;port_total=0
    for strands,max_length in ((2,5),(3,4)):
        alphabet=tuple(g for i in range(1,strands) for g in (i,-i))
        for length in range(max_length+1):
            for word in itertools.product(alphabet,repeat=length):
                rows,degrees=cube(strands,word)
                profile=homology(rows,degrees)
                c=from_dense(rows,degrees)
                ans=analyze(c)
                assert expand(c,max_dimension=6000)[0]==rows
                assert ans['homology_dimension']==sum(profile.values())
                mirror_rows,mirror_degrees=cube(strands,tuple(-g for g in word))
                mirror=homology(mirror_rows,mirror_degrees)
                assert mirror=={-h:b for h,b in profile.items()}
                ncomp=components(strands,word)
                knots+=ncomp==1
                port_total+=c.ports
                records.append({'strands':strands,'word':list(word),'components':ncomp,
                    'cube_dimension':len(rows),'homology':profile,'beta':sum(profile.values()),
                    'bridge_ports':c.ports,'base_beta':ans['base_homology_dimension'],
                    'core_shape':ans['core_shape'],'core_rank':ans['core_rank']})
    examples=[]
    for name,c in [('connected_singular_40',connected_singular_pair(40)),
                   ('connected_singular_200',connected_singular_pair(200)),
                   ('dense_invertible_40',coupled_pair(40,'invertible')),
                   ('large_homology_40',coupled_pair(40,'large_homology'))]:
        ans=analyze(c)
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(c.to_dict(),indent=2)+'\n')
        (ROOT/'examples'/f'{name}.certificate.json').write_text(json.dumps(ans,indent=2)+'\n')
        examples.append({'name':name,'dimension':ans['dimension'],'beta':ans['homology_dimension'],
                         'ports':c.ports,'core_shape':ans['core_shape'],'core_rank':ans['core_rank'],
                         'maximum_width':max(max(b.register.widths) for b in c.blocks)})
    # Supply one genuine small knot complex and its unambiguous braid provenance.
    rows,degrees=cube(3,[1,-2,1,-2]);c=from_dense(rows,degrees);ans=analyze(c)
    (ROOT/'examples'/'figure_eight_cube.json').write_text(json.dumps(c.to_dict(),indent=2)+'\n')
    (ROOT/'examples'/'figure_eight_cube.certificate.json').write_text(json.dumps(ans,indent=2)+'\n')
    (ROOT/'examples'/'figure_eight_cube.provenance.json').write_text(json.dumps({
        'constructor':'scripts/cube_oracle.py','strands':3,'word':[1,-2,1,-2],
        'normalization':'homological degree = number of 1-resolutions - negative crossings',
        'coefficient_field':'F_2','kind':'unreduced','beta':10,
        'note':'Not exported from the upstream scanner; constructed by the bundled independent cube.'},indent=2)+'\n')
    language_examples=[]
    for m,k in ((63,31),(64,32)):
        name=f'binomial_{m}_{k}'
        c=coupled_pair(m,'invertible');language=fixed_weight(m,k)
        ans=analyze_restricted(c,(language,))
        assert ans['homology_dimension']==2*(math.comb(m,k)%2)
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(c.to_dict(),indent=2)+'\n')
        (ROOT/'examples'/f'{name}.languages.json').write_text(json.dumps([language.to_dict()],indent=2)+'\n')
        (ROOT/'examples'/f'{name}.certificate.json').write_text(json.dumps(ans,indent=2)+'\n')
        language_examples.append({'m':m,'k':k,'copies':math.comb(m,k),'dimension':ans['dimension'],
                                  'homology_dimension':ans['homology_dimension'],
                                  'effective_width':max(ans['register_summaries'][0]['maximum_width'],1)})
    result={'format':'portkh-validation-1','python':sys.version,'platform':platform.platform(),
        'exhaustive_rank_update_checks':rank_checks,'singular_middle_checks':singular_middle,
        'cube_presentations':len(records),'mirror_cube_checks':len(records),
        'knot_presentations':knots,'link_presentations':len(records)-knots,
        'max_cube_dimension':max(x['cube_dimension'] for x in records),
        'max_bridge_ports':max(x['bridge_ports'] for x in records),
        'bridge_port_total':port_total,'language_examples':language_examples,'examples':examples,'cube_records':records,
        'elapsed_seconds':time.perf_counter()-started,
        'upstream_full_checkout_tests_executed':False,
        'conclusion':'All stated comparisons passed; symbolic examples have no inferred knot provenance.'}
    (ROOT/'data'/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cube_records','python','platform')},indent=2))

if __name__=='__main__':main()
