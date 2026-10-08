"""Deterministic independent validation; run from bundle root."""
from __future__ import annotations
import sys,pathlib,json,random,itertools,platform,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]))
from shear_kernel import *
from shear_kernel.reference import *
from shear_kernel.presentation import *

def main():
    rng=random.Random(20261008); counts=Counter(); corpus=[]; start=time.perf_counter()
    # Larger polynomially checkable random flow witnesses, including huge data.
    for case in range(1200):
        n=rng.randint(1,12); gaps={}
        scale=1 if case%10 else 1<<rng.randint(20,600)
        for _ in range(rng.randint(1,40)):
            u,v=rng.randrange(n),rng.randrange(n); e=rng.randint(-20,20)
            if case%13==0: e*=1<<rng.randint(20,500)
            key=(u,v,e); gaps[key]=gaps.get(key,0)+rng.randint(1,9)*scale
        sol=solve_tension(gaps,balanced_fast_path=False,forest_fast_path=False)
        verify_tension(gaps,sol.potentials,sol.dual,sol.value)
        counts['flow_instances']+=1; counts['flow_phases']+=sol.phases; counts['flow_repairs']+=sol.repairs
    # Connected braid closures. These are algebraic-stage tests, not full pipeline benchmarks.
    attempts=0
    while len(corpus)<180:
        attempts+=1; s=rng.randint(2,5); length=rng.randint(1,12)
        braid=[rng.choice([-1,1])*rng.randrange(1,s) for _ in range(length)]
        try: words,components=artin_presentation(s,braid,30000)
        except ValueError: continue
        if components!=1: continue
        reduced,alive,elims=eliminate_singletons(words,range(1,s+1),30000)
        # Keep both the original presentation and the post-elimination stage.
        item={'strands':s,'braid':braid,'original_relators':words,
              'post_elimination_relators':reduced,'alive':alive,'eliminations':elims,'stages':[]}
        for stage,(ws,gens) in enumerate(((words,list(range(1,s+1))),(reduced,alive))):
            g=Grammar(); roots=[g.word(w) for w in ws]; o=optimize(g,roots,gens)
            verify_optimization(g,roots,o.certificate)
            a=o.certificate['selected_multiplier']; z={}
            if a is not None:
                row=next(x for x in o.certificate['solutions'] if x['multiplier']==a); z=dict(row['potentials'])
            for w,r in zip(ws,o.roots):
                actual=o.grammar.expand(r,100000)
                expected=w if a is None else literal_shear(w,a,z)
                assert canonical(actual)==canonical(expected)
                if a is not None:
                    assert canonical(literal_shear(actual,a,{v:-e for v,e in z.items()}))==canonical(w)
                counts['braid_relator_image_checks']+=1
            oldg,oldr,old=selected_line_step(g,roots,gens)
            oldlength=sum(oldg.meta[r].length for r in oldr)
            assert o.certificate['optimal_length']<=oldlength
            counts['braid_stage_checks']+=1
            counts['braid_stages_joint_strictly_better']+=int(o.certificate['optimal_length']<oldlength)
            counts['braid_stages_shear_shortens']+=int(o.certificate['optimal_length']<o.certificate['initial_length'])
            item['stages'].append({'initial_length':o.certificate['initial_length'],
                                   'selected_line_length':oldlength,'shear_length':o.certificate['optimal_length']})
        corpus.append(item)
    # Serialized large abstract-presentation traces, independently replayed.
    out=pathlib.Path('certificates'); out.mkdir(exist_ok=True)
    for bits in (20,100,500):
        g=Grammar(); roots=[]
        for j in range(2,8):
            u=g.concat(g.letter(j),g.run(1,(1<<bits)+j))
            roots.extend([g.power(u,(1<<bits)+j),g.power(u,(1<<bits)+j+1)])
        _,_,record=reduce_presentation(g,roots,list(range(1,8)))
        assert verify_presentation_reduction(g,roots,list(range(1,8)),record)
        assert record['terminal']['is_infinite_cyclic']
        payload={'source_contract':'abstract group presentation; no knot provenance claimed',
                 'grammar':g.to_dict(roots),'generators':list(range(1,8)),'reduction':record}
        (out/f'star_Z_{bits}.json').write_text(json.dumps(payload,indent=2))
        counts['serialized_large_presentation_certificates']+=1
    result={'seed':20261008,'python':platform.python_version(),'counts':dict(counts),
            'braid_closures':len(corpus),'braid_generation_attempts':attempts,'failures':0,
            'elapsed_seconds':time.perf_counter()-start,
            'scope':'independent algebraic stages, not the production recognizer'}
    pathlib.Path('results/audit.json').write_text(json.dumps(result,indent=2))
    pathlib.Path('results/braid_corpus.json').write_text(json.dumps(corpus,indent=2))
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
