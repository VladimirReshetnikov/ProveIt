"""Deterministic finite audit. Run from package root with PYTHONPATH=src."""
import copy,itertools,json,platform,random,sys,time
from pathlib import Path
from gauge_cuts import compile_grammar,decode_row,compose_rows,row_bound,pair_bound,extract_cut_addresses
from checker import verify_packet,verify_coloring_recipe,VerificationError
from coloring import build_recipe,color_at
from reference import literal_atlas,expand,dense_compile,literal_response
from fixtures import leaf,mapping,random_grammar,permutation_power,hidden_power,prism,k4
C={}
def inc(key,n=1): C[key]=C.get(key,0)+n

def bounds(g,p):
    for i,(z,t) in enumerate(zip(g['nodes'],p['atlases'])):
        r=len(t['metadata']['part']);bydegree={}
        for row in t['rows']:bydegree[row[0]]=bydegree.get(row[0],0)+1
        assert len(t['rows'])<=row_bound(g['k'],r)
        for d,a in bydegree.items():assert a<=4*(d+1)*max(1,8*r)**d
        inc('atlas_size_bound_checks')
        if z['op']=='join':
            w=max(len(p['atlases'][j]['metadata']['part']) for j in z['children'])
            assert p['statistics'][i]['candidate_work']<=pair_bound(g['k'],w);inc('budget_pair_bound_checks')

def recipes(g,p,all_rows=False):
    total=len(p['atlases'][-1]['rows'])
    for ri in range(total if all_rows else min(4,total)):
        rec=build_recipe(p,ri);verify_coloring_recipe(rec,g);inc('symbolic_coloring_replays')
        ads=extract_cut_addresses(p,ri);row=p['atlases'][-1]['rows'][ri]
        assert len(ads)<=g['k'] and sum(a['capacity'] for a in ads)==row[0]
        assert len({(tuple(a['path']),a['leaf_edge']) for a in ads})==len(ads)
        for a in ads:
            node=len(g['nodes'])-1
            for b in a['path']:node=g['nodes'][node]['children'][b]
            u,v,c=g['nodes'][node]['edges'][a['leaf_edge']]
            assert color_at(rec,a['path'],u)!=color_at(rec,a['path'],v)
        inc('cut_address_replays');inc('cut_edge_addresses',len(ads))

def main():
    start=time.perf_counter();rng=random.Random(20261012)
    for n in range(6):
        poss=list(itertools.combinations(range(n),2))
        for mask in range(1<<len(poss)):
            es=[(u,v,1) for i,(u,v) in enumerate(poss) if (mask>>i)&1]
            z=leaf(n,es,range(n));g={'k':3,'nodes':[z]};p=compile_grammar(g)
            verify_packet(p,g);inc('complete_certificate_replays');bounds(g,p)
            full={decode_row(r) for r in p['atlases'][0]['rows']}
            assert full==literal_atlas(z,3);inc('simple_graphs_all_components')
            for k in range(4):
                assert {r for r in full if r[0]<=k}==literal_atlas(z,k);inc('graph_threshold_comparisons')
            for tm in range(1<<n):
                keep=[i for i in range(n) if (tm>>i)&1];op=mapping(0,range(n),keep);got=set()
                for row in full:got.update(compose_rows(op,[p['atlases'][0]['metadata']],(row,)))
                assert got==literal_atlas(leaf(n,es,keep),3);inc('terminal_subset_projection_comparisons')
        print('simple graphs through',n,'done',flush=True)
    for _ in range(1000):
        n=rng.randrange(9);es=[]
        if n:
            es=[(rng.randrange(n),rng.randrange(n),rng.randrange(1,8)) for j in range(rng.randrange(15))]
        ts=[i for i in range(n) if rng.randrange(2)];rng.shuffle(ts)
        g={'k':rng.randrange(4),'nodes':[leaf(n,es,ts)]};p=compile_grammar(g)
        verify_packet(p,g);inc('complete_certificate_replays');bounds(g,p)
        assert {decode_row(r) for r in p['atlases'][0]['rows']}==literal_atlas(g['nodes'][0],g['k'])
        inc('weighted_multigraph_leaf_comparisons')
    for trial in range(1000):
        g=random_grammar(rng,k=rng.randrange(4));p=compile_grammar(g)
        verify_packet(p,g);inc('complete_certificate_replays');bounds(g,p)
        lit=expand(g,max_vertices=12,max_edges=200)
        for i,z in enumerate(lit):
            assert {decode_row(r) for r in p['atlases'][i]['rows']}==literal_atlas(z,g['k']);inc('literal_grammar_node_comparisons')
        inc('random_grammars');recipes(g,p,trial<150)
        if trial<120:
            dense=dense_compile(g)
            for i,z in enumerate(lit):assert dense['tables'][i]==literal_response(z,g['k']);inc('explicit_response_baseline_node_checks')
        bad=copy.deepcopy(p);bad['atlases'][-1]['metadata']['edges']+=1
        try:verify_packet(bad,g)
        except VerificationError:inc('forged_metadata_rejections')
        else:raise AssertionError('accepted forged metadata')
        if trial%200==199:print('random grammars',trial+1,'done',flush=True)
    stress={}
    fixtures=[('hidden_2pow512',hidden_power(512)),
              ('permuted_channels_unit_2pow128',permutation_power(2,128)),
              ('permuted_channels_heavy_2pow512',permutation_power(32,512,capacity=4)),
              ('free_terminal_components_1024',{'k':3,'nodes':[leaf(1024,[],range(1024))]}),
              ('capacity_16385_bits',{'k':3,'nodes':[leaf(2,[(0,1,1<<16384)],[0,1]),mapping(0,[0,1],[])]})]
    for name,g in fixtures:
        t=time.perf_counter();p=compile_grammar(g);verify_packet(p,g);bounds(g,p);recipes(g,p)
        inc('complete_certificate_replays');inc('binary_stress_cases')
        stress[name]={'rules':len(g['nodes']),'peak_rows':max(s['states'] for s in p['statistics']),
                      'total_rows':sum(s['states'] for s in p['statistics']),'seconds':time.perf_counter()-t,
                      'root_metadata':p['atlases'][-1]['metadata'],'query':p['query']}
        if name!='capacity_16385_bits':
            Path('examples',name+'.json').write_text(json.dumps(g,indent=2)+'\n')
            Path('data',name+'_certificate.json').write_text(json.dumps(p,separators=(',',':'))+'\n')
        if name=='permuted_channels_unit_2pow128':
            ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3)
            Path('data',name+'_coloring.json').write_text(json.dumps(build_recipe(p,ri),separators=(',',':'))+'\n')
        print('stress',name,'done',flush=True)
    for name,g in [('prism',prism()),('k4',k4())]:
        Path('examples',name+'.json').write_text(json.dumps(g,indent=2)+'\n');p=compile_grammar(g)
        Path('data',name+'_certificate.json').write_text(json.dumps(p,indent=2)+'\n')
        if name=='prism':
            ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3)
            Path('data','prism_coloring.json').write_text(json.dumps(build_recipe(p,ri),indent=2)+'\n')
    result={'python':sys.version,'platform':platform.platform(),'seed':20261012,'counts':C,
            'stress':stress,'elapsed_seconds':time.perf_counter()-start,
            'scope':'standalone graph kernel; no native geometry or knot recognition executed'}
    Path('data/validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(C,indent=2));print('elapsed',result['elapsed_seconds'])
if __name__=='__main__':main()
