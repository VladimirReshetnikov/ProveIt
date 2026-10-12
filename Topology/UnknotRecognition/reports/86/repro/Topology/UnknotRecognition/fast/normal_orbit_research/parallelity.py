"""Finite disk/strip/cap references for source parallelity and its complement."""
from collections import Counter, defaultdict


def literal_base(geometry, *, max_points=10000):
    n, csize = geometry['polygon_points'], geometry['corner_points']
    if n+csize > max_points: raise ValueError('literal parallelity expansion exceeds its cap')
    parent = list(range(n)); corner = list(range(csize)); link = list(range(2*csize)); edges = sum((p['stop']-p['start'])*len(p['edges']) for p in geometry['polygons'])
    adjacency = defaultdict(list); handles = [None]*n
    def find(par, i):
        while par[i] != i: par[i] = par[par[i]]; i = par[i]
        return i
    def join(par, a, b): par[find(par,a)] = find(par,b)
    def vertex(p, edge, end, point): return p['corner_starts'][(edge+end)%len(p['edges'])]+point-p['start']
    for p in geometry['polygons']:
        dimension={'prism':0,'face_strip':1,'edge_cap':2}[p['kind']]
        for point in range(p['start'],p['stop']): handles[point]=dimension
    for g in geometry['gluings']:
        p,q=geometry['polygons'][g['left']],geometry['polygons'][g['right']]
        for rank in range(g['rank_start'],g['rank_stop']):
            a=g['left_map'][0]*rank+g['left_map'][1];b=g['right_map'][0]*rank+g['right_map'][1]
            join(parent,a,b);edges-=1
            for end in (0,1):
                other=end^g['ends_reverse']; x=vertex(p,g['left_edge'],end,a); y=vertex(q,g['right_edge'],other,b)
                join(corner,x,y)
                # Link endpoint 0 follows the polygon's outgoing edge; 1 is incoming.
                join(link,2*x+end,2*y+other)
            adjacency[a].append((b,int(g['fibre_flip']),int(not g['ends_reverse'])))
            adjacency[b].append((a,int(g['fibre_flip']),int(not g['ends_reverse'])))
    colours=[{},{}];bad=[set(),set()]
    for mode in (0,1):
        for start in range(n):
            if start in colours[mode]:continue
            colours[mode][start]=0;pending=[start]
            for a in pending:
                for b,fibre,orientation in adjacency[a]:
                    expected=colours[mode][a]^(fibre if mode==0 else orientation)
                    if b not in colours[mode]:colours[mode][b]=expected;pending.append(b)
                    elif colours[mode][b]!=expected:bad[mode].add(find(parent,start))
    assert bad[0]==bad[1],('fibre/base orientation disagreement',bad)
    # Each quotient corner must have a single interval or circle as its link.
    link_graph=defaultdict(list); link_owners={}; link_degrees=Counter()
    for v in range(csize):
        a,b=find(link,2*v),find(link,2*v+1);owner=find(corner,v)
        for point in (a,b):
            assert link_owners.setdefault(point,owner)==owner
            link_degrees[point]+=1
        link_graph[a].append(b);link_graph[b].append(a)
    seen=set(); checked_links=set()
    for start in link_graph:
        if start in seen:continue
        owner=link_owners[start];assert owner not in checked_links, 'disconnected vertex link'
        checked_links.add(owner);pending=[start];seen.add(start);ends=0
        for point in pending:
            assert link_degrees[point] in (1,2), 'branched vertex link'
            ends+=link_degrees[point]==1
            for target in link_graph[point]:
                if target not in seen:seen.add(target);pending.append(target)
        assert ends in (0,2), 'invalid vertex link ends'
    owners={};counts=defaultdict(lambda:[0,0,0,0,0,0]) # V,E,F,h0,h1,h2
    for p in geometry['polygons']:
        for point in range(p['start'],p['stop']):
            root=find(parent,point);row=counts[root];row[2]+=1;row[3+handles[point]]+=1
            row[1]+=len(p['edges'])
            for i in range(len(p['edges'])):
                v=find(corner,p['corner_starts'][i]+point-p['start'])
                assert owners.setdefault(v,root)==root
    for root in owners.values():counts[root][0]+=1
    for g in geometry['gluings']:
        for rank in range(g['rank_start'],g['rank_stop']):
            point=g['left_map'][0]*rank+g['left_map'][1];counts[find(parent,point)][1]-=1
    bp={};boundary_vertices=set();core_vertices=set();portsets=defaultdict(list);old_edges=Counter()
    def bfind(i):
        bp.setdefault(i,i)
        while bp[i]!=i:bp[i]=bp[bp[i]];i=bp[i]
        return i
    for e in geometry['free_edges']:
        p=geometry['polygons'][e['polygon']]
        for rank in range(e['rank_start'],e['rank_stop']):
            point=p['start']+rank-1;root=find(parent,point)
            a=find(corner,vertex(p,e['edge'],0,point));b=find(corner,vertex(p,e['edge'],1,point))
            bp[bfind(a)]=bfind(b);boundary_vertices.update((a,b))
            if e['original_boundary']:old_edges[root]+=1
            else:core_vertices.update((a,b));portsets[root].append(e['port'])
    boundary_counts=Counter(owners[v] for v in {bfind(i)for i in boundary_vertices})
    profiles=Counter()
    for root,(v,e,f,h0,h1,h2)in counts.items():
        chi=v-e+f;b=boundary_counts[root];orientable=root not in bad[0]
        if orientable:assert (2-b-chi)%2==0 and 2-b-chi>=0
        else:assert 2-b-chi>=1
        profiles[(chi,b,orientable,h0,h1,h2,old_edges[root],tuple(sorted(portsets[root])))]+=1
    base_chi=sum(v-e+f for v,e,f,*_ in counts.values());attach_chi=len(core_vertices)-len(geometry['ports'])
    selected=sum((1 if p['kind']!='face_strip' else -1)*(p['stop']-p['start'])for p in geometry['polygons'])
    assert base_chi-attach_chi==selected,(base_chi,attach_chi,selected)
    return dict(profiles=profiles,base_components=len(counts),base_euler_characteristic=base_chi,
                attachment_euler_characteristic=attach_chi,vertex_links_checked=len(checked_links),vertices=len(owners),edges=edges,faces=n)


def audit(output):
    """Replay source geometry and compare every finite base with literal links."""
    from contextlib import ExitStack
    from hashlib import sha256
    import json
    from pathlib import Path
    import random
    from time import perf_counter
    from unittest.mock import patch
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from normal_orbit_research.fixtures import layered_torus
    from normal_orbit_research import seeds
    from tests.test_normal_surface_orbits import relabel
    root=Path(__file__).resolve().parents[2];data=root/'synthesis/data';began=perf_counter();pins=seeds.sources()
    bank={r['id']:r for r in json.loads((root/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot=json.loads((data/'complement-chamber-pilot.json').read_text())
    old=json.loads((data/'cut-complement-audit.json').read_text())
    cases=[(f"pilot/{r['id']}/{r['index']}",bank[r['id']]['triangulation'],r['coordinates'])for r in pilot['records']]
    cases.extend((r['id'],r['triangulation'],r['coordinates'])for r in old['source_proofs']if '/mixed' in r['id'])
    raw,meridian=layered_torus(1)
    for kind,base in (('meridian',meridian),('link',[[1,1,1,1,0,0,0]]),('mobius',[[0,0,0,0,0,1,0]])):
        for n in range(12):cases.append((f'analytic/{kind}/{n}',raw,[[n*x for x in row]for row in base]))
    rng=random.Random(2610128)
    for t in (1,2,4):
        raw,base=layered_torus(t);rows=[[3*x for x in row]for row in base]
        for i in range(12):
            changed,vector=relabel(raw,rows,rng);cases.append((f'relabel/{t}/{i}',changed,vector))
    disabled=('fastunknot.normal_parallelity.normal_cut_parallelity','fastunknot.normal_parallelity._parallelity_geometry',
              'fastunknot.normal_parallelity._systems','fastunknot.normal_parallelity._summary',
              'fastunknot.normal_cut_boundary._cycle_recipes','fastunknot.weighted_transversal._tagged_replay')
    def encode(value):return json.dumps(json_safe(value),sort_keys=True,separators=(',',':')).encode()
    def replay(raw,rows,proof):
        with ExitStack() as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            assert verify_normal_cut_parallelity(raw,rows,proof)
    records=[];proofs=[];kept=set();links=polygons=0
    for i,(name,raw,rows) in enumerate(cases):
        result=normal_cut_parallelity(raw,rows,record_certificate=True);replay(raw,rows,result['certificate'])
        literal=literal_base(result['geometry'],max_points=100000)
        expected=Counter()
        for p in result['summary']['base_profiles']:
            expected[(p['euler_characteristic'],p['boundary_components'],p['orientable'],*p['handles'],p['original_boundary_edges'],tuple(p['core_ports']))]+=p['multiplicity']
        assert expected==literal['profiles'],name
        assert result['summary']['attachment_euler_characteristic']==literal['attachment_euler_characteristic'],name
        links+=literal['vertex_links_checked'];polygons+=literal['faces']
        records.append(dict(id=name,source_tetrahedra=len(rows),normal_discs=sum(map(sum,rows)),
            core_handle_counts=result['summary']['core_handle_counts'],base_components=literal['base_components'],
            base_euler_characteristic=literal['base_euler_characteristic'],vertex_links_checked=literal['vertex_links_checked'],
            proof_sha256=sha256(encode(result['certificate'])).hexdigest()))
        group=name.split('/')[1]if name.startswith('pilot/')else name
        if name.startswith('pilot/')and group not in kept or '/mixed' in name or name.startswith('relabel/')and name.endswith('/0'):
            kept.add(group);proofs.append(dict(id=name,triangulation=raw,coordinates=rows,certificate=result['certificate']))
        if i%200==0:print('parallelity cases',i+1,flush=True)
    large=[]
    for t,bits in ((1,128),(1,500),(4,128),(4,500),(16,128),(16,500),(1,16384)):
        raw,base=layered_torus(t);n=1<<bits;rows=[[n*x for x in row]for row in base]
        result=normal_cut_parallelity(raw,rows,record_certificate=True)
        replay(raw,json_safe(rows),json.loads(encode(result['certificate'])))
        assert result['summary']['core_handle_counts']==[4*t,6*t-3,2*t-2,0]
        g=result['geometry'];large.append(dict(tetrahedra=t,multiplicity_bits=n.bit_length(),polygon_families=len(g['polygons']),
            gluing_families=len(g['gluings']),core_handles=sum(result['summary']['core_handle_counts']),ports=len(g['ports'])))
        proofs.append(dict(id=f'binary/{t}/{bits}',triangulation=raw,coordinates=rows,certificate=result['certificate']))
    assert pins==seeds.sources()
    result=dict(native_source_sha256=pins,finite_cases=len(records),pilot_cases=len(pilot['records']),
        literal_vertex_links_checked=links,literal_polygons=polygons,large_binary_cases=large,records=records,source_proofs=proofs,
        native_seconds=perf_counter()-began,pilot_sha256=sha256((data/'complement-chamber-pilot.json').read_bytes()).hexdigest(),
        corpus_sha256=sha256((root/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest())
    Path(output).write_bytes(encode(result)+b'\n')
    print(json.dumps({k:result[k]for k in ('finite_cases','pilot_cases','literal_vertex_links_checked','literal_polygons','native_seconds')}),flush=True)


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',required=True)
    audit(parser.parse_args().output)
