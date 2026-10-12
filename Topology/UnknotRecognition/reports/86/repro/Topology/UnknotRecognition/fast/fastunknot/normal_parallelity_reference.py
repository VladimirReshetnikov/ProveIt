"""Independent parallelity reconstruction from verified raw cut-cell incidences."""
from itertools import combinations

from .normal_surface_geometry import _edge, _quad
from .normal_cut_cells_verify import _reference_cells


def _links(prepared,check):
    groups={}
    for t in range(len(prepared['tetrahedra'])):
        for a,b in combinations(range(4),2):groups.setdefault(prepared['edge_roots'][_edge(t,a,b)],[]).append((t,a,b))
    answer={}
    for root,local in sorted(groups.items()):
        if root in prepared['boundary_incidence']:continue
        opposite={};cross={}
        for t,a,b in local:
            faces=[f for f in range(4)if f not in(a,b)]
            for f in faces:
                check();opposite[t,a,b,f]=(t,a,b,next(g for g in faces if g!=f))
                e=prepared['tetrahedra'][t][f];u,p=e['tetrahedron'],e['permutation'];c,d=sorted((p[a],p[b]))
                cross[t,a,b,f]=(u,c,d,p[f])
        first=min(opposite);flag=first;rows=[]
        while True:
            check();t,a,b,entry=flag;_,_,_,exit=opposite[flag];target=cross[t,a,b,exit]
            rows.append(dict(tetrahedron=t,edge=[a,b],entry_face=entry,exit_face=exit,
                             target_tetrahedron=target[0],target_edge=list(target[1:3]),target_face=target[3]))
            flag=target
            if flag==first:break
            if len(rows)>len(local):raise ArithmeticError('reference edge link failed')
        answer[root]=rows
    return answer


def _reference_parallelity(prepared,analysed,check):
    raw=_reference_cells(prepared,analysed,check);rows=analysed['rows'];links=_links(prepared,check)
    face_families={};normal_families={};chamber_families={};edges={}
    for f in raw['faces']:
        if f['kind']=='horizontal':normal_families[f['tetrahedron'],f['column'],f['side']]=f
        else:face_families[f['tetrahedron'],f['face'],f.get('corner',-1)]=f
    for c in raw['chambers']:chamber_families[c['tetrahedron'],c.get('corner',-1)]=c
    for e in raw['edges']:
        if e['kind']=='source_edge':edges[e['edge']]=e
    def owner(t,f,v):
        e=prepared['tetrahedra'][t][f]
        if e is None:return t,f,v,None
        u,p=e['tetrahedron'],e['permutation'];g=p[f]
        return(t,f,v,None)if(t,f)<(u,g)else(u,g,p[v]if v>=0 else -1,p)
    def face_cell(t,f,v,r):
        u,g,w,_=owner(t,f,v);return face_families[u,g,w]['start']+r
    def face_chamber(t,f,cell):
        candidates=[i for i in raw['face_incidence']if i['kind']=='original'and i['tetrahedron']==t and i['face']==f and i['face_start']<=cell<i['face_stop']]
        if len(candidates)!=1:raise ArithmeticError('reference face/chamber address ambiguous')
        s,o=candidates[0]['chamber'];return s*cell+o
    def edge_face(root,t,f,e,rank):
        u,g,_,p=owner(t,f,-1);ce=e if p is None else sorted(p[v]for v in e)
        candidates=[i for i in edges[root]['incidences']if i['tetrahedron']==u and i['local_face']==g and i['local_edge']==ce and i['rank_start']<=rank<i['rank_stop']]
        if len(candidates)!=1:raise ArithmeticError('reference edge/face address ambiguous')
        s,o=candidates[0]['face'];return s*rank+o
    core0=[];by_point={}
    for c in raw['chambers']:
        t=c['tetrahedron'];count=c['stop']-c['start']
        if c['kind']=='chain':marks=[(c['start'],'central'if count==1 else'quad_a',None)]+([]if count==1 else[(c['stop']-1,'quad_b',None)])
        else:marks=[(c['start'],'triangle_tip',c['corner'])]
        for point,name,v in marks:
            by_point[point]=len(core0);core0.append(dict(id=len(core0),tetrahedron=t,kind=name,vertex=v,source_chamber=point))
    core1=[];by_face={};core_face={}
    for t,f,u,g,p in prepared['pairs']:
        for v in [-1]+[v for v in range(4)if v!=f and(t,f,v)in face_families]:
            cell=face_families[t,f,v]['start'];index=len(core1);by_face[cell]=index;core_face[t,f,v]=index
            core1.append(dict(id=index,tetrahedron=t,face=f,corner=v,
                ends=[by_point[face_chamber(t,f,cell)],by_point[face_chamber(u,g,cell)]],
                target_tetrahedron=u,target_face=g,permutation=list(p)))
    core2=[]
    for root,wedges in links.items():
        w=edges[root]['stop']-edges[root]['start']-1
        for r in ([0]if w==0 else[0,w]):
            cycle=[]
            for s in wedges:
                t,f,e=s['tetrahedron'],s['exit_face'],s['edge'];cell=edge_face(root,t,f,e,r)
                cycle.extend([dict(dimension=0,handle=by_point[face_chamber(t,f,cell)],tetrahedron=t,local_edge=e),
                              dict(dimension=1,handle=by_face[cell],tetrahedron=t,face=f,
                                   corner=next(v for (tt,ff,v),family in face_families.items()if family['start']==cell and tt==owner(t,f,-1)[0]and ff==owner(t,f,-1)[1]))])
                # The source-cycle label uses the local corner, not the owner.
                label=cycle[-1];canonical=label['corner'];entry=prepared['tetrahedra'][t][f]
                if canonical>=0 and owner(t,f,-1)[3]is not None:label['corner']=entry['permutation'].index(canonical)
            core2.append(dict(id=len(core2),edge=root,rank=r,cycle=cycle))
    core3=[]
    for v in raw['vertices']:
        if v['kind']=='original'and not v['boundary']:
            group=[[t,w]for t in range(len(rows))for w in range(4)if prepared['vertex_roots'][4*t+w]==v['root']]
            core3.append(dict(id=len(core3),vertex=v['root'],link_triangles=group))

    polygons=[];p0={};p1={};p2={};size=0
    for t,row in enumerate(rows):
        for col,m in enumerate(row):
            if m<2:continue
            index=len(polygons);p0[t,col]=index;vertices=[];boundary=[];cycle=normal_families[t,col,0]['cycle']
            for i,a in enumerate(cycle):
                f,v=a['face'],a['corner'];other=[x for x in range(4)if x not in(f,v)]
                if not a['forward']:other.reverse()
                first,last=[sorted((v,x))for x in other]
                slope,offset=a['rank'];offset+=int(col>=4 and v not in{0,col-3})
                vertices.extend([dict(edge=first,face=f),dict(edge=last,face=f)])
                boundary.append(dict(kind='face',face=f,corner=v,rank=[slope,offset]))
                # Corner rank is obtained below from raw incidence inverses.
                boundary.append(dict(kind='corner',edge=last,root=prepared['edge_roots'][_edge(t,*last)],rank=None))
            polygons.append(dict(id=index,kind='prism',tetrahedron=t,column=col,start=size,stop=size+m-1,
                rank_start=1,rank_stop=m,vertices=vertices,edges=boundary));size+=m-1
    for f in raw['faces']:
        if f['kind']!='original_arm'or f['boundary']or f['stop']-f['start']<2:continue
        t,face,v=f['tetrahedron'],f['face'],f['corner'];entry=prepared['tetrahedra'][t][face];p=entry['permutation'];u,g=entry['tetrahedron'],p[face]
        m=f['stop']-f['start'];other=[x for x in range(4)if x not in(face,v)];index=len(polygons);p1[t,face,v]=index
        polygons.append(dict(id=index,kind='face_strip',tetrahedron=t,face=face,corner=v,target_tetrahedron=u,target_face=g,
            permutation=list(p),start=size,stop=size+m-1,rank_start=1,rank_stop=m,
            vertices=[dict(end=e,branch=b)for e,b in((0,0),(1,0),(1,1),(0,1))],
            edges=[dict(kind='side',branch=0,edge=sorted((v,other[0]))),dict(kind='end',end=1),
                   dict(kind='side',branch=1,edge=sorted((v,other[1]))),dict(kind='end',end=0)]));size+=m-1
    for root,wedges in links.items():
        w=analysed['weights'][root]
        if w<2:continue
        vertices=[];boundary=[];index=len(polygons);p2[root]=index
        for s in wedges:
            t,e,a,b=s['tetrahedron'],s['edge'],s['entry_face'],s['exit_face']
            vertices.extend([dict(tetrahedron=t,edge=e,face=a),dict(tetrahedron=t,edge=e,face=b)])
            tt,ff,_,p=owner(t,b,-1);ce=e if p is None else sorted(p[x]for x in e)
            boundary.extend([dict(kind='tetrahedron_sector',tetrahedron=t,edge=e),dict(kind='face_sector',tetrahedron=tt,face=ff,edge=ce)])
        polygons.append(dict(id=index,kind='edge_cap',edge=root,start=size,stop=size+w-1,rank_start=1,rank_stop=w,
                             vertices=vertices,edges=boundary));size+=w-1
    def prism_face_map(p,f,v):
        t,col=p['tetrahedron'],p['column'];c=chamber_families[t,col if col<4 else -1]['start']
        tt,ff,vv,_=owner(t,f,v);family=face_families[tt,ff,vv]
        candidates=[]
        for i in raw['face_incidence']:
            if i['kind']!='original'or i['tetrahedron']!=t or i['face']!=f or i['corner']!=v:continue
            s,o=i['chamber'];lo=s*(c+p['rank_start']-o);hi=s*(c+p['rank_stop']-1-o)
            if min(lo,hi)>=max(i['face_start'],family['start'])and max(lo,hi)<min(i['face_stop'],family['stop']):candidates.append((s,s*(c-o)))
        if len(candidates)!=1:raise ArithmeticError('prism reference carrier ambiguous')
        return candidates[0],family
    def inverse_gap(root,t,f,e,mapping,lo,hi):
        tt,ff,_,p=owner(t,f,-1);ce=e if p is None else sorted(p[x]for x in e);a,b=mapping;candidates=[]
        for i in edges[root]['incidences']:
            if i['tetrahedron']!=tt or i['local_face']!=ff or i['local_edge']!=ce:continue
            s,o=i['face'];first=s*(a*lo+b-o);last=s*(a*(hi-1)+b-o)
            if min(first,last)>=i['rank_start']and max(first,last)<i['rank_stop']:candidates.append((s*a,s*(b-o)))
        if len(candidates)!=1:raise ArithmeticError('gap reference inverse ambiguous')
        return candidates[0]
    mappings={}
    for p in polygons:
        if p['kind']!='prism':continue
        for e in p['edges']:
            if e['kind']=='face':mappings[p['id'],e['face'],e['corner']]=prism_face_map(p,e['face'],e['corner'])
        for slot,e in enumerate(p['edges']):
            if e['kind']!='corner':continue
            flag=p['vertices'][slot];f=flag['face'];arc=next(a for a in p['edges']if a['kind']=='face'and a['face']==f)
            mapping,_=mappings[p['id'],f,arc['corner']]
            e['rank']=list(inverse_gap(e['root'],p['tetrahedron'],f,e['edge'],mapping,p['rank_start'],p['rank_stop']))
    gluings=[]
    def add(p,slot,q,eslot,mapping,reverse,fibre):
        gluings.append(dict(left=p['id'],left_edge=slot,right=q['id'],right_edge=eslot,rank_start=p['rank_start'],rank_stop=p['rank_stop'],
                            left_map=[1,p['start']-1],right_map=list(mapping),ends_reverse=bool(reverse),fibre_flip=bool(fibre)))
    for p in polygons:
        if p['kind']=='prism':
            t=p['tetrahedron']
            for slot,e in enumerate(p['edges']):
                first=p['vertices'][slot]
                if e['kind']=='face':
                    f,v=e['face'],e['corner'];entry=prepared['tetrahedra'][t][f]
                    if entry is None:continue
                    tt,ff,vv,transform=owner(t,f,v);q=polygons[p1[tt,ff,vv]];end=int(transform is not None);eslot=1 if end else 3
                    other=next(x for x in first['edge']if x!=v)
                    if transform is not None:other=transform[other]
                    branch=[x for x in range(4)if x not in(ff,vv)].index(other)
                    (s,o),family=mappings[p['id'],f,v]
                    add(p,slot,q,eslot,(s,o-family['start']+q['start']-1),q['vertices'][eslot]!=dict(end=end,branch=branch),s<0)
                elif e['root']not in prepared['boundary_incidence']:
                    q=polygons[p2[e['root']]];eslot=next(i for i,a in enumerate(q['edges'])if a['kind']=='tetrahedron_sector'and a['tetrahedron']==t and a['edge']==e['edge'])
                    s,o=e['rank'];add(p,slot,q,eslot,(s,o+q['start']-1),q['vertices'][eslot]['face']!=first['face'],s<0)
        elif p['kind']=='face_strip':
            t,f,v=p['tetrahedron'],p['face'],p['corner'];family=face_families[t,f,v]
            for slot in(0,2):
                e=p['edges'][slot];root=prepared['edge_roots'][_edge(t,*e['edge'])]
                if root in prepared['boundary_incidence']:continue
                q=polygons[p2[root]];eslot=next(i for i,a in enumerate(q['edges'])if a['kind']=='face_sector'and a['tetrahedron']==t and a['face']==f and a['edge']==e['edge'])
                s,o=inverse_gap(root,t,f,e['edge'],(1,family['start']),p['rank_start'],p['rank_stop'])
                first=p['vertices'][slot];wanted=t if first['end']==0 else p['target_tetrahedron'];wanted_f=f if first['end']==0 else p['target_face']
                start=q['vertices'][eslot];reverse=start['tetrahedron']!=wanted or start['face']!=wanted_f
                add(p,slot,q,eslot,(s,o+q['start']-1),reverse,s<0)
    covered={(p['id'],i):[]for p in polygons for i in range(len(p['edges']))}
    for g in gluings:
        for name in('left','right'):
            p=polygons[g[name]];s,o=g[name+'_map'];a=s*g['rank_start']+o;b=s*(g['rank_stop']-1)+o
            covered[p['id'],g[name+'_edge']].append((min(a,b)-p['start']+1,max(a,b)-p['start']+2))
    free=[];ports=[]
    for p in polygons:
        for slot,e in enumerate(p['edges']):
            first=p['rank_start'];gaps=[]
            for a,b in sorted(covered[p['id'],slot]):
                if a<first:raise ArithmeticError('reference parallel edge overlaps')
                if first<a:gaps.append((first,a))
                first=b
            if first<p['rank_stop']:gaps.append((first,p['rank_stop']))
            if p['kind']=='edge_cap'and e['kind']=='tetrahedron_sector':
                # Pull each core chamber back through a raw edge/face/volume
                # incidence. This splits adjacent different core contacts.
                t,local=e['tetrahedron'],e['edge'];face=p['vertices'][slot]['face'];root=p['edge'];tt,ff,_,transform=owner(t,face,-1)
                ce=local if transform is None else sorted(transform[x]for x in local);split=[]
                for lo,hi in gaps:
                    found=[]
                    for i in edges[root]['incidences']:
                        if i['tetrahedron']!=tt or i['local_face']!=ff or i['local_edge']!=ce:continue
                        si,oi=i['face']
                        for use in raw['face_incidence']:
                            if use['kind']!='original'or use['tetrahedron']!=t or use['face']!=face:continue
                            sj,oj=use['chamber'];s=sj*si;o=sj*oi+oj
                            for core in core0:
                                if core['tetrahedron']!=t:continue
                                rank=s*(core['source_chamber']-o);cell=si*rank+oi
                                if lo<=rank<hi and i['rank_start']<=rank<i['rank_stop']and use['face_start']<=cell<use['face_stop']:found.append(rank)
                    found=sorted(set(found))
                    if len(found)!=hi-lo:raise ArithmeticError('reference cap/core inverse incomplete')
                    split.extend((r,r+1)for r in found)
                gaps=split
            for lo,hi in gaps:
                check();boundary=False;dim=None;handle=None
                if p['kind']=='prism':boundary=prepared['tetrahedra'][p['tetrahedron']][e['face']]is None if e['kind']=='face'else e['root']in prepared['boundary_incidence']
                elif p['kind']=='face_strip':
                    if e['kind']=='side':boundary=prepared['edge_roots'][_edge(p['tetrahedron'],*e['edge'])]in prepared['boundary_incidence']
                    else:
                        t,f=(p['tetrahedron'],p['face'])if e['end']==0 else(p['target_tetrahedron'],p['target_face'])
                        v=p['corner'];cell=face_cell(p['tetrahedron'],p['face'],v,lo);dim=0;handle=by_point[face_chamber(t,f,cell)]
                elif e['kind']=='tetrahedron_sector':
                    t=e['tetrahedron'];f=p['vertices'][slot]['face'];cell=edge_face(p['edge'],t,f,e['edge'],lo);dim=0;handle=by_point[face_chamber(t,f,cell)]
                else:
                    cell=edge_face(p['edge'],e['tetrahedron'],e['face'],e['edge'],lo);dim=1;handle=by_face[cell]
                if not boundary and(hi-lo!=1 or dim is None):raise ArithmeticError('reference free core edge not singleton')
                record=dict(polygon=p['id'],edge=slot,rank_start=lo,rank_stop=hi,original_boundary=boundary)
                if not boundary:
                    record['port']=len(ports);ports.append(dict(id=len(ports),polygon=p['id'],edge=slot,rank=lo,core_dimension=dim,core_handle=handle))
                free.append(record)
    corner_size=0
    for p in polygons:
        p['corner_starts']=[]
        for _ in p['vertices']:p['corner_starts'].append(corner_size);corner_size+=p['stop']-p['start']
    return dict(polygon_points=size,corner_points=corner_size,polygons=polygons,gluings=gluings,free_edges=free,ports=ports,
                core=dict(handles0=core0,handles1=core1,handles2=core2,handles3=core3),source=raw['source'],coordinates=raw['coordinates'])
