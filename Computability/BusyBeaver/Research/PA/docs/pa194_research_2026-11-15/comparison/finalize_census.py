#!/usr/bin/env python3
"""Split inherited all-roots keys by exact whole-table isomorphism when needed."""
import argparse,collections,hashlib,io,json,pathlib,tempfile,zipfile
import novelty
HERE=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('source',type=pathlib.Path)
ap.add_argument('--census',type=pathlib.Path,required=True)
ap.add_argument('--representatives',type=pathlib.Path,required=True)
args=ap.parse_args()
ROOT=args.source
CS=args.census
records=json.loads((CS/'files.json').read_text())
classes=json.loads((CS/'classes.json').read_text())
by_path={r['path']:r for r in records}
archives={}
def read(loc):
    bits=loc.split('!')
    if len(bits)==1:return (ROOT/bits[0]).read_bytes()
    key=bits[0]
    if key not in archives:archives[key]=zipfile.ZipFile(ROOT/key)
    for member in bits[1:-1]:
        nextkey=key+'!'+member
        if nextkey not in archives:archives[nextkey]=zipfile.ZipFile(io.BytesIO(archives[key].read(member)))
        key=nextkey
    return archives[key].read(bits[-1])
scratch=tempfile.TemporaryDirectory(prefix='pa194-census-')
final=[];audit=[]
for c in classes:
    if c['full_graph_root']:
        final.append({**c,'whole_graph_class':c['table_class']});continue
    groups=[];seen={}
    for loc in c['paths']:
        sha=by_path[loc]['sha256']
        if sha in seen:groups[seen[sha]]['paths'].append(loc);continue
        data=read(loc)
        assert hashlib.sha256(data).hexdigest()==sha,loc
        p=pathlib.Path(scratch.name)/(sha+'.tm');p.write_bytes(data)
        graph,_=novelty.parse(p,loose=False)
        for i,g in enumerate(groups):
            if novelty.isomorphic(graph,g['graph']) is not None:
                g['paths'].append(loc);g['bytes'].append(sha);seen[sha]=i;break
        else:
            seen[sha]=len(groups);groups.append({'graph':graph,'bytes':[sha],'paths':[loc]})
    for i,g in enumerate(groups):
        final.append({**c,'paths':g['paths'],'byte_versions':len(g['bytes']),
                      'file_count':len(g['paths']),
                      'whole_graph_class':c['table_class']+(f':full{i+1}' if len(groups)>1 else '')})
    audit.append({'inherited_key':c['table_class'],'working_states':c['states'],
                  'whole_graph_classes':len(groups),'byte_payloads':sum(len(g['bytes']) for g in groups),
                  'class_payloads':[g['bytes'] for g in groups]})
(CS/'whole_graph_classes.json').write_text(json.dumps(final,indent=2)+'\n')
(CS/'disconnected_audit.json').write_text(json.dumps(audit,indent=2)+'\n')
s=json.loads((CS/'summary.json').read_text())
s['inherited_key_classes']=s.pop('graph_classes')
s['inherited_key_classes_by_states']=s.pop('classes_by_states')
s['exact_whole_graph_classes']=len(final)
s['exact_whole_graph_classes_by_states']=dict(sorted(collections.Counter(c['states'] for c in final).items()))
s['spanning_194_classes']=sum(c['states']==194 and c['full_graph_root'] for c in final)
s['nonspanning_194_classes']=sum(c['states']==194 and not c['full_graph_root'] for c in final)
s['spanning_193_classes']=sum(c['states']==193 and c['full_graph_root'] for c in final)
s['canonicalizer_correction']='The inherited all-roots key collapses two nonisomorphic 194-control diagnostics whose largest reachable components have only 3 states. Exact whole-table matching separates them. All other nonspanning groups were also checked.'
(CS/'final_summary.json').write_text(json.dumps(s,indent=2)+'\n')
(CS/'strict_summary.json').write_text(json.dumps(s,indent=2)+'\n')
OUT=args.representatives;OUT.mkdir(parents=True,exist_ok=True);index=[]
for c in final:
    if c['states']!=194:continue
    loc=min(c['paths'],key=lambda p:(not by_path[p]['declared'],len(p),p))
    f=c['whole_graph_class'].replace(':','_')+'.tm'
    data=read(loc)
    assert hashlib.sha256(data).hexdigest()==by_path[loc]['sha256'],loc
    (OUT/f).write_bytes(data)
    index.append({'table_class':c['table_class'],'whole_graph_class':c['whole_graph_class'],
                  'full_graph_root':c['full_graph_root'],'start':by_path[loc]['start'],
                  'declared':by_path[loc]['declared'],'sha256':by_path[loc]['sha256'],
                  'source':loc,'representative':f})
old=json.loads((OUT/'index.json').read_text()) if (OUT/'index.json').exists() else [];keep={x['representative'] for x in index}
for r in old:
    if r['representative'] not in keep:(OUT/r['representative']).unlink()
(OUT/'index.json').write_text(json.dumps(index,indent=2)+'\n')
scratch.cleanup()
print(json.dumps({k:s[k] for k in ('exact_whole_graph_classes','spanning_194_classes','nonspanning_194_classes','spanning_193_classes')},indent=2))
