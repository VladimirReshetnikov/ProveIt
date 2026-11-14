#!/usr/bin/env python3
import collections,csv,hashlib,json,pathlib,shutil
B=pathlib.Path(__file__).resolve().parent
OLD=B/'annotations'
census=json.loads((B/'current_census.json').read_text())
bysha={r['sha256']:r for r in census['identities']}
paths=collections.defaultdict(list)
for r in census['occurrences']:paths[r['sha256']].append(r['path'])
old=json.loads((OLD/'prior_frontier194.json').read_text())
frontier=[]
for r in old:
 h=r['representative_sha256']; current=bysha[h]
 role='auxiliary' if r['status'].startswith('Auxiliary') else 'rejected' if r['name'].startswith('Rejected') else 'reported_supported'
 # Prefer the current physical path, not obsolete incoming paths in the old census.
 ps=sorted(paths[h],key=lambda p:('!' in p,len(p),p))
 frontier.append(dict(name=r['name'],states=194,role=role,change=r['change'],
     evidence_status=r['status'],sha256=h,rooted_machine_class=current['machine'],
     table_class=current['table'],start=current['start'],representative=ps[0]))
new=[
 ('PA194H','3276a34fd0388102dad87a8b12c70e88b2bcccf6b068cb034ce78d33536adcc1','No-push MP returns consequent in visible top, retaining offset; Shift tests only cached head. Nonsymmetric comparison.'),
 ('PA194HS = PA194NS','19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1','No-push MP returns consequent in visible top, retaining offset; cached-head-only Shift with symmetric comparison. HS and NS are byte-identical.'),
 ('PA194N5','b521b1086ad29abdaf213feac2a3d2c0eb1bba7524c36e7f627763aeb2377b09','No-push successful MP composed with coefficient-5 formula constructors; original Shift.'),
 ('PA194N6','36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4','No-push successful MP composed with coefficient-6 formula constructors; original Shift. Two incoming packages have identical machine bytes.')]
for name,h,change in new:
 r=bysha[h]
 ps=sorted(paths[h],key=lambda p:('comparison' in p,len(p),p))
 frontier.append(dict(name=name,states=194,role='reported_supported',change=change,evidence_status='Incoming ordinary PA proof and reported full universal source/tape verification; proof/calibration reviewed, historical verifier not rerun for this inventory.',sha256=h,rooted_machine_class=r['machine'],table_class=r['table'],start=r['start'],representative=ps[0]))
assert len(frontier)==34 and len({r['table_class'] for r in frontier})==34
assert {r['table_class'] for r in frontier}=={r['table'] for r in census['identities'] if r['states']==194}
for r in frontier:
 same=[s for s in census['identities'] if s['table']==r['table_class']]
 r['current_byte_forms']=len(same)
 r['current_occurrences']=sum(len(paths[s['sha256']]) for s in same)
 r['all_current_paths']=sorted(p for s in same for p in paths[s['sha256']])
 td=B/'comparison_tables';td.mkdir(exist_ok=True)
 r['comparison_table']='comparison_tables/'+r['sha256']+'.tm'
 src=B/'tables'/str(r['sha256']+'.tm')
 if src.exists():shutil.copyfile(src,B/r['comparison_table'])
 elif not (B/r['comparison_table']).exists():raise FileNotFoundError(str(src))
frontier.sort(key=lambda r:(r['role'],r['name']))
(B/'frontier194.json').write_text(json.dumps(frontier,indent=2)+'\n')
with (B/'frontier194.csv').open('w') as f:
 cols=[k for k in frontier[0] if k!='all_current_paths'];w=csv.DictWriter(f,fieldnames=cols,extrasaction='ignore');w.writeheader();w.writerows(frontier)
packets=json.loads((OLD/'prior_packet_ledger.json').read_text())
for r in packets:
 r['kind']='placed';r['location']='Computability/BusyBeaver/Research/PA/docs/'+r['packet']
 r['scope']='Main README reviewed against the pinned source tree; contribution is historical, not a fresh replay of every proof.'
newpack=[
 ('pa194hs_conpa_2026-11-13','H and HS: no-push MP plus cached-head-only Shift. HS is byte-identical to separately delivered NS; H is its nonsymmetric variant.'),
 ('pa194n5_n6_conpa_2026-11-13','N5 and N6: no-push MP composed with coefficients 5 and 6. N6 repeats the separate N6 research machine exactly.'),
 ('pa194n6_research_2026-11-13','N6: coefficient-six constructors plus no-push MP; this machine is byte-identical to N6 in the N5/N6 packet.'),
 ('pa194ns_conpa_2026-11-13','NS: no-push visible-top MP plus symmetric cached-head Shift; byte-identical to HS.')]
for name,desc in newpack:
 packets.append(dict(packet=name,kind='incoming',location='docs/incoming/'+name+'.zip',reported_contribution=desc,scope='Main report/proof reviewed; byte identity and graph identity freshly recomputed; universal historical physical verifier not rerun in this inventory.'))
assert len(packets)==51
(B/'packet_ledger.json').write_text(json.dumps(packets,indent=2)+'\n')
with (B/'packet_ledger.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=sorted({k for r in packets for k in r}));w.writeheader();w.writerows(packets)
print(json.dumps({'snapshot':census['summary']['snapshot'],'packets':len(packets),'frontier_classes':len(frontier),'roles':dict(collections.Counter(r['role'] for r in frontier))},indent=2))
