from pathlib import Path
import json,gzip,hashlib
import argparse
parser=argparse.ArgumentParser(description='Review saved K217 records only; never runs a candidate.')
parser.add_argument('--records',type=Path,required=True,help='Saved fresh-record directory, plain or publication layout')
parser.add_argument('--packet',type=Path,required=True,help='Recovered original K217 packet')
parser.add_argument('--parent',type=Path,required=True,help='Extracted original nested K218 dominated parent')
parser.add_argument('--output',type=Path,required=True,help='New review JSON file')
args=parser.parse_args()
P=args.records.resolve();D=args.packet.resolve();B=args.parent.resolve()
def load(p):
    return json.loads(p.read_bytes() if p.is_file() else gzip.decompress(Path(str(p)+'.gz').read_bytes()))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def saved_path(recorded):
    historical_root=Path(a['jobs'][0]['cwd']).parent
    return P/Path(recorded).relative_to(historical_root)
a=load(P/'actual.json');assert a['status']=='FIVE_SELECTED_LEAVES_PASS'and len(a['jobs'])==5
assert all(j['accepted']and j['exit_code']==0 and not j['timed_out']and saved_path(j['receipt']).is_file()for j in a['jobs'])
assert all((P/'logs'/(j['name']+'.stderr')).read_bytes()==b'' for j in a['jobs'])
for name in ['k217.native.tm','k217.tm','sites217.json','unfolded218.native.tm']:assert(P/'rebuilt'/name).read_bytes()==(D/'machine'/name).read_bytes()
c=load(P/'runtime/runtime_cases.json');sites=load(D/'machine/sites217.json');r=load(P/'runtime/runtime.json');st=load(P/'runtime/startup.json');b=load(P/'blank.json');f=load(P/'fold-window.json');s=load(P/'source-fold.json')
assert r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==r['expected_cases']==6176 and not r['failures']and r['working_states']==217
assert r['table_sha256']==sha(D/'machine/k217.native.tm')and r['sites_sha256']==sha(D/'machine/sites217.json')
assert[(x['site_index'],x['positive'])for x in c]==[(i,z)for i,x in enumerate(sites)for z in((False,True)if x[1]=='CD'else(False,))]
assert len(c)==6176 and sum(x['symbolic_steps']for x in c)==1616558
assert all(len(x['duration'])==13 and x['duration'][0]>0 and all(v>=0 for v in x['duration'])for x in c)
assert min(x['duration'][0]for x in c)==13
assert c==json.loads(gzip.decompress((D/'evidence/runtime_cases.json.gz').read_bytes()))
rows={}
for line in (D/'machine/k217.native.tm').read_text().splitlines():
 if line and not line.startswith('#'):
  q,bit,w,d,z=line.split();rows[int(q),int(bit)]=(int(w),d,int(z))
mp={int(k):v for k,v in load(B/'binary/code/inputs/legacy_mapping.json').items()}
for q in {q for q,b in rows}|{254}:mp.setdefault(q,q+1000)
inv={v:k for k,v in mp.items()};used={(inv[q],bit)for x in c for q,bit in x['rows']};assert used==set(rows)and len(rows)==434
assert len(r['blocks'])==4 and all(x['arbitrary_contexts']for x in r['blocks'])
assert(st['steps'],st['state'],st['head'],st['gap'])==(312617,84,-5,80)
assert st['registers']==[3,0,0,0,3,0,0,0,0]and st['spares']==[1]*130 and len(st['trace'])==312617
assert st['one_cells']==b['complete_support']and len(st['one_cells'])==277
assert b['steps']==312617 and b['canonical_blank_startup_pass']and b['trace_rows_independently_replayed']==0
assert f['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'and f['inductive_window_contexts']==962479 and f['negative_control']['status']=='REJECTED'
assert f['maximum_old_block']==1 and f['maximum_new_block']==3
assert s['status']=='INDEPENDENT_SOURCE_ROTATION_AND_ALL_TAPE_FOLD_PASS'and s['complete_final_folded_decoder_binding']and len(s['rotations'])==3
old=load(D/'evidence/runtime.json');diff=[k for k in sorted(set(old)|set(r))if old.get(k)!=r.get(k)];assert diff==['seconds']
result={'status':'INDEPENDENT_FRESH_RECORD_REVIEW_PASS','actual_sha256':sha(P/'actual.json'),'jobs':5,'runtime_cases':len(c),'symbolic_rules':sum(x['symbolic_steps']for x in c),'covered_rows':len(used),'minimum_duration':13,'runtime_seconds':r['seconds'],'startup_steps':312617,'one_cells':277,'fresh_startup_trace_events':len(st['trace']),'independent_blank_stored_trace_rows':0,'startup_independent_complete_support_equal':True,'fresh_cases_identical_delivery':True,'runtime_metadata_differences':diff,'fold_contexts':962479,'negative_control_rejected':True,'scope':'Read-only audit of fresh selected process/output records. No candidate rerun, manifest validation, logical parent replay or proof assistant. Ordinary source and inherited calibration reviewed separately.'}
with args.output.open('x') as output:output.write(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
