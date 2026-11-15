#!/usr/bin/env python3
"""Supplement current .tm census with explicit complete 193/194 JSON tables.

Uses the pinned marker-separation packet's documented JSON recognizer.
Generators, Lean definitions and tables printed only in TeX are not executed.
"""
import argparse,collections,hashlib,importlib.util,io,json,pathlib,re,subprocess,sys,zipfile
HERE=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('source',type=pathlib.Path)
ap.add_argument('--output',type=pathlib.Path,required=True)
ap.add_argument('--tm-census',type=pathlib.Path,default=HERE/'current_census/files.json')
ap.add_argument('--overlay',type=pathlib.Path)
args=ap.parse_args();ROOT=args.source
pinned='d8d4fb10149d6a76a56e615a35648c8c32847cf4'
if (ROOT/'.git').exists():
    actual=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
    if actual!=pinned:raise ValueError('Checkout must be pinned to '+pinned+', got '+actual)
spec=importlib.util.spec_from_file_location('schema_parser',HERE/'schema_parser.py')
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
import machine_classes as mc
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
existing=json.loads(args.tm_census.read_text())
known={r['table'] for r in existing};normcache={};rawcache={};zipseen=set();occ=[];errors=[];payloads=[]
json_payload_occurrences=0
def sha(b):return hashlib.sha256(b).hexdigest()
def analyze(raw,path):
    global json_payload_occurrences
    json_payload_occurrences+=1;bh=sha(raw)
    payloads.append({'path':path,'sha256':bh,'bytes':len(raw)})
    if bh not in rawcache:
        hits=[]
        try:node=json.loads(raw)
        except Exception as e:
            errors.append({'path':path,'error':str(e)});rawcache[bh]=[];return
        todo=[('$',node)]
        while todo:
            ptr,v=todo.pop();d=parser.parse_json_node(v)
            if d:
                n=len(d[1])
                if n in (193,194):
                    norm=parser.normalized(d);h=sha(norm)
                    if h not in normcache:
                        info=mc.classify(norm);info.pop('roots');info['normalized_sha256']=h
                        info['new_to_tm_census']=info['table'] not in known
                        normcache[h]=info
                        (OUT/(h+'.tm')).write_bytes(norm)
                    hits.append({'pointer':ptr,'normalized_sha256':h})
                continue
            if isinstance(v,dict):todo.extend((ptr+'/'+str(k),x) for k,x in v.items() if isinstance(x,(dict,list,str)))
            elif isinstance(v,list):todo.extend((ptr+'/'+str(i),x) for i,x in enumerate(v) if isinstance(x,(dict,list,str)))
        rawcache[bh]=hits
    for hit in rawcache[bh]:occ.append({'path':path,'json_sha256':bh,**hit})
def archive(raw,path):
    h=sha(raw)
    if h in zipseen:return
    zipseen.add(h)
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        for name in sorted(z.namelist()):
            if name.lower().endswith('.json'):analyze(z.read(name),path+'!'+name)
            elif name.lower().endswith('.zip'):archive(z.read(name),path+'!'+name)
binding=json.loads((HERE/'source_json_blob_binding.json').read_text())
for entry in binding['files']:
    rel=entry['path'];p=ROOT/rel
    if not p.exists() and args.overlay is not None:p=args.overlay/rel
    raw=p.read_bytes()
    if sha(raw)!=entry['sha256']:raise ValueError('Pinned JSON byte mismatch: '+rel)
    analyze(raw,rel)
archives=json.loads((HERE/'source_blob_binding.json').read_text())
for entry in archives['files']:
    rel=entry['path']
    if not rel.lower().endswith('.zip'):continue
    raw=(ROOT/rel).read_bytes()
    if sha(raw)!=entry['sha256']:raise ValueError('Pinned ZIP byte mismatch: '+rel)
    archive(raw,rel)
new={r['table'] for r in normcache.values() if r['new_to_tm_census']}
known_bytes={r['sha256'] for r in existing};nonspanning=[]
for h,r in normcache.items():
    if r['reachable']>=r['states']:continue
    raw=(OUT/(h+'.tm')).read_bytes();rows,states,_,_=mc.parse(raw)
    largest=max(mc.rooted(rows,states,q)[1] for q in states)
    if largest<len(states):
        nonspanning.append({'normalized_sha256':h,'states':len(states),'max_reachable':largest,
                            'identical_to_tm_payload':h in known_bytes})
# The pinned supplement has precisely the two already supplied diagnostics.
# Do not silently equate a future disconnected table by its partial-root key.
assert all(r['identical_to_tm_payload'] for r in nonspanning),nonspanning
s={'commit':pinned,'json_payload_occurrences_with_distinct_zip_payloads':json_payload_occurrences,
   'verified_direct_json_blobs':len(binding['files']),
   'complete_current_PA_and_incoming_JSON_scope':True,
   'distinct_json_payloads':len(rawcache),'distinct_zip_payloads':len(zipseen),
   'recognized_193_194_occurrences':len(occ),'normalized_193_194_tables':len(normcache),
   'recognized_graph_keys':len({r['table'] for r in normcache.values()}),
   'new_graph_keys_beyond_tm_census':sorted(new),'json_parse_errors':errors,
   'nonspanning_normalized_tables':len(nonspanning),
   'all_nonspanning_tables_identical_to_tm_payloads':True,
   'new_whole_graph_classes_beyond_tm_census':sorted(new),
   'recognizer_scope':__doc__}
(OUT/'summary.json').write_text(json.dumps(s,indent=2)+'\n')
(OUT/'identities.json').write_text(json.dumps(normcache,indent=2)+'\n')
(OUT/'occurrences.json').write_text(json.dumps(occ,indent=2)+'\n')
(OUT/'payloads.json').write_text(json.dumps(payloads,indent=2)+'\n')
(OUT/'nonspanning_audit.json').write_text(json.dumps(nonspanning,indent=2)+'\n')
print(json.dumps(s,indent=2),flush=True)
