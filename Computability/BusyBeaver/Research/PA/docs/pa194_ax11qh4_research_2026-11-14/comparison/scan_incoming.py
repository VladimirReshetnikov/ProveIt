#!/usr/bin/env python3
"""Read-only recursive table census of explicitly supplied ZIPs.

Accepts numeric five-column binary L/R tables and the explicit JSON encodings
recognized by the attributed ProveIt scanners in vendor/. Does not execute
generators or infer tables from prose. Start assumptions are recorded separately
from graph identity. Recognition is not a consistency-calibration theorem.
"""
import argparse, collections, hashlib, io, json, pathlib, re, sys, zipfile
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'vendor'))
import literal_inventory as lit
import json_inventory as ji
import machine_classes as mc
if not __debug__:
    raise RuntimeError('Run the scanner with assertions enabled, without -O.')

def digest(b): return hashlib.sha256(b).hexdigest()

def scan(paths, out):
    occurrences=[]; tables={}; archives=[]; seen=set(); errors=[]; files=0
    def add(data, raw, path, pointer=None):
        rows, states, halt=data
        if pointer and len(states)<2: return
        text=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items())).encode()
        h=digest(text);tables.setdefault(h,text)
        m=None if pointer else re.search(rb'(?m)^\s*#.*?\bstart\s*(\d+)',raw)
        start=int(m.group(1)) if m else None
        basis='explicit comment' if m else 'unknown'
        if start is None and pointer is None and '.native.' not in pathlib.Path(path).name and states==set(range(len(states))):
            start=0; basis='dense-zero convention; not independently specified'
        occurrences.append({'path':path,'json_pointer':pointer,'states':len(states),'halt':halt,
            'raw_sha256':digest(raw),'normalized_sha256':h,'designated_start':start,'start_basis':basis})
    def inspect(raw,path,ext):
        nonlocal files
        files+=1
        if ext!='.json':
            data=lit.parse_table(raw)
            if data:add(data,raw,path)
            return
        if not any(k in raw for k in [b'"L"',b'"R"',b' L ',b' R ',b'"table"',b'"transitions"']) and not re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',raw):return
        try:j=json.loads(raw)
        except (ValueError,UnicodeError) as e:errors.append({'path':path,'error':str(e)});return
        todo=[('$',j)]
        while todo:
            ptr,node=todo.pop();data=ji.decode(node)
            if data:add(data,raw,path,ptr);continue
            if isinstance(node,dict):todo.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
            elif isinstance(node,list):todo.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
    def archive(raw,path,depth=0):
        h=digest(raw); archives.append({'path':path,'sha256':h,'depth':depth,'bytes':len(raw)})
        if h in seen:return
        seen.add(h)
        try:
            with zipfile.ZipFile(io.BytesIO(raw)) as z:
                for m in z.infolist():
                    if m.is_dir():continue
                    ext=pathlib.Path(m.filename).suffix.lower();p=path+'!'+m.filename
                    if ext=='.zip':archive(z.read(m),p,depth+1)
                    elif ext in ('.tm','.txt','.tsv','.csv','.json'):inspect(z.read(m),p,ext)
        except (ValueError,OSError,zipfile.BadZipFile) as e:errors.append({'path':path,'error':str(e)})
    for p in sorted(paths):
        archive(p.read_bytes(),'docs/incoming/'+p.name)
    print('Recognized occurrences',len(occurrences),'normalized tables',len(tables),flush=True)
    identities={};byclass=collections.defaultdict(list)
    for i,(h,b) in enumerate(tables.items()):
        rows,states,halt=lit.parse_table(b)
        if len(states)!=194:continue
        cl=mc.classify(b);cl.pop('roots')
        forms=[c for q in sorted(states) if (c:=lit.canonical((rows,states,halt),q)) is not None]
        graph=digest(repr(min(forms)).encode()) if forms else None
        identities[h]={'states':194,'table_class':cl['table'],'graph_hash':graph,'halt':halt,'max_reachable':cl['reachable']}
        byclass[cl['table']].append(h)
    reps=out/'incoming_194_representatives';reps.mkdir(parents=True,exist_ok=True)
    classes=[]
    for c,hs in sorted(byclass.items()):
        occ=[r for r in occurrences if r['normalized_sha256'] in hs]
        best=min(occ,key=lambda r:(sum(s in r['path'].lower() for s in ['comparison/','reference/','research/','search/','census/','inputs/']),r['json_pointer'] is not None,len(r['path'])))
        info={'table_class':c,'graph_hash':identities[hs[0]]['graph_hash'],'normalized_identities':hs,'representative':best,'occurrences':occ}
        classes.append(info);(reps/(c+'.tm')).write_bytes(tables[best['normalized_sha256']])
    summary={'archives_supplied':len(paths),'distinct_archive_payloads':len(seen),'archive_references':len(archives),'payloads_inspected':files,'table_occurrences':len(occurrences),'normalized_tables_all_sizes':len(tables),'normalized_tables_194':len(identities),'classes_194':len(classes),'spanning_classes_194':sum(c['graph_hash'] is not None for c in classes),'errors':errors}
    result={'scope':__doc__,'summary':summary,'archives':archives,'identities_194':identities,'classes_194':classes,'occurrences':occurrences}
    out.mkdir(parents=True,exist_ok=True);(out/'incoming_scan.json').write_text(json.dumps(result,indent=2)+'\n');(out/'incoming_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('archives',nargs='+',type=pathlib.Path);ap.add_argument('--out',type=pathlib.Path,required=True);a=ap.parse_args();scan(a.archives,a.out)
