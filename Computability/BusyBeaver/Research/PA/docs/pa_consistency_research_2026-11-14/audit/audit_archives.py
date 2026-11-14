#!/usr/bin/env python3
"""Inventory PA archive members and literal numeric binary TM tables.

Read-only with respect to the source repository. Table identity is tested up
to state renaming, with the input symbols, write symbols, and directions fixed.
Root-free comparison deliberately does not establish equality of start states.
"""
from __future__ import annotations
import argparse, hashlib, io, json, re, zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEXT = {'.md', '.txt', '.tex', '.json', '.py', '.lean', '.tm', '.tsv', '.csv'}
ROW = re.compile(r'^\s*(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*$')

def sha(b): return hashlib.sha256(b).hexdigest()

def parse_tm(data):
    try: text = data.decode('utf-8')
    except UnicodeDecodeError: return None
    rows={}
    for line in text.splitlines():
        m=ROW.match(line)
        if m:
            q,r,w,d,t=m.groups(); k=(int(q),int(r)); v=(int(w),d,int(t))
            if k in rows and rows[k]!=v: return None
            rows[k]=v
        elif line.strip() and not line.lstrip().startswith(('#','//',';')):
            return None
    states={q for q,b in rows}
    if len(states)<2 or set(rows)!={(q,b) for q in states for b in (0,1)}: return None
    missing={v[2] for v in rows.values()}-states
    if len(missing)>1: return None
    declared=re.search(r'(?:#!\s*)?start\s*[:=]?\s*(\d+)',text,re.I)
    return rows,states,missing,int(declared.group(1)) if declared else None

def canonical(rows,states):
    """Exact root-free isomorphism key when some state reaches all working states."""
    keys=[]
    for start in sorted(states):
        order=[start]; labels={start:0}; result=[]
        for q in order:
            row=[]
            for bit in (0,1):
                w,d,t=rows[q,bit]
                if t not in states: lab=-1
                else:
                    if t not in labels: labels[t]=len(order); order.append(t)
                    lab=labels[t]
                row.append((w,d,lab))
            result.append(tuple(row))
        if len(order)==len(states): keys.append(tuple(result))
    if not keys: return None,0
    return sha(repr(min(keys)).encode()),len(keys)

def main():
    global REPO,OUT
    parser=argparse.ArgumentParser()
    parser.add_argument('--repo',type=Path,required=True,help='ProveIt checkout at the source commit')
    parser.add_argument('--output',type=Path,default=HERE/'census_output')
    args=parser.parse_args();REPO=args.repo;OUT=args.output
    OUT.mkdir(exist_ok=True)
    cache={}; members=[]; archives=[]; tables=[]
    excerpts=[]
    def inspect(archive,name,data,depth=0):
        p=Path(name); digest=sha(data)
        members.append({'archive':archive,'path':name,'size':len(data),'sha256':digest})
        if p.suffix.lower()=='.zip' and depth<3:
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for info in z.infolist():
                        if not info.is_dir() and info.file_size<200_000_000:
                            inspect(archive,name+'!/'+info.filename,z.read(info),depth+1)
            except zipfile.BadZipFile: pass
        if p.suffix.lower() not in TEXT or len(data)>2_000_000: return
        if digest not in cache:
            parsed=parse_tm(data)
            if parsed:
                rows,states,missing,start=parsed; key,nroots=canonical(rows,states)
                cache[digest]={'working_states':len(states),'rows':len(rows),'halt_labels':sorted(missing),
                  'declared_start':start,'root_free_isomorphism_sha256':key,'roots_reaching_all_states':nroots}
            else: cache[digest]=None
        if cache[digest]: tables.append({'archive':archive,'path':name,'sha256':digest,**cache[digest]})
        if p.suffix.lower() in {'.tex','.md','.txt'} and ('report' in name.lower() or 'readme' in name.lower()):
            try: txt=data.decode('utf-8')
            except UnicodeDecodeError: return
            if re.search(r'196|208|209',txt):
                # Retain a compact collection of title/abstract/conclusion paragraphs.
                paras=re.split(r'\n\s*\n',txt)
                selected=[s for s in paras if re.search(r'196|195|194|193|breakthrough|no (?:smaller|new)|not (?:obtained|construct|establish)|isomorph|distinct|equivalen|conditional',s,re.I)]
                if selected: excerpts.append({'archive':archive,'path':name,'sha256':digest,'paragraphs':selected[:60]})
    for path in sorted((REPO/'docs/incoming').glob('*.zip')):
        data=path.read_bytes()
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            infos=[i for i in z.infolist() if not i.is_dir()]
            archives.append({'archive':path.name,'sha256':sha(data),'zip_bytes':len(data),'outer_members':len(infos),
             'uncompressed_bytes':sum(i.file_size for i in infos)})
            for info in infos: inspect(path.name,info.filename,z.read(info))
    for path in sorted((REPO/'Computability/BusyBeaver/Research/PA').rglob('*')):
        if path.is_file() and path.suffix.lower() in TEXT:
            inspect('PA-directory',str(path.relative_to(REPO)),path.read_bytes())
    payload={'source_commit':'1fe9b29810bfe3d0e507146d65f6b97692e7444a','archives':archives,'tables':tables,
     'members':members,'table_identity_caveat':'Root-free canonicalization ignores start-state choice. A matching key proves table graph isomorphism, not start-preserving equivalence; explicit starts must be checked separately.'}
    (OUT/'inventory.json').write_text(json.dumps(payload,indent=2)+'\n')
    (OUT/'excerpts.json').write_text(json.dumps(excerpts,indent=2)+'\n')
    groups={}
    for t in tables: groups.setdefault((t['working_states'],t['root_free_isomorphism_sha256']),[]).append(t)
    (OUT/'table_groups.json').write_text(json.dumps([{'working_states':k[0],'canonical_sha256':k[1],
     'occurrences':len(v),'distinct_byte_forms':len({x['sha256'] for x in v}),'members':v} for k,v in sorted(groups.items(),key=lambda x:(x[0][0],str(x[0][1])))],indent=2)+'\n')
    print(json.dumps({'archives':len(archives),'members_including_nested':len(members),'table_occurrences':len(tables),
     'distinct_table_byte_forms':len({x['sha256'] for x in tables}),'isomorphism_groups':len(groups),
     'groups':[(k[0],len(v),v[0]['archive'],v[0]['path']) for k,v in sorted(groups.items(),key=lambda x:(x[0][0],str(x[0][1])))]},indent=2))

if __name__=='__main__': main()
