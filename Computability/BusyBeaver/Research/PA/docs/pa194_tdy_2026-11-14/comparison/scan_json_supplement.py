#!/usr/bin/env python3
"""Extract complete literal tables from supplied JSON sources and recursive ZIPs."""
import argparse,hashlib,io,json,pathlib,re,sys,zipfile
from json_recognizer import decode

def main():
    ap=argparse.ArgumentParser();ap.add_argument('paths',nargs='+',type=pathlib.Path);ap.add_argument('--output',type=pathlib.Path,required=True);a=ap.parse_args()
    tables={};archives=set();files=0;errors=[];source_files=[]
    def scan_json(data,path):
        nonlocal files
        files+=1
        if not any(x in data for x in (b'"L"',b'"R"',b' L ',b' R ',b'"table"',b'"transitions"')) and not re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',data):return
        try:obj=json.loads(data)
        except Exception as e:errors.append([path,str(e)]);return
        stack=[('$',obj)]
        while stack:
            ptr,node=stack.pop();m=decode(node)
            if m:
                rows,st,halt=m
                if len(st)<2:continue
                text=''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items()))
                sha=hashlib.sha256(text.encode()).hexdigest()
                rec=tables.setdefault(sha,{'sha256':sha,'text':text,'paths':[],'states':len(st)})
                rec['paths'].append(path+'::JSON'+ptr+'.tm');continue
            if isinstance(node,dict):stack.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
            elif isinstance(node,list):stack.extend((ptr+'/'+str(k),v) for k,v in enumerate(node) if isinstance(v,(dict,list,str)))
    def scan(data,path):
        if path.endswith('.json'):scan_json(data,path)
        if not path.endswith('.zip'):return
        h=hashlib.sha256(data).hexdigest()
        if h in archives:return
        archives.add(h)
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for n in z.namelist():
                    if n.endswith(('.json','.zip')):scan(z.read(n),path+'!'+n)
        except Exception as e:errors.append([path,str(e)])
    for root in a.paths:
        for f in sorted(root.rglob('*')):
            if f.is_file() and f.suffix in ('.json','.zip'):
                path=str(f.relative_to(root))
                if root.name=='pa194_incoming':path='docs/incoming/'+path
                source_files.append({'path':path,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()});scan(f.read_bytes(),path)
    a.output.write_text(json.dumps(list(tables.values()),separators=(',',':'))+'\n')
    receipt={'json_files_examined':files,'table_byte_forms':len(tables),'recognized_occurrences':sum(len(r['paths']) for r in tables.values()),'errors':errors,'source_files':source_files}
    a.output.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='source_files'},indent=2))
if __name__=='__main__':main()
