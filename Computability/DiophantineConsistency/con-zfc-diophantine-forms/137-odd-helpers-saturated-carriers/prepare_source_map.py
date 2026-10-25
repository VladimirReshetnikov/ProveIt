#!/usr/bin/env python3
"""Copy approved producer TeX sections and retain exact source provenance.

Run only after the paths and sections are approved for inclusion.
A mapping row contains source, destination, and optional literal replacements.
No replacement changes the producer's own files.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json

def need(ok,msg):
    if not ok: raise ValueError(msg)
def safe(s):
    p=PurePosixPath(s)
    need(s and p.as_posix()==s and not p.is_absolute() and '..' not in p.parts and '\\' not in s and ':' not in s,'unsafe relative path '+s)
    return p
def digest(raw):return hashlib.sha256(raw).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--plan',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();root=a.root.resolve();rows=[]
    for row in json.loads(a.plan.read_text())['sections']:
        src=root/str(safe(row['source']));dst=root/str(safe(row['destination']))
        need(src!=dst,'presentation source must remain untouched')
        raw=src.read_bytes();text=raw.decode('utf-8');changes=[]
        for change in row.get('replacements',[]):
            old,new=change['old'],change['new'];count=text.count(old)
            need(count==change['expected_count'],'replacement count mismatch in '+row['source'])
            text=text.replace(old,new);changes.append(dict(change,actual_count=count))
        dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(text,encoding='utf-8')
        rows.append({'source':row['source'],'source_sha256':digest(raw),'destination':row['destination'],'destination_sha256':digest(dst.read_bytes()),'replacements':changes})
    a.output.write_text(json.dumps({'schema':'report_section_source_map_v1','scope':'Presentation copies only; producer sources remain unchanged. Every editorial replacement is explicit.','sections':rows},indent=2)+'\n')
    print(json.dumps({'status':'PASS','sections':len(rows)}))
if __name__=='__main__':main()
