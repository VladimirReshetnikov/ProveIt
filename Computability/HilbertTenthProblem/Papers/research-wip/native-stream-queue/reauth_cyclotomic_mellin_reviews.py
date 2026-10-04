"""Fresh read-only reauthentication; no review collector or archive code runs."""
import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

PINS={
 'review_mellin_stokes_placement_05304d5ec.md':'fd124f5cb3e1aec55e1a939cd79a83d5b1f7bcd9b54dc48b52f62ef07c9ce5dd',
 'review_mellin_stokes_placement_05304d5ec.json':'2ddf01c9f533197ad7f72c3c167d670a841c74915a09bdc1bd0749e553135dea',
 'review_cyclotomic_7389d7de4.md':'a9e1f9a9d7b3c292910fca4f908c12ce6a42c3bdd68e9038c027c4befdcebb1a',
 'review_cyclotomic_7389d7de4.json':'8b6a6348c831234ad8c4ddb87f895bde7c3bbf5c708d615000241b5d982adac0',
}

def ck(ok,message):
    if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def unique(items):
    out={}
    for k,v in items:
        ck(k not in out,'duplicate JSON key');out[k]=v
    return out
def loads(raw):return json.loads(raw,object_pairs_hook=unique)

class Audit:
    def __init__(self,repo):self.repo=repo;self.cache={};self.count=Counter()
    def git(self,*args):
        ck(args[0] in ('show','rev-parse','diff','ls-tree'),'read-only command')
        return subprocess.check_output(['git','-C',str(self.repo),*args])
    def raw(self,commit,path):
        key=(commit,path)
        if key not in self.cache:
            self.cache[key]=self.git('show',commit+':'+path)
        return self.cache[key]
    def metadata(self,data,record):
        if 'bytes' in record:ck(len(data)==record['bytes'],'byte size')
        if 'sha256' in record:ck(sha(data)==record['sha256'],'SHA256')
        if 'lines' in record:ck(len(data.splitlines())==record['lines'],'line count')
        if 'total_lines' in record:ck(len(data.splitlines())==record['total_lines'],'total lines')
    def spans(self,data,spans,normalized=False):
        for s in spans:
            if normalized:
                lines=data.decode('utf-8').splitlines();lo=s['start_line'];hi=s['end_line']
                cut=('\n'.join(lines[lo-1:hi])+'\n').encode()
                ck(sha(cut)==s['normalized_span_sha256'],'normalized span hash')
            else:
                lines=data.splitlines(keepends=True);lo=s['first'];hi=s['last']
                cut=b''.join(lines[lo-1:hi]);self.metadata(cut,s)
            ck(1<=lo<=hi<=len(lines),'span bounds')
            ck(s['lines']==hi-lo+1,'span lines')
            self.count['spans']+=1;self.count['span_lines']+=hi-lo+1
    def blob(self,record,path=None):
        path=record.get('path',path);ck(path is not None,'blob path')
        data=self.raw(record['commit'],path)
        oid=self.git('rev-parse',record['commit']+':'+path).decode().strip()
        ck(oid==record['blob'],'blob identity '+path)
        metadata={k:v for k,v in record.items() if k!='lines' or 'start_line' not in record}
        self.metadata(data,metadata)
        self.spans(data,record.get('read_spans',[]))
        self.count['blob_records']+=1
        return data
    def diff(self,parent,commit,path,record,full=False):
        opts=['--no-ext-diff','--no-renames','--no-color','--no-textconv','--full-index' if full else '--abbrev=9']
        data=self.git('diff',*opts,parent,commit,'--',path)
        self.metadata(data,record);self.spans(data,record.get('read_spans',[]))
        if 'added_lines' in record:
            lines=data.decode().splitlines()
            adds=sum(x.startswith('+') and not x.startswith('+++') for x in lines)
            dels=sum(x.startswith('-') and not x.startswith('---') for x in lines)
            ck((adds,dels)==(record['added_lines'],record['removed_lines']),'diff line totals')
            hs=[]
            for line in lines:
                m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
                if m:hs.append(dict(old_start=int(m[1]),old_count=int(m[2] or 1),new_start=int(m[3]),new_count=int(m[4] or 1)))
            ck(hs==record['hunks'],'diff hunks')
            self.count['added_lines']+=adds;self.count['removed_lines']+=dels
        self.count['diffs']+=1
    def changed(self,parent,commit):
        lines=self.git('diff','--no-ext-diff','--no-renames','--name-status',parent,commit).decode().splitlines()
        return [tuple(x.split('\t')) for x in lines]
    def archive(self,record,full):
        raw=self.blob(record);z=zipfile.ZipFile(io.BytesIO(raw))
        infos={i.filename:i for i in z.infolist() if not i.is_dir()}
        ck(len(infos)==sum(not i.is_dir() for i in z.infolist()),'archive duplicate name')
        if full:ck(list(infos)==[m['path'] for m in record['members']],'complete member census')
        members={}
        for m in record['members']:
            data=z.read(m['path']);self.metadata(data,m)
            if 'crc32' in m:ck(infos[m['path']].CRC==m['crc32'],'member CRC')
            self.spans(data,m.get('reads',[]),normalized=True)
            members[m['path']]=data;self.count['members']+=1
        self.count['archives']+=1
        return raw,members

def mellin(a,d):
    commit,parent=d['commit'],d['parent']
    ck(a.git('rev-parse',commit+'^').decode().strip()==parent,'Mellin parent')
    ck(a.changed(parent,commit)==[(r['status'],r['path']) for r in d['changes']],'Mellin changed census')
    msg=a.git('show','-s','--format=%B',commit);a.metadata(msg,d['commit_message']);a.spans(msg,d['commit_message']['read_spans'])
    for f in d['changes']:
        for side in ('before','after'):
            if side in f:a.blob(f[side])
        a.diff(parent,commit,f['path'],f['diff'])
    for r in d['instructions']+d['prior_intake']:a.blob(r)
    member_tables={};ledger_count=0
    for ar in d['archives']:
        raw,members=a.archive(ar,True);member_tables[ar['path']]=members
        ck(raw==a.blob(ar['retired_parent']) and ar['parent_equals_arrival'] is True,'arrival equality')
        ledger=next(n for n in members if PurePosixPath(n).name.startswith('SHA256SUMS'))
        prefix=str(PurePosixPath(ledger).parent)
        parsed=[]
        for line in members[ledger].decode().splitlines():
            if not line.strip():continue
            h,name=line.split(maxsplit=1);name=name.lstrip('*')
            ck(re.fullmatch('[0-9a-f]{64}',h) is not None,'ledger digest grammar')
            ck(sha(members[prefix+'/'+name])==h,'ledger member')
            parsed.append({'path':name,'sha256':h})
        ck(parsed==ar['checksum_checks'],'checksum ledger entries');ledger_count+=len(parsed)
        for m in ar['members']:
            if 'placement' in m:ck(members[m['path']]==a.raw(commit,m['placement']),'member placement')
    placed_bytes=0
    for p in d['placements']:
        data=a.blob(p);ck(data==member_tables[p['archive']][p['member']] and p['exact_bytes_equal'] is True,'placement record')
        placed_bytes+=len(data)
    old=loads(a.raw(d['prior_intake'][1]['commit'],d['prior_intake'][1]['path']))
    for ar,pr in zip(d['archives'],d['prior_intake_comparison']):
        prior=next(x for x in old['archives'] if x['path']==ar['path'])
        ck(pr['archive']==ar['path'] and pr['all_member_pins_equal'] is True,'prior comparison record')
        ck(prior['sha256']==ar['sha256'],'prior archive')
        fields=lambda xs:{m['path']:(m['bytes'],m['sha256']) for m in xs}
        ck(fields(prior['members'])==fields(ar['members']),'all prior member pins')
    for row in d['source_labels']:
        text=a.raw(commit,row['path']).decode();labs=re.findall(r'\\label\{([^}]+)\}',text)
        refs=re.findall(r'\\(?:ref|eqref|autoref|cref|Cref)\{([^}]+)\}',text)
        ck(len(labs)==len(set(labs))==row['labels'],'Mellin label census')
        ck(len(refs)==row['literal_internal_reference_occurrences'],'Mellin reference census')
        ck(sorted(set(refs)-set(labs))==row['missing'],'Mellin unresolved literal refs')
        a.count['label_censuses']+=1
    statuses=Counter(f['status'] for f in d['changes'])
    tex_lines=sum(s['lines'] for f in d['changes'] if f['path'].endswith('.tex') for s in f.get('after',{}).get('read_spans',[]))
    totals={'changed_files':len(d['changes']),'added_files':statuses['A'],'modified_guides':statuses['M'],
            'retired_archives':statuses['D'],'regular_archive_members':sum(len(x['members']) for x in d['archives']),
            'checksum_entries':ledger_count,'placed_files':len(d['placements']),'placed_bytes':placed_bytes,'selected_tex_lines':tex_lines}
    ck(totals==d['totals'],'Mellin totals')
    return totals

def cyclotomic(a,d):
    commit,parent=d['review_commit'],d['parent']
    ck(a.git('rev-parse',commit+'^').decode().strip()==parent,'cyclotomic parent')
    ck(a.changed(parent,commit)==[('M',f['path']) for f in d['files']],'cyclotomic changed census')
    adds=dels=0
    for f in d['files']:
        before=a.blob(f['before'],f['path']);after=a.blob(f['after'],f['path'])
        if 'diff' in f:
            a.diff(parent,commit,f['path'],f['diff'],True)
            adds+=f['diff']['added_lines'];dels+=f['diff']['removed_lines']
        if 'labels' in f:
            b=re.findall(rb'\\label\{([^}]+)\}',before);n=re.findall(rb'\\label\{([^}]+)\}',after)
            rec={'before_count':len(b),'after_count':len(n),'added':[x.decode() for x in n if x not in set(b)],
                 'removed':[x.decode() for x in b if x not in set(n)],'old_sequence_preserved':[x for x in n if x in set(b)]==b}
            ck(rec==f['labels'],'cyclotomic label census');a.count['label_censuses']+=1
    for r in d['reads']:
        data=a.blob(r);a.spans(data,[r],True)
    for ar in d['archives']:a.archive(ar,False)
    pr=d['provenance'];record=dict(pr['original_arrival'],path=pr['archive_path'])
    ck(a.blob(record)==a.raw(commit,pr['archive_path']) and pr['same_archive_bytes_at_review_commit'] is True,'cyclotomic arrival equality')
    destination=a.git('ls-tree','-r','--name-only',commit,'--',pr['claimed_destination']).decode().splitlines()
    ck(destination==pr['destination_files_at_review_commit'],'destination status')
    chapter=next(f for f in d['files'] if '/chapters/' in f['path'])
    current=a.raw(commit,chapter['path']).decode();previous=a.raw(parent,chapter['path']).decode()
    clause='In every direction whose open Borel ray avoids \\(\\Sigma_{a,\\zeta}\\) and for which the Laplace integral converges, its Borel sum equals the exact \\(R_a(t)\\).'
    normalize=lambda s:' '.join(s.split())
    ck(normalize(clause) in normalize(current) and normalize(clause) in normalize(previous),'historical false-clause retention')
    cross=d['cross_reference_checks'];ck(cross['false_clause_retained'] is True,'retention flag')
    alltext='\n'.join(a.raw(commit,f['path']).decode() for f in d['files'] if f['path'].endswith('.tex'))
    for lab in cross['new_labels']:ck(len(re.findall(r'\\label\{'+re.escape(lab)+r'\}',alltext))==1,'new label unique')
    for key in cross['new_citation_keys']:ck(len(re.findall(r'\\bibitem(?:\[[^]]*\])?\{'+re.escape(key)+r'\}',alltext))==1,'new bibliography key unique')
    totals={'added_text_lines':adds,'deleted_text_lines':dels,'changed_files':len(d['files']),
            'text_files':sum('diff' in f for f in d['files']),'binary_files':sum('diff' not in f for f in d['files'])}
    ck(totals==d['totals'],'cyclotomic totals')
    return totals

def build(repo,review_root):
    for name,h in PINS.items():ck(sha((review_root/name).read_bytes())==h,'review pin '+name)
    m=loads((review_root/'review_mellin_stokes_placement_05304d5ec.json').read_bytes())
    c=loads((review_root/'review_cyclotomic_7389d7de4.json').read_bytes())
    collectors={
      'review_mellin_stokes_placement_05304d5ec_metadata.py':m['helper_sha256'],
      'review_cyclotomic_7389d7de4.py':c['collector_sha256'],
    }
    for name,h in collectors.items():ck(sha((review_root/name).read_bytes())==h,'inert collector bytes '+name)
    a=Audit(repo);m_counts=mellin(a,m);c_counts=cyclotomic(a,c)
    return {'source_sha256':sha(Path(__file__).read_bytes()),'review_pins':PINS,
            'mellin':m_counts,'cyclotomic':c_counts,'collector_byte_hashes':collectors,'checks':dict(sorted(a.count.items())),
            'distinct_commit_path_blobs':len(a.cache),
            'scope':{'metadata_only':True,'mathematical_rereview':False,'collectors_executed_or_imported':False,
                     'archive_programs_executed':False,'PDF_build_or_visual_check':False,
                     'cyclotomic_archive_scope':'three listed members only; archive bytes fully hashed',
                     'mellin_archive_scope':'all18 regular members, both ledgers and all16 placements'}}

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--review-root',type=Path,required=True)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    x=p.parse_args();result=json.dumps(build(x.repo,x.review_root),sort_keys=True,indent=2)+'\n'
    if x.output:
        with x.output.open('x') as f:f.write(result)
    else:ck(x.expect.read_text()==result,'exact receipt')
    print('PASS: independent immutable metadata reauthentication')

if __name__=='__main__':main()
