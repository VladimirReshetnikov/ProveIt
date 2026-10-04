"""Independent read-only reauthentication; no predecessor code import/execution."""
import collections
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
DEST = Path('/tmp/reauth_two_publication_reviews.json')
INPUTS = [
 ('polish_borel_9a8894d0a', '8369c3fe61d9dcbaff643beb32b76abacfdf0bba17548a5bc66e600bd91e2e16', '2643f8ae2df4c0e2f00b175f69f73d0cdeb645b3d1feb600b95d7b61fac03900'),
 ('definable_publication_c7d65e30b', '47e29c2276d241a8dd7cc14b5ee2a0e53e0ac6e8f3881cadd3db3108143ab7a7', '5c636dbaf2bf11dd17dd14b6147de4a9c2529affab2d360257108cca0f51e8e1')]
EVENTS = []
CACHE = {}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def run_git(*parts):
    return subprocess.check_output(['git',*parts],cwd=REPO)

def require(ok, tag, **details):
    if not ok:
        raise RuntimeError(json.dumps(dict(failed=tag,**details)))
    EVENTS.append(dict(check=tag,**details))

def read_git(commit,path):
    key=(commit,path)
    if key not in CACHE:
        CACHE[key]=run_git('show',commit+':'+path)
    return CACHE[key]

def verify_bytes(record,data,tag):
    require(digest(data)==record['sha256'],tag+'.sha256',sha256=record['sha256'])
    if 'bytes' in record: require(len(data)==record['bytes'],tag+'.bytes',bytes=len(data))
    if 'lines' in record: require(len(data.splitlines())==record['lines'],tag+'.lines',lines=len(data.splitlines()))

def pin(record,tag):
    c,p=record['commit'],record['path']; data=read_git(c,p)
    verify_bytes(record,data,tag)
    require(run_git('rev-parse',c+':'+p).decode().strip()==record['blob'],tag+'.blob',commit=c,path=p,blob=record['blob'])
    return data

def check_span(record,data,tag):
    lo=record.get('first',record.get('start')); hi=record.get('last',record.get('end'))
    lines=data.splitlines(keepends=True)
    require(1<=lo<=hi<=len(lines),tag+'.range',first=lo,last=hi)
    verify_bytes(record,b''.join(lines[lo-1:hi]),tag)
    if 'lines' in record: require(record['lines']==hi-lo+1,tag+'.span_length')

def uncomment(data):
    text=data.decode()
    # TeX percent starts a comment iff preceded by an even number of slashes.
    cleaned=[]
    for line in text.splitlines(keepends=True):
        for pos,ch in enumerate(line):
            if ch=='%':
                n=0;j=pos-1
                while j>=0 and line[j]=='\\': n+=1;j-=1
                if n%2==0:
                    line=line[:pos]+ ('\n' if line.endswith('\n') else '')
                    break
        cleaned.append(line)
    return ''.join(cleaned)

LABEL = re.compile(r'\\label(?:\[[^\]]*\])?\{([^{}]+)\}')
def tex_labels(data): return LABEL.findall(uncomment(data))
def refs_in(data):
    text=uncomment(data); found=[]
    for m in re.finditer(r'\\([A-Za-z]+)\*?(?:\[[^\]]*\])?\{([^{}]*)\}',text):
        if m[1] in {'ref','cref','Cref','eqref','pageref','cpageref','Cpageref','autoref','crefrange','Crefrange'}:
            found += [k.strip() for k in m[2].split(',')]
    return found

def statement_positions(data):
    numbered={'theorem','lemma','proposition','corollary','definition','example','question','remark'}
    section=counter=0; stack=[]; out={}
    pattern=re.compile(r'\\section(\*)?\{|\\setcounter\{section\}\{(\d+)\}|\\(begin|end)\{([^{}]+)\}|\\label(?:\[[^\]]*\])?\{([^{}]+)\}')
    for m in pattern.finditer(uncomment(data)):
        if m[0].startswith('\\section'):
            if not m[1]: section+=1;counter=0
        elif m[2] is not None: section=int(m[2]);counter=0
        elif m[3]=='begin':
            if m[4] in numbered: counter+=1;stack.append((m[4],section,counter))
        elif m[3]=='end':
            if m[4] in numbered:
                if not stack or stack[-1][0]!=m[4]: raise RuntimeError('numbered environment nesting')
                stack.pop()
        elif m[5] is not None and stack: out[m[5]]=list(stack[-1])
    return out

def audit(stem,json_hash,md_hash):
    jpath=Path('/tmp/review_'+stem+'.json'); mpath=jpath.with_suffix('.md')
    raw=jpath.read_bytes(); md=mpath.read_bytes()
    require(digest(raw)==json_hash,stem+'.receipt_pin')
    require(digest(md)==md_hash,stem+'.review_pin')
    r=json.loads(raw); c=r['commit']; p=r['parent']; count=collections.Counter()
    require(run_git('rev-parse',c+'^').decode().strip()==p,stem+'.parent')
    files=r['files']; expected={x['path'] for x in files}
    require(set(run_git('diff','--name-only',p,c).decode().splitlines())==expected,stem+'.changed_paths')
    for f in files:
        for side in ('before','after'):
            q=f[side]; data=pin(q,stem+'.'+f['path']+'.'+side);count['git_file_records']+=1
            require(q['commit']==(p if side=='before' else c) and q['path']==f['path'],stem+'.version_binding')
            for k,s in enumerate(q.get('read_spans',[])):
                check_span(s,data,stem+f'.{side}.span{k}');count['hashed_spans']+=1
        if 'diff' in f:
            d=f['diff']; args=['diff','--no-ext-diff','--no-color','--unified=3',p,c,'--',f['path']]
            b=run_git(*args);verify_bytes(d,b,stem+'.diff');count['diffs']+=1
            for s in d.get('read_spans',[])+d.get('human_read_spans',[]):
                check_span(s,b,stem+'.diff_span');count['hashed_spans']+=1
            if 'added_lines' in d:
                require(sum(x.startswith(b'+') and not x.startswith(b'+++') for x in b.splitlines())==d['added_lines'],stem+'.added_lines')
                require(sum(x.startswith(b'-') and not x.startswith(b'---') for x in b.splitlines())==d['removed_lines'],stem+'.removed_lines')
    for q in r.get('instructions',[])+r.get('ancestry',[]):
        b=pin(q,stem+'.context');count['git_file_records']+=1
        for s in q.get('read_spans',[]):check_span(s,b,stem+'.context_span');count['hashed_spans']+=1
    for q in r.get('human_article_reads',[])+r.get('instructions_reads',[])+([r['prior_review_read']] if 'prior_review_read' in r else []):
        check_span(q,read_git(q['commit'],q['path']),stem+'.declared_read');count['hashed_spans']+=1
    if 'prior_review' in r:pin(r['prior_review'],stem+'.prior');count['git_file_records']+=1
    collector=r.get('collector',dict(path='/tmp/review_polish_borel_9a8894d0a_metadata.py',sha256=r.get('source_helper_sha256')))
    require(digest(Path(collector['path']).read_bytes())==collector['sha256'],stem+'.collector_bytes_only')

    members={}; source_tex={}
    for ar in r['archives']:
        rawzip=pin(ar,stem+'.archive');count['archives']+=1;count['git_file_records']+=1
        with zipfile.ZipFile(io.BytesIO(rawzip)) as z:
            require([i.filename for i in z.infolist() if not i.is_dir()]==[m['path'] for m in ar['members']],stem+'.complete_zip_inventory')
            for m in ar['members']:
                b=z.read(m['path']);members[ar['path'],m['path']]=b
                verify_bytes(m,b,stem+'.member');count['zip_members']+=1
                if 'crc32' in m:require(z.getinfo(m['path']).CRC==m['crc32'],stem+'.crc')
                for s in m.get('read_spans',[]):check_span(s,b,stem+'.member_span');count['hashed_spans']+=1
                if 'source_label_map' in m:
                    require([x['original'] for x in m['source_label_map']]==tex_labels(b),stem+'.complete_source_label_inventory')
                if 'source' in ar and m['path']==ar['tex_member']:source_tex[ar['source']]=b
            if ar.get('source')=='05':
                checks=z.read('definable_surreals_real_parameters/SHA256SUMS').decode().splitlines()
                parsed=[]
                for line in checks:
                    if not line.strip():continue
                    h,name=line.split(maxsplit=1);name=name.lstrip('* ')
                    require(digest(z.read('definable_surreals_real_parameters/'+name))==h,stem+'.delivered_checksum')
                    parsed.append(dict(path=name,sha256=h))
                require(parsed==r['delivered_checksum_checks'],stem+'.delivered_checksum_records');count['delivered_checksums']=len(parsed)
    for q in r.get('placements',[]):
        b=pin(q,stem+'.placement');count['git_file_records']+=1
        require(b==members[q['archive'],q['member']]==read_git(p,q['path']),stem+'.placement_equal');count['placements']+=1
    for q in r.get('ancillary_placement_matches',[]):
        a,b=pin(q['placement'],stem+'.original_placement'),pin(q['publication'],stem+'.published_placement');count['git_file_records']+=2
        ar=next(x for x in r['archives'] if x['source']==q['source'])
        require(a==b==members[ar['path'],q['member']],stem+'.placement_equal')
        require(digest(a)==q['member_sha256'],stem+'.placement_member_hash');count['placements']+=1

    article=next(f for f in files if f['path'].endswith('/article.tex'))
    old=read_git(p,article['path']);new=read_git(c,article['path']);ol,nl=tex_labels(old),tex_labels(new);ls=r['labels']
    require(len(ol)==ls['before'] and len(nl)==ls['after'] and len(set(nl))==len(nl),stem+'.label_counts')
    require([x for x in nl if x in set(ol)]==ol,stem+'.old_label_sequence')
    refs=refs_in(new);missing=sorted(set(refs)-set(nl))
    require(not missing,stem+'.references_resolve',occurrences=len(refs),distinct=len(set(refs)))
    expected_ref=ls.get('literal_internal_ref_occurrences',ls.get('all_internal_reference_occurrences_resolved'))
    require(len(refs)==expected_ref,stem+'.reference_count')
    if 'distinct_internal_references' in ls:require(len(set(refs))==ls['distinct_internal_references'],stem+'.distinct_reference_count')
    if 'new' in ls:require(len(set(nl)-set(ol))==ls['new'],stem+'.new_label_count')
    for pref,num in ls.get('new_prefix_counts',{}).items():require(sum(x.startswith(pref) and x not in ol for x in nl)==num,stem+'.new_prefix_count')
    for ar in r['archives']:
        for m in ar['members']:
            for x in m.get('source_label_map',[]):
                require(x['merged'] in nl,stem+'.mapped_source_label');count['source_label_routes']+=1
    lines=new.splitlines(keepends=True)
    for mapping in ls.get('source_mappings',[]):
        src=tex_labels(source_tex[mapping['source']]);entries=mapping['entries']
        require([e['source_label'] for e in entries]==src,stem+'.complete_source_label_inventory')
        direct=0
        for e in entries:
            count['source_label_routes']+=1
            if e['type']=='prefix/suffix label resolution':direct+=1
            for t in e['targets']:
                n=t['line'];line=lines[n-1]
                require(digest(line)==t['line_sha256'],stem+'.label_line_hash',line=n,label=t['label']);count['hashed_label_lines']+=1
                require(t['label'] in LABEL.findall(line.decode()),stem+'.label_line_content')
        require(len(src)==mapping['label_occurrences'] and direct==mapping['direct_label_resolutions'],stem+'.source_route_counts')
    if 'source_counter_checks' in ls:
        orig={s:statement_positions(b) for s,b in source_tex.items()};current=statement_positions(new)
        for q in ls['source_counter_checks']:
            require(orig[q['source']].get(q['label'])==q['original'],stem+'.source_statement_counter',label=q['label'])
            require(current.get(q['target'])==q['published'],stem+'.published_statement_counter',label=q['target']);count['statement_number_pairs']+=1
    return dict(stem=stem,receipt=dict(path=str(jpath),sha256=json_hash),review=dict(path=str(mpath),sha256=md_hash),commit=c,parent=p,
                counts=dict(count),labels_before=len(ol),labels_after=len(nl),internal_reference_occurrences=len(refs),distinct_references=len(set(refs)),status='PASS')

results=[audit(*item) for item in INPUTS]
output=dict(schema='independent-two-publication-reauth-v1',checker_sha256=digest(Path(__file__).read_bytes()),results=results,
            checks=EVENTS,execution=dict(fresh_script_only=True,supplied_or_predecessor_execution=False,build=False,repo_mutation=False),
            limitations=['Authenticates recorded read spans, not whether a human read or proved them.',
                         'No mathematical re-review, source-body equivalence proof, external-paper audit, PDF render or build.',
                         'TeX references and statement counters checked as literal source syntax; no general TeX macro evaluator.',
                         'Editorial label correspondence target lines are authenticated, not proved semantically equivalent.',
                         'Current working files need not equal immutable snapshots and are not part of this audit.'])
DEST.write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(dict(results=results,successful_checks=len(EVENTS),receipt_sha256=digest(DEST.read_bytes())),indent=2))
