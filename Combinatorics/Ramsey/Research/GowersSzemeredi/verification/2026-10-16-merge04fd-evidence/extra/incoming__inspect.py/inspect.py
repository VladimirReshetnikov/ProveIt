import collections, hashlib, json, pathlib, re, subprocess, sys

OUT=pathlib.Path(__file__).parent
GIT='/tmp/gowers-origin04fd-source-review.git'
BASE='68ad8d3'
TIP='04fd0fb36e46ff05373664236758eff99665bded'
def git(*args):return subprocess.check_output(['git','--git-dir='+GIT,*args])
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,data):
    (OUT/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
ns={};exec(pathlib.Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py').read_text(),ns)
ns['COMMAND']=re.compile(ns['COMMAND'].pattern.replace('|export|run_cmd','|export|alias|run_cmd'),re.M)
parse=ns['parse_declarations'];mask=ns['mask_comments']
paths=git('diff','--name-only',BASE+'..'+TIP).decode().splitlines()
lean=[p for p in paths if p.endswith('.lean')]
source={};before={};after={};errors=[];removed=[];retained=[];added=[]
for p in lean:
    b=git('show',BASE+':'+p);a=git('show',TIP+':'+p)
    before[p]=b.decode();after[p]=a.decode()
    source[p]={'baseline_sha256':sha(b),'incoming_sha256':sha(a),'before_lines':len(b.splitlines()),'after_lines':len(a.splitlines())}
    try: bd=parse(b.decode());ad=parse(a.decode())
    except Exception as e:errors.append([p,str(e)]);continue
    for n,d in bd.items():
        if n not in ad:
            removed.append({'file':p,'name':n,**d,'private':'private ' in d['header']})
        else:
            e=ad[n];retained.append({'file':p,'name':n,'kind':d['kind'],'header_exact':d['header']==e['header'],'context_exact':d['context']==e['context'],'block_exact':d['block']==e['block'],'line_before':d['line'],'line_after':e['line'],'before_header':d['header'],'after_header':e['header'],'before_block_sha256':sha(d['block'].encode()),'after_block_sha256':sha(e['block'].encode())})
    added.extend({'file':p,'name':n,**d} for n,d in ad.items() if n not in bd)
    source[p]['imports_exact']=ns['imports'](b.decode())==ns['imports'](a.decode())
    def cmds(s):
        m=mask(s);cs=list(ns['COMMAND'].finditer(m));return [m[x.start():(cs[i+1].start() if i+1<len(cs) else len(m))].strip() for i,x in enumerate(cs) if x['kind'] not in ns['DECL_KINDS']]
    source[p]['nondeclaration_commands_exact']=cmds(b.decode())==cmds(a.decode())
    (OUT/'diffs').mkdir(exist_ok=True)
    (OUT/'diffs'/pathlib.Path(p).with_suffix('.diff').name).write_bytes(git('diff',BASE+'..'+TIP,'--',p))
write('source-rows.json',source);write('removed-declarations.json',removed);write('retained-declarations.json',retained);write('added-declarations.json',added)
bycommit={}
for old,new in [(BASE,'cc482c540'),('9d5ca068b','e81621153'),('e81621153',TIP)]:
    pp=[p for p in git('diff','--name-only',old+'..'+new).decode().splitlines() if p.endswith('.lean')]
    rr=[]
    for p in pp:
        b=parse(git('show',old+':'+p).decode());a=parse(git('show',new+':'+p).decode())
        rr.extend({'file':p,'name':n,'kind':d['kind'],'private':'private ' in d['header']} for n,d in b.items() if n not in a)
    bycommit[new]={'owners':len(pp),'removed':rr,'source_line_delta':sum(len(git('show',new+':'+p).splitlines())-len(git('show',old+':'+p).splitlines()) for p in pp)}
write('commit-removals.json',bycommit)
summary={'changed_files':len(paths),'lean_files':len(lean),'errors':errors,'retained':len(retained),'removed':len(removed),'removed_kinds':dict(collections.Counter(d['kind'] for d in removed)),'removed_private':sum(d['private'] for d in removed),'retained_changed_headers':[d for d in retained if not d['header_exact'] or not d['context_exact']],'retained_changed_blocks':sum(not d['block_exact'] for d in retained),'added':len(added),'import_changes':[p for p,d in source.items() if not d['imports_exact']],'ambient_command_changes':[p for p,d in source.items() if not d['nondeclaration_commands_exact']],'source_delta':sum(d['after_lines']-d['before_lines'] for d in source.values()),'commit_counts':{k:{'owners':v['owners'],'removed':len(v['removed']),'private':sum(d['private'] for d in v['removed']),'source_line_delta':v['source_line_delta']} for k,v in bycommit.items()}}
write('summary.provisional.json',summary);print(json.dumps(summary,ensure_ascii=False,indent=2))
