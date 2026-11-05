"""Validate a terminal 61-module extension against an authenticated context."""
import os
import re
from pathlib import Path

def verify_terminal(state,exit_code,ctx,extension_root,helpers,expected_hashes):
    """No Lean calls or writes. The caller must authenticate ctx before/after."""
    need=helpers['need'];digest=helpers['digest'];guard=helpers['check_guard']
    suffixes=helpers['suffixes'];root=Path(extension_root);overlay=root/'lib'
    need(exit_code==0 and state.get('status')=='PASS' and state.get('phase')=='complete',
         ('extension did not exit successfully',exit_code,state.get('status')))
    for key,value in expected_hashes.items():need(state.get(key)==value,('terminal pin mismatch',key))
    order=ctx['order'];rows=ctx['rows'];records=state.get('records',[]);outputs=state.get('outputs',{})
    need(len(order)==61 and len(records)==61 and set(outputs)==set(order) and
         [r.get('module') for r in records]==order and all(r.get('exit')==0 for r in records),
         'incomplete or failed extension rows')
    expected_base={}
    for name,g in ctx['base']['outputs'].items():
        for path,entry in g.items():
            orig=Path(path);need(orig.is_relative_to(ctx['base_lib']),('base output escaped',path))
            expected_base[str(overlay/orig.relative_to(ctx['base_lib']))]=entry
    need(state.get('base_overlay_guards')==expected_base,'extension base overlay differs from authenticated base')
    need(state.get('external_guards')==ctx['external_guard'],'extension external guard differs from current preflight')
    shadow=state.get('overlay_external_guards',{})
    expected_shadow={str(overlay/(n.replace('.','/')+s)) for n in ctx['external'] for s in suffixes}
    need(set(shadow)==expected_shadow and all(v is None for v in shadow.values()),'external overlay shadow guards differ')
    expected_present={path for g in [expected_base,*outputs.values()] for path,entry in g.items() if entry is not None}
    def check_inventory():
        for top in {n.split('.')[0] for n in ctx['external']}:
            for suffix in ('',*suffixes,'.so','.dll','.dylib'):
                need(not os.path.lexists(overlay/(top+suffix)),('external namespace shadow',top+suffix))
        actual=set()
        for path in overlay.rglob('*'):
            need(not (path.is_symlink() and path.is_dir()),('symlinked overlay directory',str(path)))
            if path.is_file() or path.is_symlink():actual.add(str(path))
        need(actual==expected_present,'unexpected or missing extension overlay file')
    check_inventory()
    guard(expected_base);guard(state['external_guards']);guard(shadow)
    project=set(ctx['manifest']['sources'])|set(rows)
    for i,rec in enumerate(records):
        name=order[i];row=rows[name];staged=root/'src'/(name.replace('.','/')+'.lean')
        workspace=ctx['workspace_root']/row['workspace_path']
        need(staged.is_file() and not staged.is_symlink() and workspace.is_file() and
             digest(staged)==digest(workspace)==row['sha256']==rec['source_sha256'],('source mismatch',name))
        obj=overlay/(name.replace('.','/')+'.olean');og=outputs[name]
        need(set(og)=={str(obj)[:-6]+s for s in suffixes} and obj.is_file() and not obj.is_symlink() and
             digest(obj)==rec['object_sha256'] and isinstance(og[str(obj)],dict) and
             og[str(obj)]['sha256']==rec['object_sha256'] and og[str(obj)]['realpath']==str(obj.absolute()),
             ('output mismatch',name))
        guard(og)
        log=root/'logs'/(f'{i:03d}-'+name.replace('.','_')+'.log')
        need(rec['log']==str(log) and log.is_file() and digest(log)==rec['log_sha256'],('log mismatch',name))
        need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',log.read_text()),
             ('error or sorry in log',name))
        direct=rec['direct_inputs'];declared=set(row['imports']);actual=set(direct)
        need(declared<=actual and not actual-declared-{'Init'},('direct imports mismatch',name))
        for module,entry in direct.items():
            path=Path(entry['path'])
            if module in project:
                need(entry['kind']=='project' and path==overlay/(module.replace('.','/')+'.olean'),('project route mismatch',name,module))
                sourceguard=expected_base if module in ctx['manifest']['sources'] else outputs[module]
            else:
                roots={'package':ctx['package_root'],'toolchain':ctx['tool_root']}
                need(entry['kind'] in roots and path==roots[entry['kind']]/(module.replace('.','/')+'.olean'),('external route mismatch',name,module))
                sourceguard=state['external_guards']
            guarded=sourceguard.get(str(path))
            need(isinstance(guarded,dict) and guarded['sha256']==entry['sha256'] and
                 path.is_file() and str(path.resolve())==guarded['realpath'] and digest(path)==entry['sha256'],
                 ('direct producer mismatch',name,module))
    guard(expected_base);guard(state['external_guards']);guard(shadow)
    check_inventory()
    for i,rec in enumerate(records):
        name=order[i];row=rows[name];staged=root/'src'/(name.replace('.','/')+'.lean')
        workspace=ctx['workspace_root']/row['workspace_path']
        need(digest(staged)==digest(workspace)==row['sha256'],('final source drift',name))
        need(digest(rec['log'])==rec['log_sha256'],('final log drift',name))
        guard(outputs[name])
    return {'rows':len(records),'source_status':'CURRENT_AT_AUDIT','output_count':len(outputs),
            'scope':'Terminal state and direct guards only; caller must authenticate base/provider before and after.'}
