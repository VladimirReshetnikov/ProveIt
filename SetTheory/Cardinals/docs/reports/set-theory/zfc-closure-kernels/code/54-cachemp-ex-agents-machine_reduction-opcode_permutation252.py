#!/usr/bin/env python3
"""Twelve bounded compiler experiments permuting MP/DROP/NIP code positions.

The AX branch and operand decoder remain fixed. Both cache-MP's original NIP
and a specialized H=1 NIP are considered. Graph counts are always labeled
separately from complete affine runtime checks and blank initialization.
"""
import itertools,json,time,hashlib
from functools import lru_cache
import role_aware_compiler252 as rc

def main():
    started=time.monotonic();results=[]
    for specialized in (False,True):
        for perm in itertools.permutations((198,48,189)):
            nodes=rc.NODES.copy()
            if specialized:
                nodes[189]=(('N',188),('N',187))
                nodes[188]=(('D',5),('N',186))
                nodes[186]=(('N',168),('H',))
            for n,body in zip((199,193,190),perm):nodes[n]=(nodes[n][0],('N',body))
            try:
                table,meta=rc.compile(nodes)
                result=rc.c.run(table,nodes,rc.ROOT)
                entry={'specialized_nip':specialized,'body_assignment':perm,
                       'graph_states':len(rc.r.gc(table))//2,
                       'cases':result['cases_checked'],
                       'failures':result['failures'],'compiler':meta}
                if not result['failures'] and (entry['graph_states']<252 or (not specialized and perm==(48,198,189))):
                    stem='mp-drop-swap252' if perm==(48,198,189) and not specialized else f'opcode-special{int(specialized)}-'+ '-'.join(map(str,perm))
                    folder=rc.r.HERE/'rotation-candidates'
                    graph=rc.r.gc(table)
                    assert all(tuple(row) in graph for row in result['used_rows'])
                    assert all((str(q),b) in graph for q,b in rc.c.audit.BOX_PAIRS)
                    rc.r.save(folder/(stem+'.tm'),graph)
                    out=folder/(stem+'.tm');out.write_text(out.read_text().replace('#! start 64\n','#! start 0\n',1))
                    (folder/(stem+'.json')).write_text(json.dumps({'nodes':nodes,'root':rc.ROOT,'physical':rc.r.NEWPHYS,'start':0,'description':'Cache MP opcode0 and DROP opcode1 exchanged; no blank startup yet proved.'},indent=2)+'\n')
                    @lru_cache(None)
                    def fp(e):
                        text='N('+','.join(fp(x) for x in nodes[e[1]])+')' if e[0]=='N' else ':'.join(map(str,e))
                        return hashlib.sha256(text.encode()).hexdigest()
                    decoder={'root':rc.ROOT,'nodes':nodes,'fingerprints':{str(n):fp(('N',n)) for n in nodes},'state_entries':meta['decoder_entries'],'leaf_entries':rc.DATA['leaf_entries'],'opaque_cuts':[],'physical':list(rc.r.NEWPHYS),'warning':'Reconstructed decoder-entry map; complete affine checks passed, blank startup not certified.'}
                    (rc.r.HERE/(stem+'-decoder-entries.json')).write_text(json.dumps(decoder,indent=2)+'\n')
                    (rc.r.HERE/(stem+'-check.json')).write_text(json.dumps(result,indent=2)+'\n')
                    entry['table']=stem+'.tm'
                    entry['table_sha256']=hashlib.sha256(out.read_bytes()).hexdigest()
            except (AssertionError,KeyError) as ex:
                entry={'specialized_nip':specialized,'body_assignment':perm,
                       'compiler_error':str(ex)}
            results.append(entry)
            print({k:v for k,v in entry.items() if k not in ('failures','compiler')},
                  'failures',len(entry.get('failures',[])),flush=True)
    (rc.r.HERE/'opcode-permutation252-results.json').write_text(json.dumps({
        'results':results,'elapsed_seconds':time.monotonic()-started,
        'scope':'Six assignments times two NIP bodies. One role-aware compiler heuristic per assignment; complete strict affine checks per produced table. Graph costs and checker failures are not lower bounds on other compilations.'},indent=2)+'\n')

if __name__=='__main__':main()
