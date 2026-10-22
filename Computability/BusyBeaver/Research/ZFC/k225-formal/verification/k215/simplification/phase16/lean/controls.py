"""Pure metadata negative controls. No packet capture or proof tools."""
import copy, json
import packet

def run():
    passed = []
    def reject(name, action):
        try: action()
        except AssertionError: passed.append(name)
        else: raise AssertionError('accepted ' + name)
    base = {'A':{'source_sha256':'a','imports':['Init']}, 'B':{'source_sha256':'b','imports':['A']}}
    assert packet.closure(base, ['B']) == {'A','B'} and packet.compatible(base, base, 'B')
    for key, value in [('source_sha256','changed'),('imports',[])]:
        changed = copy.deepcopy(base); changed['A'][key] = value
        assert not packet.compatible(changed, base, 'B')  # Equal B object bytes cannot mask this.
        passed.append('transitive_' + key)
    row = {'source':'candidate','source_sha256':'a','imports':['Init']}
    packet.bind_source(row, row, None)
    for key, value in [('source','other'),('source_sha256','other'),('imports',[])]:
        changed = {**row,key:value}; reject('override_' + key, lambda: packet.bind_source(changed,row,None))
    outer = {'status':'PASS_OUTER_EXIT_ZERO','exit_code':0,'timed_out':False,'argv':['held'],'freeze_sha256':packet.FREEZE,'frozen_files_unchanged':True}
    packet.outer_gate(outer,['held'])
    for key,value in [('status','FAIL'),('exit_code',143),('timed_out',True),('argv',['different']),('freeze_sha256','other'),('frozen_files_unchanged',False)]:
        reject('outer_' + key, lambda: packet.outer_gate({**outer,key:value},['held']))
    old = ['old1','old2','old3','old4']; actual = old + [packet.ROOT + '/retired']
    packet.absence_gate(actual,old,'retired')
    reject('wrong_retirement',lambda:packet.absence_gate(old+['other'],old,'retired'))
    return {'status':'PASS_METADATA_CONTROLS','positive_count':4,'negative_count':len(passed),'negative_cases':passed,'scope':'Direct pure metadata gates only; no actual packet or compiler.'}

if __name__ == '__main__': print(json.dumps(run(), indent=2))
