#!/usr/bin/env python3
"""Audit saved orientation search witnesses and summarize bounded runs.

Checks word membership in the permitted exact AST-emitter family. Does not
certify literal machine simulation or a PA calibration of changed coding.
"""
from pathlib import Path
import argparse, hashlib, itertools, json, re
import transpose_inputs as t

HERE=Path(__file__).resolve().parent
SPANS=[(18,35),(35,54),(54,70),(70,86),(86,102),(102,121)]
def verify_word(grammar,mode):
    tree=t.c.read_grammar(grammar)
    word=t.b.word(t.b.expanded(tree))
    baseline=t.b.word(t.b.expanded(t.c.read_grammar(HERE/'baseline.grammar.json')))
    assert len(word)==190
    assert word[:18]==baseline[:18] and word[121:128]==baseline[121:128]
    assert word[-3:]==baseline[-3:]
    found=[]
    for j,(lo,hi) in enumerate(SPANS):
        options=[]
        for flags in range(8):
            ref=t.emit(t.orient(t.heads(flags)[j],mode))
            for perm in itertools.permutations('DHA'):
                remap={t.TOK[a]:t.TOK[b] for a,b in zip('DHA',perm)}
                candidate=[remap.get(v,v) for v in ref]
                if candidate==word[lo:hi]:options.append({'flags':flags,'parameter_permutation':''.join(perm)})
        assert options,(grammar,j)
        found.append(options)
    gates=[(commute,swap) for commute,swap in itertools.product(range(2),repeat=2)
           if t.emit(t.orient(t.gate(commute,swap),mode))==word[128:-3]]
    assert gates,grammar
    return {'tokens':190,'permitted_head_options':found,'gate_options':gates,
            'word_sha256':hashlib.sha256(json.dumps(word,separators=(',',':')).encode()).hexdigest()}
def main(output):
    out=[]
    for prefix in ['transpose','retained']:
        for mode in [1,2,3]:
            name=f'{prefix}_mode{mode}'
            log=(HERE/f'{name}.log').read_text()
            bests=re.findall(r'BEST score (\d+) eff (\d+) nodes (\d+) folds (\d+) pen (\d+) iteration (\d+) seconds ([\d.]+)',log)
            done=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',log)
            last=bests[-1]
            rec={'run':name,'mode':mode,'completed':bool(done),'best_score':int(last[0]),
                 'reader_score':int(last[1]),'reader_nodes':int(last[2]),'compatible_local_folds':int(last[3]),
                 'scanner_penalty':int(last[4]),'nominal_total':134+int(last[1]),
                 'best_iteration':int(last[5]),'best_seconds':float(last[6]),
                 'proof_scope':'search score and exact emitter word; no machine certificate or PA calibration',
                 'grammar_audit':verify_word(HERE/f'{name}.best.grammar.json',mode)}
            if done:rec['final']={'iterations':int(done[1]),'accepted':int(done[2]),'hits':int(done[3]),'seconds':float(done[5])}
            else:
                cycles=re.findall(r'CYCLE .* iterations (\d+) nodes (\d+) seconds ([\d.]+)',log)
                if cycles:rec['last_recorded']={'iterations':int(cycles[-1][0]),'seconds':float(cycles[-1][2])}
                rec['termination']='No DONE record; the original mode2/mode3 tool processes exited137, not successful completion.' if prefix=='transpose' else 'Still running or no successful completion record.'
            out.append(rec)
    result={'baseline_reader_score':60,'baseline_nominal_total':194,'experiments':out,
            'sub194_constructed':False,'no_global_lower_bound_claimed':True}
    assert json.loads(json.dumps(result))==json.loads((HERE/'search_summary.json').read_text()), 'Recorded summary differs from reconstructed evidence'
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ['run','completed','reader_score','nominal_total']} for r in out]))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'audit_result.json')
    main(parser.parse_args().output)
