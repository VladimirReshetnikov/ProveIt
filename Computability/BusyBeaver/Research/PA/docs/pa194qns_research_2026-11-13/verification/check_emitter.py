#!/usr/bin/env python3
"""Replay the Q emitter change and exchange proof using retained pure helpers.

parent_source_audit.py is the unchanged helper module from the supplied QN
packet. This adapter does not call its old package-layout-specific main()
and does not import a compiler, builder, or physical symbolic runtime.
"""
import argparse,hashlib,json,sys
from pathlib import Path
import parent_source_audit as audit

ROOT=Path(__file__).resolve().parent.parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    assert __debug__ and not sys.flags.optimize,'Assertions must be enabled.'
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    q=ROOT/'inputs/q.grammar.json';old=ROOT/'inputs/primary.grammar.json'
    certificate=ROOT/'verification/exchange_certificate.json'
    new_word=audit.macro_word(audit.load(q));old_word=audit.macro_word(audit.load(old))
    audit.require(len(new_word)==len(old_word)==190,'AX word length')
    audit.require(new_word[:102]==old_word[:102] and new_word[121:]==old_word[121:],'Changed AX tokens outside exchanged head')
    U=lambda i,f:('U',i,f)
    P,Q,R=U('D','A'),U('D',audit.imp('A','H')),U('D','H')
    old_head=audit.imp(P,audit.imp(Q,R));new_head=audit.imp(Q,audit.imp(P,R))
    audit.require(audit.execute_block(old_word[102:121])==(['old_T'],audit.raw(old_head)),'Old head formula/stack effect')
    audit.require(audit.execute_block(new_word[102:121])==(['old_T'],audit.raw(new_head)),'New head formula/stack effect')
    exchange=audit.check_exchange(audit.load(certificate))
    audit.require(exchange['lines']==61,'Unexpected exchange proof length')
    result={'status':'PASS','macro_tokens':190,'only_changed_macro_interval_half_open':[102,121],
            'old_head':old_head,'new_head':new_head,'block_stack_effect':'Push incoming top and preserve the older stack.',
            'exchange':exchange,'input_sha256':{'q.grammar.json':digest(q),'primary.grammar.json':digest(old),
              'exchange_certificate.json':digest(certificate),'parent_source_audit.py':digest(Path(audit.__file__))},
            'scope':'Exact finite symbolic emitter and K/S/MP proof-template replay. K and S and PA calibration retain their stated inherited mathematical dependencies.'}
    text=json.dumps(result,indent=2)+'\n';a.output.write_text(text);print(text,end='')

if __name__=='__main__':main()
