"""Translate a matched control certificate to an eager certificate.

Usage: python3 translate.py byte|supply INPUT.json OUTPUT.json
Only exact integer zero in the administrative-major field is replaced.
Numerical zero, mode fields, templates and the public goal are unchanged.
"""
import json,sys
from pathlib import Path

def translate(document,profile):
    result=[]
    for packet in document[:-1]:
        if type(packet) is list and len(packet)==4:
            packet=packet.copy()
            index=3 if profile=='byte' else 0
            if type(packet[index]) is int and packet[index]==0:
                packet[index]=[]
        result.append(packet)
    return result+document[-1:]

if __name__=='__main__':
    profile,source,destination=sys.argv[1:]
    if profile not in ('byte','supply'):raise ValueError('Choose byte or supply')
    Path(destination).write_text(json.dumps(translate(json.loads(Path(source).read_text()),profile))+'\n')
