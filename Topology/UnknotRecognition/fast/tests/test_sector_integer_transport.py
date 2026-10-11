"""Independent exact-sector proofs must survive binary integer transport."""
from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_sector import discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from test_normal_sector_integration import solid_torus,capped_solid_torus
from test_sector_support import fixture,discover_in_sector as discover_support


def encoded_transcript(proof, *, zero='0x0'):
    result=deepcopy(proof)
    for entry in result['rays']:
        entry['quadrilaterals']=[hex(x)if x else zero for x in entry['quadrilaterals']]
        entry['euler_characteristic']=hex(entry['euler_characteristic'])
    if 'q_support_certificate'in result:
        result['q_support_certificate']=encoded_transcript(result['q_support_certificate'],zero=zero)
    return json.loads(json.dumps(result))


class SectorIntegerTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases=[]
        for source,support,phase in (
            (solid_torus(),[(0,1)],'quadrilateral'),
            (capped_solid_torus(),[(1,0)],'quadrilateral'),
            (capped_solid_torus(),[(1,0)],'standard'),
        ):
            proof=discover_in_sector(source,support,phase=phase)['certificate']
            cls.cases.append((source,proof))
        source,support=fixture()
        proof=discover_support(source,support,phase='standard')['certificate']
        assert 'q_support_certificate'in proof
        cls.reduced=(source,proof)
        cls.cases.append(cls.reduced)

    def test_real_source_all_statuses_accept_equivalent_integer_transport(self):
        self.assertEqual({proof['status']for _,proof in self.cases},
            {'NO_POSITIVE_EULER','POSITIVE_EULER_ONLY','NO_VERTEX_DISC_IN_SECTOR'})
        for source,proof in self.cases:
            self.assertTrue(verify_sector_exhaustion(source,proof))
            encoded=encoded_transcript(proof)
            self.assertTrue(verify_sector_exhaustion(source,encoded))
            # Mixed encodings have exactly the same meaning.
            if encoded['rays']:
                encoded['rays'][0]['euler_characteristic']=proof['rays'][0]['euler_characteristic']
                self.assertTrue(verify_sector_exhaustion(source,encoded))

    def test_nested_zero_support_is_decoded_with_producers_disabled(self):
        source,proof=self.reduced
        disabled=('fastunknot.normal_sector.build_sector_kernel',
            'fastunknot.normal_sector.sector_rays','fastunknot.normal_sector._discover_in_kernel',
            'fastunknot.sector_planar.sector_planar_rays')
        with ExitStack()as stack:
            for name in disabled:
                stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            for zero in ('0x0','-0x0','+0X00'):
                self.assertTrue(verify_sector_exhaustion(source,encoded_transcript(proof,zero=zero)))

    def test_malformed_or_changed_ray_numbers_rejected(self):
        source,proof=self.reduced
        for field in ('quadrilaterals','euler_characteristic'):
            for value in (True,False,1.0,None,'1','0x','0xg',[],{},hex(1<<8192)):
                changed=encoded_transcript(proof)
                entry=changed['rays'][0]
                if field=='quadrilaterals':entry[field][0]=value
                else:entry[field]=value
                with self.subTest(field=field,value_type=type(value).__name__):
                    self.assertFalse(verify_sector_exhaustion(source,changed))
        for length_change in (-1,1):
            changed=encoded_transcript(proof)
            row=changed['rays'][0]['quadrilaterals']
            if length_change<0:row.pop()
            else:row.append('0x0')
            self.assertFalse(verify_sector_exhaustion(source,changed))
        changed=encoded_transcript(proof)
        changed['rays'].append(deepcopy(changed['rays'][0]))
        self.assertFalse(verify_sector_exhaustion(source,changed))

    def test_large_json_safe_mutation_is_checked_without_decimal_conversion(self):
        source,proof=self.reduced
        for nested in (False,True):
            changed=deepcopy(proof)
            target=changed['q_support_certificate']if nested else changed
            target['rays'][0]['quadrilaterals'][0]=1<<16384
            transported=json.loads(json.dumps(json_safe(changed)))
            chosen=transported['q_support_certificate']if nested else transported
            self.assertIsInstance(chosen['rays'][0]['quadrilaterals'][0],str)
            self.assertFalse(verify_sector_exhaustion(source,transported))

    def test_metadata_and_cancellation_remain_strict(self):
        source,proof=self.reduced
        changed=encoded_transcript(proof)
        changed['allowed_types'][0][0]='0x0'
        self.assertFalse(verify_sector_exhaustion(source,changed))
        def interrupt():raise InterruptedError('cancelled')
        with self.assertRaises(InterruptedError):
            verify_sector_exhaustion(source,encoded_transcript(proof),check=interrupt)


if __name__=='__main__':unittest.main()
