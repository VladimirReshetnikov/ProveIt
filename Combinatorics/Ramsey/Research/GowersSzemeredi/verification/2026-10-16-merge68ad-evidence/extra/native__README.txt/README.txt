Merge68ad native validation preparation

This package was prepared without running or importing native/capture/source-guard helpers.
common.py, capture.py and run.py are byte-identical to the reviewed NEXT829 package.
plan.json is remeasured on the resolved Lean sources at merge commit a87906dc3960604bc3a0b423868d392b43ba85c0.
All 153 changed production owners and 1,668 of 1,671 dependent consumers are covered.
Only the same three aggregate facades are excluded as native roots; they remain protected inputs.
The original 1/65/18 roots suffice; core/shared/supplemental module counts are 572/1915/351.
Inventory normalization has completed. No source snapshot was captured and no native checker was run.
A new committed snapshot and sequential fresh validation chain are still required.
The old 5e5a native outcomes do not certify merged sources.
