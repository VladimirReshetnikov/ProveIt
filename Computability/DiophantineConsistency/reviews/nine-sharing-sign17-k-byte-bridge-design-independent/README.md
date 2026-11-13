# Independent external K digit-layout review

PASS. Starting from the pinned decompressed K snapshot, this checker independently extracts base-2^47 digits by repeated division and verifies each digit against the reversed 986-entry coefficient array and three sentinel positions. There are 2,021 digits: digit 1004 is coefficient 1 plus one (30,099,357,829,123); the maximum digit is below 2^47 = 140,737,488,355,328, so the described layout has no carry. The 11,868-byte snapshot also has 252 full 47-byte blocks and a 24-byte tail, corresponding to 2,016 digits and five tail digits.

This is external Python/snapshot evidence. It does not prove a Lean digit-layout, coefficient-array, gzip or file theorem, and the text's proposed formal route remains untested.
