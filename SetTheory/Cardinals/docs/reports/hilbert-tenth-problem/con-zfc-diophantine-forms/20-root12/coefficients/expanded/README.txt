ACTUAL EXPANDED COMPACT COEFFICIENTS

The four .bin files store nonnegative integers in unsigned big-endian binary,
using the minimum whole-byte length. Any unused high bits of the first byte
are zero. There is no sign byte, header, text encoding, or compression.

Port mapping:
  beta.bin       = B - 1
  K.bin          = D_C + B * D_R
  MC.bin         = native low mask M_C
  MF_source.bin  = native field mask M_F + B - 1

Do not use MF_source as the native field mask itself. Recover the native
field mask by subtracting beta. Use all four integers as one tuple with
the exact tiles4094.json ordering and coefficient proof in the parent folder.

Python example:
  value = int.from_bytes(open('K.bin', 'rb').read(), 'big')

MANIFEST.json records SHA-256 hashes, exact bit lengths, populations and
byte lengths. The four files total 25,421,252 bytes (about 25.4 MB).
Run ../audit_compact.py --materialize from any working directory to
reproduce the finite checks and all files from the pinned literal inputs.

These actual integers instantiate the ordinary mathematical compiler
adapter. Their expansion does not itself prove the inherited universal
compiler, the K215 endpoint, or consistency of ZFC.
