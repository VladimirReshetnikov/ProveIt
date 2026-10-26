# Limits of the same uniform power-of-two scaling argument

This is a scoped local comparison, separate from the complete frozen
[length2953 proof](PROOF.md). It explains why doubling helps this
particular layout and why further uniform powers do not automatically
shorten its clause. It is not a global lower bound for Diophantine
equations, native encodings, marker locations or other carry arguments.

Keep rho=2^47, the942-selector language, all34 label positions, physical
marker A=1005, bare terms18 and1005, and spatial term9. Let c_e denote
the unscaled coefficients of the complete proof and M=2^44. For a
uniform scale s=2^a, the corresponding reflected clause and mask are

    Acl=s*n+2^(10+a)*Q,
    mu_a=s*M-2*s.

The mask has43 tests at bits a+1 through a+43, provided0<=a<=3; this
keeps the entire mask within one47-bit field. If the complete low part
`s*n+k+tau+b` is below2^(10+a), those tests force it below2s, hence
n<=1. The doubled construction proves precisely this condition at a=1.
This note does not supply every global-carry/controller condition for
the other scales.

After alignment and predecessor reset, an occupied clause has value
`s*M+s+b`, with b the Boolean bare-marker contribution. For s=1,
b=1 sets the forbidden bit1. For every s>=2, both b=0 and b=1 fit
below2s and are locally allowed. This is the useful new freedom at
scale2: its clause can overlap an arbitrary selector bit without
restricting the decoded language. If the chosen scale makes s*M=rho,
the same low-bit observation still holds modulo rho, but the outgoing
carry changes; no completeness theorem for that case is asserted here.

## The unconditional reset band imposes exact local bounds

The retained phase proof resets every output0..1004 before any count
or label decoding. Marker1005 only needs its incoming carry to be zero.
At a candidate clause center C, a reflected contribution at output h
has coefficient index t+f with t=C-h and f a physical position. Before
decoding those physical bits are independent Boolean inputs. A temporal
digit may be rho/2. Thus a complete local reflected sum exceeding rho/2
already defeats this same unconditional reset estimate, even without
adding the nonnegative bare, spatial or incoming-carry contributions.

For t=940 and941 all relevant differences f are among0..45, hence are
physical selector positions. Therefore the exact maximum includes all
the indicated coefficients simultaneously. The calibrated values are

    c_941=15015588664321,
    c_940=15015454446593,
    sum of unscaled label weights=M-1024.

At scale2, t=941 gives

    2*(c_941+M-1024)=65215549415426 < rho/2-60.

This is the sufficient envelope used at C1945, where h<=1004 implies
t>=941. At t=940 the exact envelope is instead

    2*(c_940+c_941+M-1024)=95246458308612 > rho/2.

For any integral center985<=C<=1944, choose h=C-940. Then h lies
in45..1004 and exposes exactly that same failing local envelope. The
lower bound C>=985 is necessary merely to keep all reflected powers
nonnegative. Thus center1945 is the least center compatible with this
particular complete pre-decoding reset estimate at scale2, fixed A1005
and the full independent-Boolean physical domain. The failure does not
produce a whole native solution and does not preclude a different proof.

At scale4, t=941 already gives

    4*(c_941+M-1024)=130431098830852 > rho/2.

Every985<=C<=1945 exposes that envelope at h=C-941. Excluding selector
941 requires C>=1946 under the same reset-band argument. For label-only
indices the sum4*(M-1024)=rho/2-4096 does leave a positive local margin,
but a complete scale4 construction would still require all other masks,
predecessors, actual ranks and controller conditions to be proved.

At scale8, even t=950 gives

    8*(2^43+2^35-1024)=70643622076416 > rho/2.

Here2^43 is the last south-label weight and2^35-1024 is the sum of
all the other label blocks. Their differences0..35 are again physical.
Every985<=C<=1954 exposes this failing envelope at h=C-950. To avoid
that obstruction by the same argument requires C>=1955. For a>=4,
the43 consecutive tests no longer fit within a single47-bit field, so
the stated unchanged-mask family has already ended.

These comparisons explain the local advantage of scale2 over scales4
and8 for this proof architecture. They do not certify any alternative
tuple, improve the accepted equation, rule out a different marker or
phase argument, or prove a minimum outside the explicitly fixed family.
