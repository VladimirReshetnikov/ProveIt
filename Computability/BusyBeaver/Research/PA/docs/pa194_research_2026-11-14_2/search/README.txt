Search evidence
===============

See contractions/README.txt and modal_heads/README.txt for the complete
bounded contraction and logical-emitter searches. Their negative outcomes
are not state-count lower bounds.

The physical-layout experiment uses a C++17 compiler:

  g++ -std=c++17 -O3 search_layout.cpp -o search_layout
  ./search_layout ax11h_layout_input.native.tm path.txt
  ./search_layout primary_layout_input.native.tm path.txt

Both exact native tables and the required initial source address are
included. The program considers every permutation fixing physical position
6: 8! = 40,320. It redirects non-box entry rows through that permutation,
leaves arithmetic-box rows unchanged, and checks an exact complete initial
frame with extra gap 0 and 26 one-valued spare registers. Each screen has
100,000 transitions and tape coordinates -512 through 1535 available.

ax11h_results.txt: 137 successful screens, 40,183 unsuccessful under those
limits. Best observed initialization: 48,320, permutation
[5,3,1,4,7,0,6,8,2]. This became the principal AX11HR construction and was
then checked with the complete independent symbolic source engine, exact
startup, and duration/endpoint audit.

results.txt: primary-PA194 search, 152 successes and 40,168 unsuccessful
screens. Best observed initialization: 40,856, permutation
[2,1,8,3,5,7,6,0,4]. It is retained as exploratory evidence rather than
substituted for the AX11H-calibrated principal construction.

An unsuccessful bounded screen does not prove impossible startup; a
candidate could need more time, more tape, another frame or another gap.
The positive whole-tape certificate for the delivered AX11HR table is exact.

