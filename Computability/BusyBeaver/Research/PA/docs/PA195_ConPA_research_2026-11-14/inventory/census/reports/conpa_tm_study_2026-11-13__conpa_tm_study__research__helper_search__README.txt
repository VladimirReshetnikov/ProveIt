FINITE-WINDOW SHARED-HELPER SCREEN

helper.cpp is the exact two-merges/one-new-helper search used for the 196-state
tables. It admits bit-writing, left/right-moving helper actions and rejoins the
old one-step endpoint within its radius-four window and 31-step bound. The
source context collector uses the packet's symbolic runtime. No compatible
net-saving shared helper was found in the recorded inputs.

Compile and replay the Combined196 screen from the packet root:
  g++ -O3 -std=c++17 research/helper_search/helper.cpp -o helper_screen
  ./helper_screen machines/h_only_mp_h.tm research/helper_search/h_only_mp_h_contexts.txt helper_results.txt

The source collector and combine.py are included as adapted experimental
code. Run combine.py from its own directory after compiling helper.cpp there
to an executable named helper. The primary artifact verifier is ../../verify.py.
The rebracketed tables/receipts come from an earlier supplied research report;
the combined rebracketed variant and its no-candidate searches are new here.
Source filenames and state counts do not imply a certified machine below 196.
