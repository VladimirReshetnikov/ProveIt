From Coq Require Import Lists.List Arith.PeanoNat NArith Lia.
Require Import DrainCore CoreContraction.
Import ListNotations.

Inductive tree (A : Type) :=
| Empty : tree A
| Branch : tree A -> N -> A -> tree A -> tree A.
Arguments Empty {A}.
Arguments Branch {A}.

Fixpoint lookup {A} (t : tree A) (q : N) : option A :=
  match t with
  | Empty => None
  | Branch l k a r =>
      match N.compare q k with
      | Eq => Some a | Lt => lookup l q | Gt => lookup r q
      end
  end.

Fixpoint elements {A} (t : tree A) : list (N * A) :=
  match t with
  | Empty => []
  | Branch l k a r => (k,a) :: elements l ++ elements r
  end.

Lemma lookup_member {A} (t : tree A) q a :
  lookup t q = Some a -> In (q,a) (elements t).
Proof.
  induction t as [|l IHl k x r IHr]; simpl; [discriminate|].
  destruct (N.compare q k) eqn:E; intro H.
  - apply N.compare_eq_iff in E; subst. inversion H; subst; left; reflexivity.
  - right; apply in_or_app; left; apply IHl; assumption.
  - right; apply in_or_app; right; apply IHr; assumption.
Qed.

Definition k215_tree : tree node :=
(Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 0%N (Test 8 (Arc 9%N []) (Arc 2%N []))
 Empty) 2%N (Test 0 (Arc 2%N [(6,1);(8,1)]) (Arc 7%N [(0,1)]))
 Empty) 7%N (Test 6 (Arc 7%N [(0,1)]) (Arc 9%N []))
 (Branch (Branch Empty 9%N (Test 8 (Arc 11%N [(7,1)]) (Arc 17%N []))
 Empty) 11%N (Test 6 (Arc 9%N []) (Arc 13%N []))
 Empty)) 13%N (Test 7 (Arc 13%N [(6,1)]) (Arc 9%N []))
 (Branch (Branch (Branch Empty 17%N (Test 7 (Arc 17%N [(8,1)]) (Arc 20%N []))
 Empty) 20%N (Test 6 (Arc 20%N [(3,1)]) (Arc 23%N []))
 Empty) 23%N (Test 3 (Arc 24%N []) (Arc 4726%N [(6,1)]))
 (Branch (Branch Empty 24%N (Test 3 (Arc 25%N []) (Arc 4698%N []))
 Empty) 25%N (Test 3 (Arc 26%N []) (Arc 4591%N []))
 Empty))) 26%N (Test 1 (Arc 26%N [(6,1)]) (Arc 29%N []))
 (Branch (Branch (Branch (Branch Empty 29%N (Test 2 (Arc 29%N [(1,1)]) (Arc 32%N []))
 Empty) 32%N (Test 1 (Arc 32%N [(6,1);(7,1)]) (Arc 36%N []))
 Empty) 36%N (Test 6 (Arc 38%N [(7,1)]) (Arc 42%N []))
 (Branch (Branch Empty 38%N (Test 6 (Arc 38%N [(1,1)]) (Arc 32%N []))
 Empty) 42%N (Test 7 (Arc 42%N [(2,1)]) (Arc 45%N []))
 Empty)) 45%N (Test 4 (Arc 45%N [(1,1);(6,1)]) (Arc 49%N []))
 (Branch (Branch (Branch Empty 49%N (Test 6 (Arc 49%N [(4,1)]) (Arc 52%N []))
 Empty) 52%N (Test 1 (Arc 52%N [(6,1)]) (Arc 55%N []))
 Empty) 55%N (Test 2 (Arc 55%N [(1,1)]) (Arc 58%N []))
 (Branch Empty 58%N (Test 1 (Arc 58%N [(6,1);(7,1)]) (Arc 62%N []))
 Empty)))) 62%N (Test 6 (Arc 64%N [(7,1)]) (Arc 68%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 64%N (Test 6 (Arc 64%N [(1,1)]) (Arc 58%N []))
 Empty) 68%N (Test 7 (Arc 68%N [(2,1)]) (Arc 71%N []))
 Empty) 71%N (Test 5 (Arc 71%N [(1,1);(6,1)]) (Arc 75%N []))
 (Branch (Branch Empty 75%N (Test 6 (Arc 75%N [(5,1)]) (Arc 78%N []))
 Empty) 78%N (Test 2 (Arc 80%N [(7,1)]) (Arc 86%N []))
 Empty)) 80%N (Test 6 (Arc 78%N []) (Arc 82%N []))
 (Branch (Branch (Branch Empty 82%N (Test 7 (Arc 82%N [(6,1)]) (Arc 78%N []))
 Empty) 86%N (Test 7 (Arc 86%N [(2,1)]) (Arc 89%N []))
 Empty) 89%N (Test 1 (Arc 89%N [(6,1);(7,1)]) (Arc 93%N []))
 (Branch Empty 93%N (Test 6 (Arc 95%N [(7,1)]) (Arc 99%N []))
 Empty))) 95%N (Test 6 (Arc 95%N [(1,1)]) (Arc 89%N []))
 (Branch (Branch (Branch (Branch Empty 99%N (Test 7 (Arc 99%N [(1,4)]) (Arc 107%N [(1,2)]))
 Empty) 107%N (Test 1 (Arc 107%N [(6,1)]) (Arc 110%N []))
 Empty) 110%N (Test 2 (Arc 110%N [(1,1)]) (Arc 113%N []))
 (Branch (Branch Empty 113%N (Test 1 (Arc 113%N [(6,1);(7,1)]) (Arc 117%N []))
 Empty) 117%N (Test 6 (Arc 119%N [(7,1)]) (Arc 123%N []))
 Empty)) 119%N (Test 6 (Arc 119%N [(1,1)]) (Arc 113%N []))
 (Branch (Branch (Branch Empty 123%N (Test 7 (Arc 123%N [(2,1)]) (Arc 126%N []))
 Empty) 126%N (Test 3 (Arc 126%N [(1,1);(6,1)]) (Arc 130%N []))
 Empty) 130%N (Test 6 (Arc 130%N [(3,1)]) (Arc 133%N []))
 (Branch Empty 133%N (Test 1 (Arc 133%N [(6,1)]) (Arc 136%N []))
 Empty))))) 136%N (Test 2 (Arc 136%N [(1,1)]) (Arc 139%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 139%N (Test 1 (Arc 139%N [(6,1);(7,1)]) (Arc 143%N []))
 Empty) 143%N (Test 6 (Arc 145%N [(7,1)]) (Arc 149%N []))
 Empty) 145%N (Test 6 (Arc 145%N [(1,1)]) (Arc 139%N []))
 (Branch (Branch Empty 149%N (Test 7 (Arc 149%N [(2,1)]) (Arc 152%N []))
 Empty) 152%N (Test 4 (Arc 152%N [(1,1);(6,1)]) (Arc 156%N []))
 Empty)) 156%N (Test 6 (Arc 156%N [(4,1)]) (Arc 159%N []))
 (Branch (Branch (Branch Empty 159%N (Test 8 (Arc 161%N [(7,1)]) (Arc 167%N []))
 Empty) 161%N (Test 6 (Arc 159%N []) (Arc 163%N []))
 Empty) 163%N (Test 7 (Arc 163%N [(6,1)]) (Arc 159%N []))
 (Branch (Branch Empty 167%N (Test 7 (Arc 167%N [(8,1)]) (Arc 170%N []))
 Empty) 170%N (Test 6 (Arc 170%N [(5,1)]) (Arc 173%N []))
 Empty))) 173%N (Test 2 (Arc 175%N [(7,1)]) (Arc 181%N []))
 (Branch (Branch (Branch (Branch Empty 175%N (Test 6 (Arc 173%N []) (Arc 177%N []))
 Empty) 177%N (Test 7 (Arc 177%N [(6,1)]) (Arc 173%N []))
 Empty) 181%N (Test 7 (Arc 181%N [(2,1)]) (Arc 184%N []))
 (Branch (Branch Empty 184%N (Test 1 (Arc 184%N [(6,1);(7,1)]) (Arc 188%N []))
 Empty) 188%N (Test 6 (Arc 190%N [(7,1)]) (Arc 194%N []))
 Empty)) 190%N (Test 6 (Arc 190%N [(1,1)]) (Arc 184%N []))
 (Branch (Branch (Branch Empty 194%N (Test 7 (Arc 194%N [(1,4)]) (Arc 200%N []))
 Empty) 200%N (Test 8 (Arc 202%N [(7,1)]) (Arc 208%N []))
 Empty) 202%N (Test 6 (Arc 200%N []) (Arc 204%N []))
 (Branch Empty 204%N (Test 7 (Arc 204%N [(6,1)]) (Arc 200%N []))
 Empty)))) 208%N (Test 7 (Arc 208%N [(8,1)]) (Arc 211%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 211%N (Test 6 (Arc 211%N [(4,1)]) (Arc 214%N []))
 Empty) 214%N (Test 1 (Arc 214%N [(6,1)]) (Arc 217%N []))
 Empty) 217%N (Test 2 (Arc 217%N [(1,1)]) (Arc 220%N []))
 (Branch (Branch Empty 220%N (Test 1 (Arc 220%N [(6,1);(7,1)]) (Arc 224%N []))
 Empty) 224%N (Test 6 (Arc 226%N [(7,1)]) (Arc 230%N []))
 Empty)) 226%N (Test 6 (Arc 226%N [(1,1)]) (Arc 220%N []))
 (Branch (Branch (Branch Empty 230%N (Test 7 (Arc 230%N [(2,1)]) (Arc 233%N []))
 Empty) 233%N (Test 4 (Arc 233%N [(1,1);(6,1)]) (Arc 237%N []))
 Empty) 237%N (Test 6 (Arc 237%N [(4,1)]) (Arc 240%N []))
 (Branch Empty 240%N (Test 2 (Arc 242%N [(7,1)]) (Arc 248%N []))
 Empty))) 242%N (Test 6 (Arc 240%N []) (Arc 244%N []))
 (Branch (Branch (Branch (Branch Empty 244%N (Test 7 (Arc 244%N [(6,1)]) (Arc 240%N []))
 Empty) 248%N (Test 7 (Arc 248%N [(2,1)]) (Arc 251%N []))
 Empty) 251%N (Test 1 (Arc 251%N [(6,1);(7,1)]) (Arc 255%N []))
 (Branch (Branch Empty 255%N (Test 6 (Arc 257%N [(7,1)]) (Arc 261%N []))
 Empty) 257%N (Test 6 (Arc 257%N [(1,1)]) (Arc 251%N []))
 Empty)) 261%N (Test 7 (Arc 261%N [(1,4)]) (Arc 267%N []))
 (Branch (Branch (Branch Empty 267%N (Test 1 (Arc 267%N [(6,1)]) (Arc 270%N []))
 Empty) 270%N (Test 2 (Arc 270%N [(1,1)]) (Arc 273%N []))
 Empty) 273%N (Test 1 (Arc 273%N [(6,1);(7,1)]) (Arc 277%N []))
 (Branch Empty 277%N (Test 6 (Arc 279%N [(7,1)]) (Arc 283%N []))
 Empty)))))) 279%N (Test 6 (Arc 279%N [(1,1)]) (Arc 273%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 283%N (Test 7 (Arc 283%N [(2,1)]) (Arc 286%N []))
 Empty) 286%N (Test 4 (Arc 286%N [(1,1);(6,1)]) (Arc 290%N []))
 Empty) 290%N (Test 6 (Arc 290%N [(4,1)]) (Arc 293%N []))
 (Branch (Branch Empty 293%N (Test 1 (Arc 293%N [(6,1)]) (Arc 296%N []))
 Empty) 296%N (Test 2 (Arc 296%N [(1,1)]) (Arc 299%N []))
 Empty)) 299%N (Test 1 (Arc 299%N [(6,1);(7,1)]) (Arc 303%N []))
 (Branch (Branch (Branch Empty 303%N (Test 6 (Arc 305%N [(7,1)]) (Arc 309%N []))
 Empty) 305%N (Test 6 (Arc 305%N [(1,1)]) (Arc 299%N []))
 Empty) 309%N (Test 7 (Arc 309%N [(2,1)]) (Arc 312%N []))
 (Branch (Branch Empty 312%N (Test 3 (Arc 312%N [(1,1);(6,1)]) (Arc 316%N []))
 Empty) 316%N (Test 6 (Arc 316%N [(3,1)]) (Arc 319%N []))
 Empty))) 319%N (Test 2 (Arc 321%N [(7,1)]) (Arc 327%N []))
 (Branch (Branch (Branch (Branch Empty 321%N (Test 6 (Arc 319%N []) (Arc 323%N []))
 Empty) 323%N (Test 7 (Arc 323%N [(6,1)]) (Arc 319%N []))
 Empty) 327%N (Test 7 (Arc 327%N [(2,1)]) (Arc 330%N []))
 (Branch (Branch Empty 330%N (Test 1 (Arc 330%N [(6,1);(7,1)]) (Arc 334%N []))
 Empty) 334%N (Test 6 (Arc 336%N [(7,1)]) (Arc 340%N []))
 Empty)) 336%N (Test 6 (Arc 336%N [(1,1)]) (Arc 330%N []))
 (Branch (Branch (Branch Empty 340%N (Test 7 (Arc 340%N [(1,4)]) (Arc 346%N []))
 Empty) 346%N (Test 1 (Arc 346%N [(6,1)]) (Arc 349%N []))
 Empty) 349%N (Test 2 (Arc 349%N [(1,1)]) (Arc 352%N []))
 (Branch Empty 352%N (Test 1 (Arc 352%N [(6,1);(7,1)]) (Arc 356%N []))
 Empty)))) 356%N (Test 6 (Arc 358%N [(7,1)]) (Arc 362%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 358%N (Test 6 (Arc 358%N [(1,1)]) (Arc 352%N []))
 Empty) 362%N (Test 7 (Arc 362%N [(2,1)]) (Arc 365%N []))
 Empty) 365%N (Test 5 (Arc 365%N [(1,1);(6,1)]) (Arc 369%N []))
 (Branch (Branch Empty 369%N (Test 6 (Arc 369%N [(5,1)]) (Arc 372%N []))
 Empty) 372%N (Test 1 (Arc 372%N [(6,1)]) (Arc 375%N []))
 Empty)) 375%N (Test 2 (Arc 375%N [(1,1)]) (Arc 378%N []))
 (Branch (Branch (Branch Empty 378%N (Test 1 (Arc 378%N [(6,1);(7,1)]) (Arc 382%N []))
 Empty) 382%N (Test 6 (Arc 384%N [(7,1)]) (Arc 388%N []))
 Empty) 384%N (Test 6 (Arc 384%N [(1,1)]) (Arc 378%N []))
 (Branch Empty 388%N (Test 7 (Arc 388%N [(2,1)]) (Arc 391%N []))
 Empty))) 391%N (Test 3 (Arc 391%N [(1,1);(6,1)]) (Arc 395%N []))
 (Branch (Branch (Branch (Branch Empty 395%N (Test 6 (Arc 395%N [(3,1)]) (Arc 398%N []))
 Empty) 398%N (Test 2 (Arc 400%N [(7,1)]) (Arc 406%N []))
 Empty) 400%N (Test 6 (Arc 398%N []) (Arc 402%N []))
 (Branch (Branch Empty 402%N (Test 7 (Arc 402%N [(6,1)]) (Arc 398%N []))
 Empty) 406%N (Test 7 (Arc 406%N [(2,1)]) (Arc 409%N []))
 Empty)) 409%N (Test 1 (Arc 409%N [(6,1);(7,1)]) (Arc 413%N []))
 (Branch (Branch (Branch Empty 413%N (Test 6 (Arc 415%N [(7,1)]) (Arc 419%N []))
 Empty) 415%N (Test 6 (Arc 415%N [(1,1)]) (Arc 409%N []))
 Empty) 419%N (Test 7 (Arc 419%N [(1,4)]) (Arc 425%N []))
 (Branch Empty 425%N (Test 2 (Arc 427%N [(7,1)]) (Arc 433%N []))
 Empty))))) 427%N (Test 6 (Arc 425%N []) (Arc 429%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 429%N (Test 7 (Arc 429%N [(6,1)]) (Arc 425%N []))
 Empty) 433%N (Test 7 (Arc 433%N [(2,1)]) (Arc 436%N []))
 Empty) 436%N (Test 1 (Arc 436%N [(6,1);(7,1)]) (Arc 440%N []))
 (Branch (Branch Empty 440%N (Test 6 (Arc 442%N [(7,1)]) (Arc 446%N []))
 Empty) 442%N (Test 6 (Arc 442%N [(1,1)]) (Arc 436%N []))
 Empty)) 446%N (Test 7 (Arc 446%N [(1,4)]) (Arc 452%N []))
 (Branch (Branch (Branch Empty 452%N (Test 2 (Arc 454%N [(7,1)]) (Arc 460%N []))
 Empty) 454%N (Test 6 (Arc 452%N []) (Arc 456%N []))
 Empty) 456%N (Test 7 (Arc 456%N [(6,1)]) (Arc 452%N []))
 (Branch Empty 460%N (Test 7 (Arc 460%N [(2,1)]) (Arc 463%N []))
 Empty))) 463%N (Test 1 (Arc 463%N [(6,1);(7,1)]) (Arc 467%N []))
 (Branch (Branch (Branch (Branch Empty 467%N (Test 6 (Arc 469%N [(7,1)]) (Arc 473%N []))
 Empty) 469%N (Test 6 (Arc 469%N [(1,1)]) (Arc 463%N []))
 Empty) 473%N (Test 7 (Arc 473%N [(1,4)]) (Arc 479%N []))
 (Branch (Branch Empty 479%N (Test 1 (Arc 479%N [(6,1)]) (Arc 482%N []))
 Empty) 482%N (Test 2 (Arc 482%N [(1,1)]) (Arc 485%N []))
 Empty)) 485%N (Test 1 (Arc 485%N [(6,1);(7,1)]) (Arc 489%N []))
 (Branch (Branch (Branch Empty 489%N (Test 6 (Arc 491%N [(7,1)]) (Arc 495%N []))
 Empty) 491%N (Test 6 (Arc 491%N [(1,1)]) (Arc 485%N []))
 Empty) 495%N (Test 7 (Arc 495%N [(2,1)]) (Arc 498%N []))
 (Branch Empty 498%N (Test 3 (Arc 498%N [(1,1);(6,1)]) (Arc 502%N []))
 Empty)))) 502%N (Test 6 (Arc 502%N [(3,1)]) (Arc 505%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 505%N (Test 1 (Arc 505%N [(6,1)]) (Arc 508%N []))
 Empty) 508%N (Test 2 (Arc 508%N [(1,1)]) (Arc 511%N []))
 Empty) 511%N (Test 1 (Arc 511%N [(6,1);(7,1)]) (Arc 515%N []))
 (Branch (Branch Empty 515%N (Test 6 (Arc 517%N [(7,1)]) (Arc 521%N []))
 Empty) 517%N (Test 6 (Arc 517%N [(1,1)]) (Arc 511%N []))
 Empty)) 521%N (Test 7 (Arc 521%N [(2,1)]) (Arc 524%N []))
 (Branch (Branch (Branch Empty 524%N (Test 4 (Arc 524%N [(1,1);(6,1)]) (Arc 528%N []))
 Empty) 528%N (Test 6 (Arc 528%N [(4,1)]) (Arc 531%N []))
 Empty) 531%N (Test 2 (Arc 533%N [(7,1)]) (Arc 539%N []))
 (Branch Empty 533%N (Test 6 (Arc 531%N []) (Arc 535%N []))
 Empty))) 535%N (Test 7 (Arc 535%N [(6,1)]) (Arc 531%N []))
 (Branch (Branch (Branch (Branch Empty 539%N (Test 7 (Arc 539%N [(2,1)]) (Arc 542%N []))
 Empty) 542%N (Test 1 (Arc 542%N [(6,1);(7,1)]) (Arc 546%N []))
 Empty) 546%N (Test 6 (Arc 548%N [(7,1)]) (Arc 552%N []))
 (Branch (Branch Empty 548%N (Test 6 (Arc 548%N [(1,1)]) (Arc 542%N []))
 Empty) 552%N (Test 7 (Arc 552%N [(1,4)]) (Arc 561%N [(1,3)]))
 Empty)) 561%N (Test 1 (Arc 561%N [(6,1)]) (Arc 564%N []))
 (Branch (Branch (Branch Empty 564%N (Test 2 (Arc 564%N [(1,1)]) (Arc 567%N []))
 Empty) 567%N (Test 1 (Arc 567%N [(6,1);(7,1)]) (Arc 571%N []))
 Empty) 571%N (Test 6 (Arc 573%N [(7,1)]) (Arc 577%N []))
 (Branch Empty 573%N (Test 6 (Arc 573%N [(1,1)]) (Arc 567%N []))
 Empty))))))) 577%N (Test 7 (Arc 577%N [(2,1)]) (Arc 580%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 580%N (Test 3 (Arc 580%N [(1,1);(6,1)]) (Arc 584%N []))
 Empty) 584%N (Test 6 (Arc 584%N [(3,1)]) (Arc 587%N []))
 Empty) 587%N (Test 1 (Arc 587%N [(6,1)]) (Arc 590%N []))
 (Branch (Branch Empty 590%N (Test 2 (Arc 590%N [(1,1)]) (Arc 593%N []))
 Empty) 593%N (Test 1 (Arc 593%N [(6,1);(7,1)]) (Arc 597%N []))
 Empty)) 597%N (Test 6 (Arc 599%N [(7,1)]) (Arc 603%N []))
 (Branch (Branch (Branch Empty 599%N (Test 6 (Arc 599%N [(1,1)]) (Arc 593%N []))
 Empty) 603%N (Test 7 (Arc 603%N [(2,1)]) (Arc 606%N []))
 Empty) 606%N (Test 5 (Arc 606%N [(1,1);(6,1)]) (Arc 610%N []))
 (Branch (Branch Empty 610%N (Test 6 (Arc 610%N [(5,1)]) (Arc 613%N []))
 Empty) 613%N (Test 2 (Arc 615%N [(7,1)]) (Arc 621%N []))
 Empty))) 615%N (Test 6 (Arc 613%N []) (Arc 617%N []))
 (Branch (Branch (Branch (Branch Empty 617%N (Test 7 (Arc 617%N [(6,1)]) (Arc 613%N []))
 Empty) 621%N (Test 7 (Arc 621%N [(2,1)]) (Arc 624%N []))
 Empty) 624%N (Test 1 (Arc 624%N [(6,1);(7,1)]) (Arc 628%N []))
 (Branch (Branch Empty 628%N (Test 6 (Arc 630%N [(7,1)]) (Arc 634%N []))
 Empty) 630%N (Test 6 (Arc 630%N [(1,1)]) (Arc 624%N []))
 Empty)) 634%N (Test 7 (Arc 634%N [(1,4)]) (Arc 643%N [(1,3)]))
 (Branch (Branch (Branch Empty 643%N (Test 1 (Arc 643%N [(6,1)]) (Arc 646%N []))
 Empty) 646%N (Test 2 (Arc 646%N [(1,1)]) (Arc 649%N []))
 Empty) 649%N (Test 1 (Arc 649%N [(6,1);(7,1)]) (Arc 653%N []))
 (Branch Empty 653%N (Test 6 (Arc 655%N [(7,1)]) (Arc 659%N []))
 Empty)))) 655%N (Test 6 (Arc 655%N [(1,1)]) (Arc 649%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 659%N (Test 7 (Arc 659%N [(2,1)]) (Arc 662%N []))
 Empty) 662%N (Test 4 (Arc 662%N [(1,1);(6,1)]) (Arc 666%N []))
 Empty) 666%N (Test 6 (Arc 666%N [(4,1)]) (Arc 669%N []))
 (Branch (Branch Empty 669%N (Test 1 (Arc 669%N [(6,1)]) (Arc 672%N []))
 Empty) 672%N (Test 2 (Arc 672%N [(1,1)]) (Arc 675%N []))
 Empty)) 675%N (Test 1 (Arc 675%N [(6,1);(7,1)]) (Arc 679%N []))
 (Branch (Branch (Branch Empty 679%N (Test 6 (Arc 681%N [(7,1)]) (Arc 685%N []))
 Empty) 681%N (Test 6 (Arc 681%N [(1,1)]) (Arc 675%N []))
 Empty) 685%N (Test 7 (Arc 685%N [(2,1)]) (Arc 688%N []))
 (Branch Empty 688%N (Test 5 (Arc 688%N [(1,1);(6,1)]) (Arc 692%N []))
 Empty))) 692%N (Test 6 (Arc 692%N [(5,1)]) (Arc 695%N []))
 (Branch (Branch (Branch (Branch Empty 695%N (Test 2 (Arc 697%N [(7,1)]) (Arc 703%N []))
 Empty) 697%N (Test 6 (Arc 695%N []) (Arc 699%N []))
 Empty) 699%N (Test 7 (Arc 699%N [(6,1)]) (Arc 695%N []))
 (Branch (Branch Empty 703%N (Test 7 (Arc 703%N [(2,1)]) (Arc 706%N []))
 Empty) 706%N (Test 1 (Arc 706%N [(6,1);(7,1)]) (Arc 710%N []))
 Empty)) 710%N (Test 6 (Arc 712%N [(7,1)]) (Arc 716%N []))
 (Branch (Branch (Branch Empty 712%N (Test 6 (Arc 712%N [(1,1)]) (Arc 706%N []))
 Empty) 716%N (Test 7 (Arc 716%N [(1,4)]) (Arc 723%N [(1,1)]))
 Empty) 723%N (Test 1 (Arc 723%N [(6,1)]) (Arc 726%N []))
 (Branch Empty 726%N (Test 2 (Arc 726%N [(1,1)]) (Arc 729%N []))
 Empty))))) 729%N (Test 1 (Arc 729%N [(6,1);(7,1)]) (Arc 733%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 733%N (Test 6 (Arc 735%N [(7,1)]) (Arc 739%N []))
 Empty) 735%N (Test 6 (Arc 735%N [(1,1)]) (Arc 729%N []))
 Empty) 739%N (Test 7 (Arc 739%N [(2,1)]) (Arc 742%N []))
 (Branch (Branch Empty 742%N (Test 4 (Arc 742%N [(1,1);(6,1)]) (Arc 746%N []))
 Empty) 746%N (Test 6 (Arc 746%N [(4,1)]) (Arc 749%N []))
 Empty)) 749%N (Test 1 (Arc 749%N [(6,1)]) (Arc 752%N []))
 (Branch (Branch (Branch Empty 752%N (Test 2 (Arc 752%N [(1,1)]) (Arc 755%N []))
 Empty) 755%N (Test 1 (Arc 755%N [(6,1);(7,1)]) (Arc 759%N []))
 Empty) 759%N (Test 6 (Arc 761%N [(7,1)]) (Arc 765%N []))
 (Branch Empty 761%N (Test 6 (Arc 761%N [(1,1)]) (Arc 755%N []))
 Empty))) 765%N (Test 7 (Arc 765%N [(2,1)]) (Arc 768%N []))
 (Branch (Branch (Branch (Branch Empty 768%N (Test 5 (Arc 768%N [(1,1);(6,1)]) (Arc 772%N []))
 Empty) 772%N (Test 6 (Arc 772%N [(5,1)]) (Arc 775%N []))
 Empty) 775%N (Test 2 (Arc 777%N [(7,1)]) (Arc 783%N []))
 (Branch (Branch Empty 777%N (Test 6 (Arc 775%N []) (Arc 779%N []))
 Empty) 779%N (Test 7 (Arc 779%N [(6,1)]) (Arc 775%N []))
 Empty)) 783%N (Test 7 (Arc 783%N [(2,1)]) (Arc 786%N []))
 (Branch (Branch (Branch Empty 786%N (Test 1 (Arc 786%N [(6,1);(7,1)]) (Arc 790%N []))
 Empty) 790%N (Test 6 (Arc 792%N [(7,1)]) (Arc 796%N []))
 Empty) 792%N (Test 6 (Arc 792%N [(1,1)]) (Arc 786%N []))
 (Branch Empty 796%N (Test 7 (Arc 796%N [(1,4)]) (Arc 805%N [(1,3)]))
 Empty)))) 805%N (Test 2 (Arc 807%N [(7,1)]) (Arc 813%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 807%N (Test 6 (Arc 805%N []) (Arc 809%N []))
 Empty) 809%N (Test 7 (Arc 809%N [(6,1)]) (Arc 805%N []))
 Empty) 813%N (Test 7 (Arc 813%N [(2,1)]) (Arc 816%N []))
 (Branch (Branch Empty 816%N (Test 1 (Arc 816%N [(6,1);(7,1)]) (Arc 820%N []))
 Empty) 820%N (Test 6 (Arc 822%N [(7,1)]) (Arc 826%N []))
 Empty)) 822%N (Test 6 (Arc 822%N [(1,1)]) (Arc 816%N []))
 (Branch (Branch (Branch Empty 826%N (Test 7 (Arc 826%N [(1,4)]) (Arc 834%N [(1,2)]))
 Empty) 834%N (Test 2 (Arc 836%N [(7,1)]) (Arc 842%N []))
 Empty) 836%N (Test 6 (Arc 834%N []) (Arc 838%N []))
 (Branch Empty 838%N (Test 7 (Arc 838%N [(6,1)]) (Arc 834%N []))
 Empty))) 842%N (Test 7 (Arc 842%N [(2,1)]) (Arc 845%N []))
 (Branch (Branch (Branch (Branch Empty 845%N (Test 1 (Arc 845%N [(6,1);(7,1)]) (Arc 849%N []))
 Empty) 849%N (Test 6 (Arc 851%N [(7,1)]) (Arc 855%N []))
 Empty) 851%N (Test 6 (Arc 851%N [(1,1)]) (Arc 845%N []))
 (Branch (Branch Empty 855%N (Test 7 (Arc 855%N [(1,4)]) (Arc 861%N []))
 Empty) 861%N (Test 2 (Arc 863%N [(7,1)]) (Arc 869%N []))
 Empty)) 863%N (Test 6 (Arc 861%N []) (Arc 865%N []))
 (Branch (Branch (Branch Empty 865%N (Test 7 (Arc 865%N [(6,1)]) (Arc 861%N []))
 Empty) 869%N (Test 7 (Arc 869%N [(2,1)]) (Arc 872%N []))
 Empty) 872%N (Test 1 (Arc 872%N [(6,1);(7,1)]) (Arc 876%N []))
 (Branch Empty 876%N (Test 6 (Arc 878%N [(7,1)]) (Arc 882%N []))
 Empty)))))) 878%N (Test 6 (Arc 878%N [(1,1)]) (Arc 872%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 882%N (Test 7 (Arc 882%N [(1,4)]) (Arc 888%N []))
 Empty) 888%N (Test 1 (Arc 888%N [(6,1)]) (Arc 891%N []))
 Empty) 891%N (Test 2 (Arc 891%N [(1,1)]) (Arc 894%N []))
 (Branch (Branch Empty 894%N (Test 1 (Arc 894%N [(6,1);(7,1)]) (Arc 898%N []))
 Empty) 898%N (Test 6 (Arc 900%N [(7,1)]) (Arc 904%N []))
 Empty)) 900%N (Test 6 (Arc 900%N [(1,1)]) (Arc 894%N []))
 (Branch (Branch (Branch Empty 904%N (Test 7 (Arc 904%N [(2,1)]) (Arc 907%N []))
 Empty) 907%N (Test 4 (Arc 907%N [(1,1);(6,1)]) (Arc 911%N []))
 Empty) 911%N (Test 6 (Arc 911%N [(4,1)]) (Arc 914%N []))
 (Branch (Branch Empty 914%N (Test 1 (Arc 914%N [(6,1)]) (Arc 917%N []))
 Empty) 917%N (Test 2 (Arc 917%N [(1,1)]) (Arc 920%N []))
 Empty))) 920%N (Test 1 (Arc 920%N [(6,1);(7,1)]) (Arc 924%N []))
 (Branch (Branch (Branch (Branch Empty 924%N (Test 6 (Arc 926%N [(7,1)]) (Arc 930%N []))
 Empty) 926%N (Test 6 (Arc 926%N [(1,1)]) (Arc 920%N []))
 Empty) 930%N (Test 7 (Arc 930%N [(2,1)]) (Arc 933%N []))
 (Branch (Branch Empty 933%N (Test 4 (Arc 933%N [(1,1);(6,1)]) (Arc 937%N []))
 Empty) 937%N (Test 6 (Arc 937%N [(4,1)]) (Arc 940%N []))
 Empty)) 940%N (Test 1 (Arc 940%N [(6,1)]) (Arc 943%N []))
 (Branch (Branch (Branch Empty 943%N (Test 2 (Arc 943%N [(1,1)]) (Arc 946%N []))
 Empty) 946%N (Test 1 (Arc 946%N [(6,1);(7,1)]) (Arc 950%N []))
 Empty) 950%N (Test 6 (Arc 952%N [(7,1)]) (Arc 956%N []))
 (Branch Empty 952%N (Test 6 (Arc 952%N [(1,1)]) (Arc 946%N []))
 Empty)))) 956%N (Test 7 (Arc 956%N [(2,1)]) (Arc 959%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 959%N (Test 3 (Arc 959%N [(1,1);(6,1)]) (Arc 963%N []))
 Empty) 963%N (Test 6 (Arc 963%N [(3,1)]) (Arc 966%N []))
 Empty) 966%N (Test 2 (Arc 968%N [(7,1)]) (Arc 974%N []))
 (Branch (Branch Empty 968%N (Test 6 (Arc 966%N []) (Arc 970%N []))
 Empty) 970%N (Test 7 (Arc 970%N [(6,1)]) (Arc 966%N []))
 Empty)) 974%N (Test 7 (Arc 974%N [(2,1)]) (Arc 977%N []))
 (Branch (Branch (Branch Empty 977%N (Test 1 (Arc 977%N [(6,1);(7,1)]) (Arc 981%N []))
 Empty) 981%N (Test 6 (Arc 983%N [(7,1)]) (Arc 987%N []))
 Empty) 983%N (Test 6 (Arc 983%N [(1,1)]) (Arc 977%N []))
 (Branch Empty 987%N (Test 7 (Arc 987%N [(1,4)]) (Arc 995%N [(1,2)]))
 Empty))) 995%N (Test 1 (Arc 995%N [(6,1)]) (Arc 998%N []))
 (Branch (Branch (Branch (Branch Empty 998%N (Test 2 (Arc 998%N [(1,1)]) (Arc 1001%N []))
 Empty) 1001%N (Test 1 (Arc 1001%N [(6,1);(7,1)]) (Arc 1005%N []))
 Empty) 1005%N (Test 6 (Arc 1007%N [(7,1)]) (Arc 1011%N []))
 (Branch (Branch Empty 1007%N (Test 6 (Arc 1007%N [(1,1)]) (Arc 1001%N []))
 Empty) 1011%N (Test 7 (Arc 1011%N [(2,1)]) (Arc 1015%N [(1,1)]))
 Empty)) 1015%N (Test 2 (Arc 1017%N [(7,1)]) (Arc 1023%N []))
 (Branch (Branch (Branch Empty 1017%N (Test 6 (Arc 1015%N []) (Arc 1019%N []))
 Empty) 1019%N (Test 7 (Arc 1019%N [(6,1)]) (Arc 1015%N []))
 Empty) 1023%N (Test 7 (Arc 1023%N [(2,1)]) (Arc 1026%N []))
 (Branch Empty 1026%N (Test 1 (Arc 1026%N [(6,1);(7,1)]) (Arc 1030%N []))
 Empty))))) 1030%N (Test 6 (Arc 1032%N [(7,1)]) (Arc 1036%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1032%N (Test 6 (Arc 1032%N [(1,1)]) (Arc 1026%N []))
 Empty) 1036%N (Test 7 (Arc 1036%N [(1,4)]) (Arc 1042%N []))
 Empty) 1042%N (Test 2 (Arc 1044%N [(7,1)]) (Arc 1050%N []))
 (Branch (Branch Empty 1044%N (Test 6 (Arc 1042%N []) (Arc 1046%N []))
 Empty) 1046%N (Test 7 (Arc 1046%N [(6,1)]) (Arc 1042%N []))
 Empty)) 1050%N (Test 7 (Arc 1050%N [(2,1)]) (Arc 1053%N []))
 (Branch (Branch (Branch Empty 1053%N (Test 1 (Arc 1053%N [(6,1);(7,1)]) (Arc 1057%N []))
 Empty) 1057%N (Test 6 (Arc 1059%N [(7,1)]) (Arc 1063%N []))
 Empty) 1059%N (Test 6 (Arc 1059%N [(1,1)]) (Arc 1053%N []))
 (Branch Empty 1063%N (Test 7 (Arc 1063%N [(1,4)]) (Arc 1071%N [(1,2)]))
 Empty))) 1071%N (Test 1 (Arc 1071%N [(6,1)]) (Arc 1074%N []))
 (Branch (Branch (Branch (Branch Empty 1074%N (Test 2 (Arc 1074%N [(1,1)]) (Arc 1077%N []))
 Empty) 1077%N (Test 1 (Arc 1077%N [(6,1);(7,1)]) (Arc 1081%N []))
 Empty) 1081%N (Test 6 (Arc 1083%N [(7,1)]) (Arc 1087%N []))
 (Branch (Branch Empty 1083%N (Test 6 (Arc 1083%N [(1,1)]) (Arc 1077%N []))
 Empty) 1087%N (Test 7 (Arc 1087%N [(2,1)]) (Arc 1091%N [(1,1)]))
 Empty)) 1091%N (Test 2 (Arc 1093%N [(7,1)]) (Arc 1099%N []))
 (Branch (Branch (Branch Empty 1093%N (Test 6 (Arc 1091%N []) (Arc 1095%N []))
 Empty) 1095%N (Test 7 (Arc 1095%N [(6,1)]) (Arc 1091%N []))
 Empty) 1099%N (Test 7 (Arc 1099%N [(2,1)]) (Arc 1102%N []))
 (Branch Empty 1102%N (Test 1 (Arc 1102%N [(6,1);(7,1)]) (Arc 1106%N []))
 Empty)))) 1106%N (Test 6 (Arc 1108%N [(7,1)]) (Arc 1112%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 1108%N (Test 6 (Arc 1108%N [(1,1)]) (Arc 1102%N []))
 Empty) 1112%N (Test 7 (Arc 1112%N [(1,4)]) (Arc 1118%N []))
 Empty) 1118%N (Test 1 (Arc 1118%N [(6,1)]) (Arc 1121%N []))
 (Branch (Branch Empty 1121%N (Test 2 (Arc 1121%N [(1,1)]) (Arc 1124%N []))
 Empty) 1124%N (Test 1 (Arc 1124%N [(6,1);(7,1)]) (Arc 1128%N []))
 Empty)) 1128%N (Test 6 (Arc 1130%N [(7,1)]) (Arc 1134%N []))
 (Branch (Branch (Branch Empty 1130%N (Test 6 (Arc 1130%N [(1,1)]) (Arc 1124%N []))
 Empty) 1134%N (Test 7 (Arc 1134%N [(2,1)]) (Arc 1137%N []))
 Empty) 1137%N (Test 3 (Arc 1137%N [(1,1);(6,1)]) (Arc 1141%N []))
 (Branch Empty 1141%N (Test 6 (Arc 1141%N [(3,1)]) (Arc 1144%N []))
 Empty))) 1144%N (Test 2 (Arc 1146%N [(7,1)]) (Arc 1152%N []))
 (Branch (Branch (Branch (Branch Empty 1146%N (Test 6 (Arc 1144%N []) (Arc 1148%N []))
 Empty) 1148%N (Test 7 (Arc 1148%N [(6,1)]) (Arc 1144%N []))
 Empty) 1152%N (Test 7 (Arc 1152%N [(2,1)]) (Arc 1155%N []))
 (Branch (Branch Empty 1155%N (Test 1 (Arc 1155%N [(6,1);(7,1)]) (Arc 1159%N []))
 Empty) 1159%N (Test 6 (Arc 1161%N [(7,1)]) (Arc 1165%N []))
 Empty)) 1161%N (Test 6 (Arc 1161%N [(1,1)]) (Arc 1155%N []))
 (Branch (Branch (Branch Empty 1165%N (Test 7 (Arc 1165%N [(1,4)]) (Arc 1171%N []))
 Empty) 1171%N (Test 1 (Arc 1171%N [(6,1)]) (Arc 1174%N []))
 Empty) 1174%N (Test 2 (Arc 1174%N [(1,1)]) (Arc 1177%N []))
 (Branch Empty 1177%N (Test 1 (Arc 1177%N [(6,1);(7,1)]) (Arc 1181%N []))
 Empty)))))))) 1181%N (Test 6 (Arc 1183%N [(7,1)]) (Arc 1187%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1183%N (Test 6 (Arc 1183%N [(1,1)]) (Arc 1177%N []))
 Empty) 1187%N (Test 7 (Arc 1187%N [(2,1)]) (Arc 1190%N []))
 Empty) 1190%N (Test 3 (Arc 1190%N [(1,1);(6,1)]) (Arc 1194%N []))
 (Branch (Branch Empty 1194%N (Test 6 (Arc 1194%N [(3,1)]) (Arc 1197%N []))
 Empty) 1197%N (Test 1 (Arc 1197%N [(6,1)]) (Arc 1200%N []))
 Empty)) 1200%N (Test 2 (Arc 1200%N [(1,1)]) (Arc 1203%N []))
 (Branch (Branch (Branch Empty 1203%N (Test 1 (Arc 1203%N [(6,1);(7,1)]) (Arc 1207%N []))
 Empty) 1207%N (Test 6 (Arc 1209%N [(7,1)]) (Arc 1213%N []))
 Empty) 1209%N (Test 6 (Arc 1209%N [(1,1)]) (Arc 1203%N []))
 (Branch (Branch Empty 1213%N (Test 7 (Arc 1213%N [(2,1)]) (Arc 1216%N []))
 Empty) 1216%N (Test 4 (Arc 1216%N [(1,1);(6,1)]) (Arc 1220%N []))
 Empty))) 1220%N (Test 6 (Arc 1220%N [(4,1)]) (Arc 1223%N []))
 (Branch (Branch (Branch (Branch Empty 1223%N (Test 2 (Arc 1225%N [(7,1)]) (Arc 1231%N []))
 Empty) 1225%N (Test 6 (Arc 1223%N []) (Arc 1227%N []))
 Empty) 1227%N (Test 7 (Arc 1227%N [(6,1)]) (Arc 1223%N []))
 (Branch (Branch Empty 1231%N (Test 7 (Arc 1231%N [(2,1)]) (Arc 1234%N []))
 Empty) 1234%N (Test 1 (Arc 1234%N [(6,1);(7,1)]) (Arc 1238%N []))
 Empty)) 1238%N (Test 6 (Arc 1240%N [(7,1)]) (Arc 1244%N []))
 (Branch (Branch (Branch Empty 1240%N (Test 6 (Arc 1240%N [(1,1)]) (Arc 1234%N []))
 Empty) 1244%N (Test 7 (Arc 1244%N [(1,4)]) (Arc 1253%N [(1,3)]))
 Empty) 1253%N (Test 1 (Arc 1253%N [(6,1)]) (Arc 1256%N []))
 (Branch Empty 1256%N (Test 2 (Arc 1256%N [(1,1)]) (Arc 1259%N []))
 Empty)))) 1259%N (Test 1 (Arc 1259%N [(6,1);(7,1)]) (Arc 1263%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 1263%N (Test 6 (Arc 1265%N [(7,1)]) (Arc 1269%N []))
 Empty) 1265%N (Test 6 (Arc 1265%N [(1,1)]) (Arc 1259%N []))
 Empty) 1269%N (Test 7 (Arc 1269%N [(2,1)]) (Arc 1272%N []))
 (Branch (Branch Empty 1272%N (Test 3 (Arc 1272%N [(1,1);(6,1)]) (Arc 1276%N []))
 Empty) 1276%N (Test 6 (Arc 1276%N [(3,1)]) (Arc 1279%N []))
 Empty)) 1279%N (Test 1 (Arc 1279%N [(6,1)]) (Arc 1282%N []))
 (Branch (Branch (Branch Empty 1282%N (Test 2 (Arc 1282%N [(1,1)]) (Arc 1285%N []))
 Empty) 1285%N (Test 1 (Arc 1285%N [(6,1);(7,1)]) (Arc 1289%N []))
 Empty) 1289%N (Test 6 (Arc 1291%N [(7,1)]) (Arc 1295%N []))
 (Branch Empty 1291%N (Test 6 (Arc 1291%N [(1,1)]) (Arc 1285%N []))
 Empty))) 1295%N (Test 7 (Arc 1295%N [(2,1)]) (Arc 1298%N []))
 (Branch (Branch (Branch (Branch Empty 1298%N (Test 5 (Arc 1298%N [(1,1);(6,1)]) (Arc 1302%N []))
 Empty) 1302%N (Test 6 (Arc 1302%N [(5,1)]) (Arc 1305%N []))
 Empty) 1305%N (Test 2 (Arc 1307%N [(7,1)]) (Arc 1313%N []))
 (Branch (Branch Empty 1307%N (Test 6 (Arc 1305%N []) (Arc 1309%N []))
 Empty) 1309%N (Test 7 (Arc 1309%N [(6,1)]) (Arc 1305%N []))
 Empty)) 1313%N (Test 7 (Arc 1313%N [(2,1)]) (Arc 1316%N []))
 (Branch (Branch (Branch Empty 1316%N (Test 1 (Arc 1316%N [(6,1);(7,1)]) (Arc 1320%N []))
 Empty) 1320%N (Test 6 (Arc 1322%N [(7,1)]) (Arc 1326%N []))
 Empty) 1322%N (Test 6 (Arc 1322%N [(1,1)]) (Arc 1316%N []))
 (Branch Empty 1326%N (Test 7 (Arc 1326%N [(1,4)]) (Arc 1333%N [(1,1)]))
 Empty))))) 1333%N (Test 1 (Arc 1333%N [(6,1)]) (Arc 1336%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1336%N (Test 2 (Arc 1336%N [(1,1)]) (Arc 1339%N []))
 Empty) 1339%N (Test 1 (Arc 1339%N [(6,1);(7,1)]) (Arc 1343%N []))
 Empty) 1343%N (Test 6 (Arc 1345%N [(7,1)]) (Arc 1349%N []))
 (Branch (Branch Empty 1345%N (Test 6 (Arc 1345%N [(1,1)]) (Arc 1339%N []))
 Empty) 1349%N (Test 7 (Arc 1349%N [(2,1)]) (Arc 1352%N []))
 Empty)) 1352%N (Test 4 (Arc 1352%N [(1,1);(6,1)]) (Arc 1356%N []))
 (Branch (Branch (Branch Empty 1356%N (Test 6 (Arc 1356%N [(4,1)]) (Arc 1359%N []))
 Empty) 1359%N (Test 1 (Arc 1359%N [(6,1)]) (Arc 1362%N []))
 Empty) 1362%N (Test 2 (Arc 1362%N [(1,1)]) (Arc 1365%N []))
 (Branch (Branch Empty 1365%N (Test 1 (Arc 1365%N [(6,1);(7,1)]) (Arc 1369%N []))
 Empty) 1369%N (Test 6 (Arc 1371%N [(7,1)]) (Arc 1375%N []))
 Empty))) 1371%N (Test 6 (Arc 1371%N [(1,1)]) (Arc 1365%N []))
 (Branch (Branch (Branch (Branch Empty 1375%N (Test 7 (Arc 1375%N [(2,1)]) (Arc 1378%N []))
 Empty) 1378%N (Test 5 (Arc 1378%N [(1,1);(6,1)]) (Arc 1382%N []))
 Empty) 1382%N (Test 6 (Arc 1382%N [(5,1)]) (Arc 1385%N []))
 (Branch (Branch Empty 1385%N (Test 2 (Arc 1387%N [(7,1)]) (Arc 1393%N []))
 Empty) 1387%N (Test 6 (Arc 1385%N []) (Arc 1389%N []))
 Empty)) 1389%N (Test 7 (Arc 1389%N [(6,1)]) (Arc 1385%N []))
 (Branch (Branch (Branch Empty 1393%N (Test 7 (Arc 1393%N [(2,1)]) (Arc 1396%N []))
 Empty) 1396%N (Test 1 (Arc 1396%N [(6,1);(7,1)]) (Arc 1400%N []))
 Empty) 1400%N (Test 6 (Arc 1402%N [(7,1)]) (Arc 1406%N []))
 (Branch Empty 1402%N (Test 6 (Arc 1402%N [(1,1)]) (Arc 1396%N []))
 Empty)))) 1406%N (Test 7 (Arc 1406%N [(1,4)]) (Arc 1413%N [(1,1)]))
 (Branch (Branch (Branch (Branch (Branch Empty 1413%N (Test 2 (Arc 1415%N [(7,1)]) (Arc 1421%N []))
 Empty) 1415%N (Test 6 (Arc 1413%N []) (Arc 1417%N []))
 Empty) 1417%N (Test 7 (Arc 1417%N [(6,1)]) (Arc 1413%N []))
 (Branch (Branch Empty 1421%N (Test 7 (Arc 1421%N [(2,1)]) (Arc 1424%N []))
 Empty) 1424%N (Test 1 (Arc 1424%N [(6,1);(7,1)]) (Arc 1428%N []))
 Empty)) 1428%N (Test 6 (Arc 1430%N [(7,1)]) (Arc 1434%N []))
 (Branch (Branch (Branch Empty 1430%N (Test 6 (Arc 1430%N [(1,1)]) (Arc 1424%N []))
 Empty) 1434%N (Test 7 (Arc 1434%N [(1,4)]) (Arc 1440%N []))
 Empty) 1440%N (Test 2 (Arc 1442%N [(7,1)]) (Arc 1448%N []))
 (Branch Empty 1442%N (Test 6 (Arc 1440%N []) (Arc 1444%N []))
 Empty))) 1444%N (Test 7 (Arc 1444%N [(6,1)]) (Arc 1440%N []))
 (Branch (Branch (Branch (Branch Empty 1448%N (Test 7 (Arc 1448%N [(2,1)]) (Arc 1451%N []))
 Empty) 1451%N (Test 1 (Arc 1451%N [(6,1);(7,1)]) (Arc 1455%N []))
 Empty) 1455%N (Test 6 (Arc 1457%N [(7,1)]) (Arc 1461%N []))
 (Branch (Branch Empty 1457%N (Test 6 (Arc 1457%N [(1,1)]) (Arc 1451%N []))
 Empty) 1461%N (Test 7 (Arc 1461%N [(1,4)]) (Arc 1467%N []))
 Empty)) 1467%N (Test 1 (Arc 1467%N [(6,1)]) (Arc 1470%N []))
 (Branch (Branch (Branch Empty 1470%N (Test 2 (Arc 1470%N [(1,1)]) (Arc 1473%N []))
 Empty) 1473%N (Test 1 (Arc 1473%N [(6,1);(7,1)]) (Arc 1477%N []))
 Empty) 1477%N (Test 6 (Arc 1479%N [(7,1)]) (Arc 1483%N []))
 (Branch Empty 1479%N (Test 6 (Arc 1479%N [(1,1)]) (Arc 1473%N []))
 Empty)))))) 1483%N (Test 7 (Arc 1483%N [(2,1)]) (Arc 1486%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1486%N (Test 4 (Arc 1486%N [(1,1);(6,1)]) (Arc 1490%N []))
 Empty) 1490%N (Test 6 (Arc 1490%N [(4,1)]) (Arc 1493%N []))
 Empty) 1493%N (Test 1 (Arc 1493%N [(6,1)]) (Arc 1496%N []))
 (Branch (Branch Empty 1496%N (Test 2 (Arc 1496%N [(1,1)]) (Arc 1499%N []))
 Empty) 1499%N (Test 1 (Arc 1499%N [(6,1);(7,1)]) (Arc 1503%N []))
 Empty)) 1503%N (Test 6 (Arc 1505%N [(7,1)]) (Arc 1509%N []))
 (Branch (Branch (Branch Empty 1505%N (Test 6 (Arc 1505%N [(1,1)]) (Arc 1499%N []))
 Empty) 1509%N (Test 7 (Arc 1509%N [(2,1)]) (Arc 1512%N []))
 Empty) 1512%N (Test 5 (Arc 1512%N [(1,1);(6,1)]) (Arc 1516%N []))
 (Branch (Branch Empty 1516%N (Test 6 (Arc 1516%N [(5,1)]) (Arc 1519%N []))
 Empty) 1519%N (Test 1 (Arc 1519%N [(6,1)]) (Arc 1522%N []))
 Empty))) 1522%N (Test 2 (Arc 1522%N [(1,1)]) (Arc 1525%N []))
 (Branch (Branch (Branch (Branch Empty 1525%N (Test 1 (Arc 1525%N [(6,1);(7,1)]) (Arc 1529%N []))
 Empty) 1529%N (Test 6 (Arc 1531%N [(7,1)]) (Arc 1535%N []))
 Empty) 1531%N (Test 6 (Arc 1531%N [(1,1)]) (Arc 1525%N []))
 (Branch (Branch Empty 1535%N (Test 7 (Arc 1535%N [(2,1)]) (Arc 1538%N []))
 Empty) 1538%N (Test 3 (Arc 1538%N [(1,1);(6,1)]) (Arc 1542%N []))
 Empty)) 1542%N (Test 6 (Arc 1542%N [(3,1)]) (Arc 1545%N []))
 (Branch (Branch (Branch Empty 1545%N (Test 2 (Arc 1547%N [(7,1)]) (Arc 1553%N []))
 Empty) 1547%N (Test 6 (Arc 1545%N []) (Arc 1549%N []))
 Empty) 1549%N (Test 7 (Arc 1549%N [(6,1)]) (Arc 1545%N []))
 (Branch Empty 1553%N (Test 7 (Arc 1553%N [(2,1)]) (Arc 1556%N []))
 Empty)))) 1556%N (Test 1 (Arc 1556%N [(6,1);(7,1)]) (Arc 1560%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 1560%N (Test 6 (Arc 1562%N [(7,1)]) (Arc 1566%N []))
 Empty) 1562%N (Test 6 (Arc 1562%N [(1,1)]) (Arc 1556%N []))
 Empty) 1566%N (Test 7 (Arc 1566%N [(1,4)]) (Arc 1574%N [(1,2)]))
 (Branch (Branch Empty 1574%N (Test 2 (Arc 1576%N [(7,1)]) (Arc 1582%N []))
 Empty) 1576%N (Test 6 (Arc 1574%N []) (Arc 1578%N []))
 Empty)) 1578%N (Test 7 (Arc 1578%N [(6,1)]) (Arc 1574%N []))
 (Branch (Branch (Branch Empty 1582%N (Test 7 (Arc 1582%N [(2,1)]) (Arc 1585%N []))
 Empty) 1585%N (Test 1 (Arc 1585%N [(6,1);(7,1)]) (Arc 1589%N []))
 Empty) 1589%N (Test 6 (Arc 1591%N [(7,1)]) (Arc 1595%N []))
 (Branch Empty 1591%N (Test 6 (Arc 1591%N [(1,1)]) (Arc 1585%N []))
 Empty))) 1595%N (Test 7 (Arc 1595%N [(1,4)]) (Arc 1603%N [(1,2)]))
 (Branch (Branch (Branch (Branch Empty 1603%N (Test 1 (Arc 1603%N [(6,1)]) (Arc 1606%N []))
 Empty) 1606%N (Test 2 (Arc 1606%N [(1,1)]) (Arc 1609%N []))
 Empty) 1609%N (Test 1 (Arc 1609%N [(6,1);(7,1)]) (Arc 1613%N []))
 (Branch (Branch Empty 1613%N (Test 6 (Arc 1615%N [(7,1)]) (Arc 1619%N []))
 Empty) 1615%N (Test 6 (Arc 1615%N [(1,1)]) (Arc 1609%N []))
 Empty)) 1619%N (Test 7 (Arc 1619%N [(2,1)]) (Arc 1622%N []))
 (Branch (Branch (Branch Empty 1622%N (Test 5 (Arc 1622%N [(1,1);(6,1)]) (Arc 1626%N []))
 Empty) 1626%N (Test 6 (Arc 1626%N [(5,1)]) (Arc 1629%N []))
 Empty) 1629%N (Test 1 (Arc 1629%N [(6,1)]) (Arc 1632%N []))
 (Branch Empty 1632%N (Test 2 (Arc 1632%N [(1,1)]) (Arc 1635%N []))
 Empty))))) 1635%N (Test 1 (Arc 1635%N [(6,1);(7,1)]) (Arc 1639%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1639%N (Test 6 (Arc 1641%N [(7,1)]) (Arc 1645%N []))
 Empty) 1641%N (Test 6 (Arc 1641%N [(1,1)]) (Arc 1635%N []))
 Empty) 1645%N (Test 7 (Arc 1645%N [(2,1)]) (Arc 1648%N []))
 (Branch (Branch Empty 1648%N (Test 4 (Arc 1648%N [(1,1);(6,1)]) (Arc 1652%N []))
 Empty) 1652%N (Test 6 (Arc 1652%N [(4,1)]) (Arc 1655%N []))
 Empty)) 1655%N (Test 1 (Arc 1655%N [(6,1)]) (Arc 1658%N []))
 (Branch (Branch (Branch Empty 1658%N (Test 2 (Arc 1658%N [(1,1)]) (Arc 1661%N []))
 Empty) 1661%N (Test 1 (Arc 1661%N [(6,1);(7,1)]) (Arc 1665%N []))
 Empty) 1665%N (Test 6 (Arc 1667%N [(7,1)]) (Arc 1671%N []))
 (Branch Empty 1667%N (Test 6 (Arc 1667%N [(1,1)]) (Arc 1661%N []))
 Empty))) 1671%N (Test 7 (Arc 1671%N [(2,1)]) (Arc 1674%N []))
 (Branch (Branch (Branch (Branch Empty 1674%N (Test 3 (Arc 1674%N [(1,1);(6,1)]) (Arc 1678%N []))
 Empty) 1678%N (Test 6 (Arc 1678%N [(3,1)]) (Arc 1681%N []))
 Empty) 1681%N (Test 2 (Arc 1683%N [(7,1)]) (Arc 1689%N []))
 (Branch (Branch Empty 1683%N (Test 6 (Arc 1681%N []) (Arc 1685%N []))
 Empty) 1685%N (Test 7 (Arc 1685%N [(6,1)]) (Arc 1681%N []))
 Empty)) 1689%N (Test 7 (Arc 1689%N [(2,1)]) (Arc 1692%N []))
 (Branch (Branch (Branch Empty 1692%N (Test 1 (Arc 1692%N [(6,1);(7,1)]) (Arc 1696%N []))
 Empty) 1696%N (Test 6 (Arc 1698%N [(7,1)]) (Arc 1702%N []))
 Empty) 1698%N (Test 6 (Arc 1698%N [(1,1)]) (Arc 1692%N []))
 (Branch Empty 1702%N (Test 7 (Arc 1702%N [(1,4)]) (Arc 1710%N [(1,2)]))
 Empty)))) 1710%N (Test 2 (Arc 1712%N [(7,1)]) (Arc 1718%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 1712%N (Test 6 (Arc 1710%N []) (Arc 1714%N []))
 Empty) 1714%N (Test 7 (Arc 1714%N [(6,1)]) (Arc 1710%N []))
 Empty) 1718%N (Test 7 (Arc 1718%N [(2,1)]) (Arc 1721%N []))
 (Branch (Branch Empty 1721%N (Test 1 (Arc 1721%N [(6,1);(7,1)]) (Arc 1725%N []))
 Empty) 1725%N (Test 6 (Arc 1727%N [(7,1)]) (Arc 1731%N []))
 Empty)) 1727%N (Test 6 (Arc 1727%N [(1,1)]) (Arc 1721%N []))
 (Branch (Branch (Branch Empty 1731%N (Test 7 (Arc 1731%N [(1,4)]) (Arc 1739%N [(1,2)]))
 Empty) 1739%N (Test 2 (Arc 1741%N [(7,1)]) (Arc 1747%N []))
 Empty) 1741%N (Test 6 (Arc 1739%N []) (Arc 1743%N []))
 (Branch Empty 1743%N (Test 7 (Arc 1743%N [(6,1)]) (Arc 1739%N []))
 Empty))) 1747%N (Test 7 (Arc 1747%N [(2,1)]) (Arc 1750%N []))
 (Branch (Branch (Branch (Branch Empty 1750%N (Test 1 (Arc 1750%N [(6,1);(7,1)]) (Arc 1754%N []))
 Empty) 1754%N (Test 6 (Arc 1756%N [(7,1)]) (Arc 1760%N []))
 Empty) 1756%N (Test 6 (Arc 1756%N [(1,1)]) (Arc 1750%N []))
 (Branch (Branch Empty 1760%N (Test 7 (Arc 1760%N [(1,4)]) (Arc 1766%N []))
 Empty) 1766%N (Test 1 (Arc 1766%N [(6,1)]) (Arc 1769%N []))
 Empty)) 1769%N (Test 2 (Arc 1769%N [(1,1)]) (Arc 1772%N []))
 (Branch (Branch (Branch Empty 1772%N (Test 1 (Arc 1772%N [(6,1);(7,1)]) (Arc 1776%N []))
 Empty) 1776%N (Test 6 (Arc 1778%N [(7,1)]) (Arc 1782%N []))
 Empty) 1778%N (Test 6 (Arc 1778%N [(1,1)]) (Arc 1772%N []))
 (Branch Empty 1782%N (Test 7 (Arc 1782%N [(2,1)]) (Arc 1785%N []))
 Empty))))))) 1785%N (Test 4 (Arc 1785%N [(1,1);(6,1)]) (Arc 1789%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1789%N (Test 6 (Arc 1789%N [(4,1)]) (Arc 1792%N []))
 Empty) 1792%N (Test 1 (Arc 1792%N [(6,1)]) (Arc 1795%N []))
 Empty) 1795%N (Test 2 (Arc 1795%N [(1,1)]) (Arc 1798%N []))
 (Branch (Branch Empty 1798%N (Test 1 (Arc 1798%N [(6,1);(7,1)]) (Arc 1802%N []))
 Empty) 1802%N (Test 6 (Arc 1804%N [(7,1)]) (Arc 1808%N []))
 Empty)) 1804%N (Test 6 (Arc 1804%N [(1,1)]) (Arc 1798%N []))
 (Branch (Branch (Branch Empty 1808%N (Test 7 (Arc 1808%N [(2,1)]) (Arc 1811%N []))
 Empty) 1811%N (Test 5 (Arc 1811%N [(1,1);(6,1)]) (Arc 1815%N []))
 Empty) 1815%N (Test 6 (Arc 1815%N [(5,1)]) (Arc 1818%N []))
 (Branch (Branch Empty 1818%N (Test 2 (Arc 1820%N [(7,1)]) (Arc 1826%N []))
 Empty) 1820%N (Test 6 (Arc 1818%N []) (Arc 1822%N []))
 Empty))) 1822%N (Test 7 (Arc 1822%N [(6,1)]) (Arc 1818%N []))
 (Branch (Branch (Branch (Branch Empty 1826%N (Test 7 (Arc 1826%N [(2,1)]) (Arc 1829%N []))
 Empty) 1829%N (Test 1 (Arc 1829%N [(6,1);(7,1)]) (Arc 1833%N []))
 Empty) 1833%N (Test 6 (Arc 1835%N [(7,1)]) (Arc 1839%N []))
 (Branch (Branch Empty 1835%N (Test 6 (Arc 1835%N [(1,1)]) (Arc 1829%N []))
 Empty) 1839%N (Test 7 (Arc 1839%N [(1,4)]) (Arc 1848%N [(1,3)]))
 Empty)) 1848%N (Test 1 (Arc 1848%N [(6,1)]) (Arc 1851%N []))
 (Branch (Branch (Branch Empty 1851%N (Test 2 (Arc 1851%N [(1,1)]) (Arc 1854%N []))
 Empty) 1854%N (Test 1 (Arc 1854%N [(6,1);(7,1)]) (Arc 1858%N []))
 Empty) 1858%N (Test 6 (Arc 1860%N [(7,1)]) (Arc 1864%N []))
 (Branch Empty 1860%N (Test 6 (Arc 1860%N [(1,1)]) (Arc 1854%N []))
 Empty)))) 1864%N (Test 7 (Arc 1864%N [(2,1)]) (Arc 1867%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 1867%N (Test 3 (Arc 1867%N [(1,1);(6,1)]) (Arc 1871%N []))
 Empty) 1871%N (Test 6 (Arc 1871%N [(3,1)]) (Arc 1874%N []))
 Empty) 1874%N (Test 1 (Arc 1874%N [(6,1)]) (Arc 1877%N []))
 (Branch (Branch Empty 1877%N (Test 2 (Arc 1877%N [(1,1)]) (Arc 1880%N []))
 Empty) 1880%N (Test 1 (Arc 1880%N [(6,1);(7,1)]) (Arc 1884%N []))
 Empty)) 1884%N (Test 6 (Arc 1886%N [(7,1)]) (Arc 1890%N []))
 (Branch (Branch (Branch Empty 1886%N (Test 6 (Arc 1886%N [(1,1)]) (Arc 1880%N []))
 Empty) 1890%N (Test 7 (Arc 1890%N [(2,1)]) (Arc 1893%N []))
 Empty) 1893%N (Test 4 (Arc 1893%N [(1,1);(6,1)]) (Arc 1897%N []))
 (Branch Empty 1897%N (Test 6 (Arc 1897%N [(4,1)]) (Arc 1900%N []))
 Empty))) 1900%N (Test 2 (Arc 1902%N [(7,1)]) (Arc 1908%N []))
 (Branch (Branch (Branch (Branch Empty 1902%N (Test 6 (Arc 1900%N []) (Arc 1904%N []))
 Empty) 1904%N (Test 7 (Arc 1904%N [(6,1)]) (Arc 1900%N []))
 Empty) 1908%N (Test 7 (Arc 1908%N [(2,1)]) (Arc 1911%N []))
 (Branch (Branch Empty 1911%N (Test 1 (Arc 1911%N [(6,1);(7,1)]) (Arc 1915%N []))
 Empty) 1915%N (Test 6 (Arc 1917%N [(7,1)]) (Arc 1921%N []))
 Empty)) 1917%N (Test 6 (Arc 1917%N [(1,1)]) (Arc 1911%N []))
 (Branch (Branch (Branch Empty 1921%N (Test 7 (Arc 1921%N [(1,4)]) (Arc 1928%N [(1,1)]))
 Empty) 1928%N (Test 1 (Arc 1928%N [(6,1)]) (Arc 1931%N []))
 Empty) 1931%N (Test 2 (Arc 1931%N [(1,1)]) (Arc 1934%N []))
 (Branch Empty 1934%N (Test 1 (Arc 1934%N [(6,1);(7,1)]) (Arc 1938%N []))
 Empty))))) 1938%N (Test 6 (Arc 1940%N [(7,1)]) (Arc 1944%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1940%N (Test 6 (Arc 1940%N [(1,1)]) (Arc 1934%N []))
 Empty) 1944%N (Test 7 (Arc 1944%N [(2,1)]) (Arc 1947%N []))
 Empty) 1947%N (Test 3 (Arc 1947%N [(1,1);(6,1)]) (Arc 1951%N []))
 (Branch (Branch Empty 1951%N (Test 6 (Arc 1951%N [(3,1)]) (Arc 1954%N []))
 Empty) 1954%N (Test 1 (Arc 1954%N [(6,1)]) (Arc 1957%N []))
 Empty)) 1957%N (Test 2 (Arc 1957%N [(1,1)]) (Arc 1960%N []))
 (Branch (Branch (Branch Empty 1960%N (Test 1 (Arc 1960%N [(6,1);(7,1)]) (Arc 1964%N []))
 Empty) 1964%N (Test 6 (Arc 1966%N [(7,1)]) (Arc 1970%N []))
 Empty) 1966%N (Test 6 (Arc 1966%N [(1,1)]) (Arc 1960%N []))
 (Branch Empty 1970%N (Test 7 (Arc 1970%N [(2,1)]) (Arc 1973%N []))
 Empty))) 1973%N (Test 5 (Arc 1973%N [(1,1);(6,1)]) (Arc 1977%N []))
 (Branch (Branch (Branch (Branch Empty 1977%N (Test 6 (Arc 1977%N [(5,1)]) (Arc 1980%N []))
 Empty) 1980%N (Test 2 (Arc 1982%N [(7,1)]) (Arc 1988%N []))
 Empty) 1982%N (Test 6 (Arc 1980%N []) (Arc 1984%N []))
 (Branch (Branch Empty 1984%N (Test 7 (Arc 1984%N [(6,1)]) (Arc 1980%N []))
 Empty) 1988%N (Test 7 (Arc 1988%N [(2,1)]) (Arc 1991%N []))
 Empty)) 1991%N (Test 1 (Arc 1991%N [(6,1);(7,1)]) (Arc 1995%N []))
 (Branch (Branch (Branch Empty 1995%N (Test 6 (Arc 1997%N [(7,1)]) (Arc 2001%N []))
 Empty) 1997%N (Test 6 (Arc 1997%N [(1,1)]) (Arc 1991%N []))
 Empty) 2001%N (Test 7 (Arc 2001%N [(1,4)]) (Arc 2008%N [(1,1)]))
 (Branch Empty 2008%N (Test 2 (Arc 2010%N [(7,1)]) (Arc 2016%N []))
 Empty)))) 2010%N (Test 6 (Arc 2008%N []) (Arc 2012%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2012%N (Test 7 (Arc 2012%N [(6,1)]) (Arc 2008%N []))
 Empty) 2016%N (Test 7 (Arc 2016%N [(2,1)]) (Arc 2019%N []))
 Empty) 2019%N (Test 1 (Arc 2019%N [(6,1);(7,1)]) (Arc 2023%N []))
 (Branch (Branch Empty 2023%N (Test 6 (Arc 2025%N [(7,1)]) (Arc 2029%N []))
 Empty) 2025%N (Test 6 (Arc 2025%N [(1,1)]) (Arc 2019%N []))
 Empty)) 2029%N (Test 7 (Arc 2029%N [(1,4)]) (Arc 2035%N []))
 (Branch (Branch (Branch Empty 2035%N (Test 2 (Arc 2037%N [(7,1)]) (Arc 2043%N []))
 Empty) 2037%N (Test 6 (Arc 2035%N []) (Arc 2039%N []))
 Empty) 2039%N (Test 7 (Arc 2039%N [(6,1)]) (Arc 2035%N []))
 (Branch Empty 2043%N (Test 7 (Arc 2043%N [(2,1)]) (Arc 2046%N []))
 Empty))) 2046%N (Test 1 (Arc 2046%N [(6,1);(7,1)]) (Arc 2050%N []))
 (Branch (Branch (Branch (Branch Empty 2050%N (Test 6 (Arc 2052%N [(7,1)]) (Arc 2056%N []))
 Empty) 2052%N (Test 6 (Arc 2052%N [(1,1)]) (Arc 2046%N []))
 Empty) 2056%N (Test 7 (Arc 2056%N [(1,4)]) (Arc 2062%N []))
 (Branch (Branch Empty 2062%N (Test 1 (Arc 2062%N [(6,1)]) (Arc 2065%N []))
 Empty) 2065%N (Test 2 (Arc 2065%N [(1,1)]) (Arc 2068%N []))
 Empty)) 2068%N (Test 1 (Arc 2068%N [(6,1);(7,1)]) (Arc 2072%N []))
 (Branch (Branch (Branch Empty 2072%N (Test 6 (Arc 2074%N [(7,1)]) (Arc 2078%N []))
 Empty) 2074%N (Test 6 (Arc 2074%N [(1,1)]) (Arc 2068%N []))
 Empty) 2078%N (Test 7 (Arc 2078%N [(2,1)]) (Arc 2081%N []))
 (Branch Empty 2081%N (Test 4 (Arc 2081%N [(1,1);(6,1)]) (Arc 2085%N []))
 Empty)))))) 2085%N (Test 6 (Arc 2085%N [(4,1)]) (Arc 2088%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2088%N (Test 1 (Arc 2088%N [(6,1)]) (Arc 2091%N []))
 Empty) 2091%N (Test 2 (Arc 2091%N [(1,1)]) (Arc 2094%N []))
 Empty) 2094%N (Test 1 (Arc 2094%N [(6,1);(7,1)]) (Arc 2098%N []))
 (Branch (Branch Empty 2098%N (Test 6 (Arc 2100%N [(7,1)]) (Arc 2104%N []))
 Empty) 2100%N (Test 6 (Arc 2100%N [(1,1)]) (Arc 2094%N []))
 Empty)) 2104%N (Test 7 (Arc 2104%N [(2,1)]) (Arc 2107%N []))
 (Branch (Branch (Branch Empty 2107%N (Test 5 (Arc 2107%N [(1,1);(6,1)]) (Arc 2111%N []))
 Empty) 2111%N (Test 6 (Arc 2111%N [(5,1)]) (Arc 2114%N []))
 Empty) 2114%N (Test 1 (Arc 2114%N [(6,1)]) (Arc 2117%N []))
 (Branch (Branch Empty 2117%N (Test 2 (Arc 2117%N [(1,1)]) (Arc 2120%N []))
 Empty) 2120%N (Test 1 (Arc 2120%N [(6,1);(7,1)]) (Arc 2124%N []))
 Empty))) 2124%N (Test 6 (Arc 2126%N [(7,1)]) (Arc 2130%N []))
 (Branch (Branch (Branch (Branch Empty 2126%N (Test 6 (Arc 2126%N [(1,1)]) (Arc 2120%N []))
 Empty) 2130%N (Test 7 (Arc 2130%N [(2,1)]) (Arc 2133%N []))
 Empty) 2133%N (Test 3 (Arc 2133%N [(1,1);(6,1)]) (Arc 2137%N []))
 (Branch (Branch Empty 2137%N (Test 6 (Arc 2137%N [(3,1)]) (Arc 2140%N []))
 Empty) 2140%N (Test 2 (Arc 2142%N [(7,1)]) (Arc 2148%N []))
 Empty)) 2142%N (Test 6 (Arc 2140%N []) (Arc 2144%N []))
 (Branch (Branch (Branch Empty 2144%N (Test 7 (Arc 2144%N [(6,1)]) (Arc 2140%N []))
 Empty) 2148%N (Test 7 (Arc 2148%N [(2,1)]) (Arc 2151%N []))
 Empty) 2151%N (Test 1 (Arc 2151%N [(6,1);(7,1)]) (Arc 2155%N []))
 (Branch Empty 2155%N (Test 6 (Arc 2157%N [(7,1)]) (Arc 2161%N []))
 Empty)))) 2157%N (Test 6 (Arc 2157%N [(1,1)]) (Arc 2151%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2161%N (Test 7 (Arc 2161%N [(1,4)]) (Arc 2167%N []))
 Empty) 2167%N (Test 2 (Arc 2169%N [(7,1)]) (Arc 2175%N []))
 Empty) 2169%N (Test 6 (Arc 2167%N []) (Arc 2171%N []))
 (Branch (Branch Empty 2171%N (Test 7 (Arc 2171%N [(6,1)]) (Arc 2167%N []))
 Empty) 2175%N (Test 7 (Arc 2175%N [(2,1)]) (Arc 2178%N []))
 Empty)) 2178%N (Test 1 (Arc 2178%N [(6,1);(7,1)]) (Arc 2182%N []))
 (Branch (Branch (Branch Empty 2182%N (Test 6 (Arc 2184%N [(7,1)]) (Arc 2188%N []))
 Empty) 2184%N (Test 6 (Arc 2184%N [(1,1)]) (Arc 2178%N []))
 Empty) 2188%N (Test 7 (Arc 2188%N [(1,4)]) (Arc 2196%N [(1,2)]))
 (Branch Empty 2196%N (Test 1 (Arc 2196%N [(6,1)]) (Arc 2199%N []))
 Empty))) 2199%N (Test 2 (Arc 2199%N [(1,1)]) (Arc 2202%N []))
 (Branch (Branch (Branch (Branch Empty 2202%N (Test 1 (Arc 2202%N [(6,1);(7,1)]) (Arc 2206%N []))
 Empty) 2206%N (Test 6 (Arc 2208%N [(7,1)]) (Arc 2212%N []))
 Empty) 2208%N (Test 6 (Arc 2208%N [(1,1)]) (Arc 2202%N []))
 (Branch (Branch Empty 2212%N (Test 7 (Arc 2212%N [(2,1)]) (Arc 2215%N []))
 Empty) 2215%N (Test 4 (Arc 2215%N [(1,1);(6,1)]) (Arc 2219%N []))
 Empty)) 2219%N (Test 6 (Arc 2219%N [(4,1)]) (Arc 2222%N []))
 (Branch (Branch (Branch Empty 2222%N (Test 1 (Arc 2222%N [(6,1)]) (Arc 2225%N []))
 Empty) 2225%N (Test 2 (Arc 2225%N [(1,1)]) (Arc 2228%N []))
 Empty) 2228%N (Test 1 (Arc 2228%N [(6,1);(7,1)]) (Arc 2232%N []))
 (Branch Empty 2232%N (Test 6 (Arc 2234%N [(7,1)]) (Arc 2238%N []))
 Empty))))) 2234%N (Test 6 (Arc 2234%N [(1,1)]) (Arc 2228%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2238%N (Test 7 (Arc 2238%N [(2,1)]) (Arc 2241%N []))
 Empty) 2241%N (Test 5 (Arc 2241%N [(1,1);(6,1)]) (Arc 2245%N []))
 Empty) 2245%N (Test 6 (Arc 2245%N [(5,1)]) (Arc 2248%N []))
 (Branch (Branch Empty 2248%N (Test 2 (Arc 2250%N [(7,1)]) (Arc 2256%N []))
 Empty) 2250%N (Test 6 (Arc 2248%N []) (Arc 2252%N []))
 Empty)) 2252%N (Test 7 (Arc 2252%N [(6,1)]) (Arc 2248%N []))
 (Branch (Branch (Branch Empty 2256%N (Test 7 (Arc 2256%N [(2,1)]) (Arc 2259%N []))
 Empty) 2259%N (Test 1 (Arc 2259%N [(6,1);(7,1)]) (Arc 2263%N []))
 Empty) 2263%N (Test 6 (Arc 2265%N [(7,1)]) (Arc 2269%N []))
 (Branch Empty 2265%N (Test 6 (Arc 2265%N [(1,1)]) (Arc 2259%N []))
 Empty))) 2269%N (Test 7 (Arc 2269%N [(1,4)]) (Arc 2277%N [(1,2)]))
 (Branch (Branch (Branch (Branch Empty 2277%N (Test 1 (Arc 2277%N [(6,1)]) (Arc 2280%N []))
 Empty) 2280%N (Test 2 (Arc 2280%N [(1,1)]) (Arc 2283%N []))
 Empty) 2283%N (Test 1 (Arc 2283%N [(6,1);(7,1)]) (Arc 2287%N []))
 (Branch (Branch Empty 2287%N (Test 6 (Arc 2289%N [(7,1)]) (Arc 2293%N []))
 Empty) 2289%N (Test 6 (Arc 2289%N [(1,1)]) (Arc 2283%N []))
 Empty)) 2293%N (Test 7 (Arc 2293%N [(2,1)]) (Arc 2296%N []))
 (Branch (Branch (Branch Empty 2296%N (Test 4 (Arc 2296%N [(1,1);(6,1)]) (Arc 2300%N []))
 Empty) 2300%N (Test 6 (Arc 2300%N [(4,1)]) (Arc 2303%N []))
 Empty) 2303%N (Test 1 (Arc 2303%N [(6,1)]) (Arc 2306%N []))
 (Branch Empty 2306%N (Test 2 (Arc 2306%N [(1,1)]) (Arc 2309%N []))
 Empty)))) 2309%N (Test 1 (Arc 2309%N [(6,1);(7,1)]) (Arc 2313%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2313%N (Test 6 (Arc 2315%N [(7,1)]) (Arc 2319%N []))
 Empty) 2315%N (Test 6 (Arc 2315%N [(1,1)]) (Arc 2309%N []))
 Empty) 2319%N (Test 7 (Arc 2319%N [(2,1)]) (Arc 2322%N []))
 (Branch (Branch Empty 2322%N (Test 3 (Arc 2322%N [(1,1);(6,1)]) (Arc 2326%N []))
 Empty) 2326%N (Test 6 (Arc 2326%N [(3,1)]) (Arc 2329%N []))
 Empty)) 2329%N (Test 2 (Arc 2331%N [(7,1)]) (Arc 2337%N []))
 (Branch (Branch (Branch Empty 2331%N (Test 6 (Arc 2329%N []) (Arc 2333%N []))
 Empty) 2333%N (Test 7 (Arc 2333%N [(6,1)]) (Arc 2329%N []))
 Empty) 2337%N (Test 7 (Arc 2337%N [(2,1)]) (Arc 2340%N []))
 (Branch Empty 2340%N (Test 1 (Arc 2340%N [(6,1);(7,1)]) (Arc 2344%N []))
 Empty))) 2344%N (Test 6 (Arc 2346%N [(7,1)]) (Arc 2350%N []))
 (Branch (Branch (Branch (Branch Empty 2346%N (Test 6 (Arc 2346%N [(1,1)]) (Arc 2340%N []))
 Empty) 2350%N (Test 7 (Arc 2350%N [(1,4)]) (Arc 2358%N [(1,2)]))
 Empty) 2358%N (Test 2 (Arc 2360%N [(7,1)]) (Arc 2366%N []))
 (Branch (Branch Empty 2360%N (Test 6 (Arc 2358%N []) (Arc 2362%N []))
 Empty) 2362%N (Test 7 (Arc 2362%N [(6,1)]) (Arc 2358%N []))
 Empty)) 2366%N (Test 7 (Arc 2366%N [(2,1)]) (Arc 2369%N []))
 (Branch (Branch (Branch Empty 2369%N (Test 1 (Arc 2369%N [(6,1);(7,1)]) (Arc 2373%N []))
 Empty) 2373%N (Test 6 (Arc 2375%N [(7,1)]) (Arc 2379%N []))
 Empty) 2375%N (Test 6 (Arc 2375%N [(1,1)]) (Arc 2369%N []))
 (Branch Empty 2379%N (Test 7 (Arc 2379%N [(1,4)]) (Arc 2385%N []))
 Empty))))))))) 2385%N (Test 2 (Arc 2387%N [(7,1)]) (Arc 2393%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2387%N (Test 6 (Arc 2385%N []) (Arc 2389%N []))
 Empty) 2389%N (Test 7 (Arc 2389%N [(6,1)]) (Arc 2385%N []))
 Empty) 2393%N (Test 7 (Arc 2393%N [(2,1)]) (Arc 2396%N []))
 (Branch (Branch Empty 2396%N (Test 1 (Arc 2396%N [(6,1);(7,1)]) (Arc 2400%N []))
 Empty) 2400%N (Test 6 (Arc 2402%N [(7,1)]) (Arc 2406%N []))
 Empty)) 2402%N (Test 6 (Arc 2402%N [(1,1)]) (Arc 2396%N []))
 (Branch (Branch (Branch Empty 2406%N (Test 7 (Arc 2406%N [(1,4)]) (Arc 2412%N []))
 Empty) 2412%N (Test 1 (Arc 2412%N [(6,1)]) (Arc 2415%N []))
 Empty) 2415%N (Test 2 (Arc 2415%N [(1,1)]) (Arc 2418%N []))
 (Branch (Branch Empty 2418%N (Test 1 (Arc 2418%N [(6,1);(7,1)]) (Arc 2422%N []))
 Empty) 2422%N (Test 6 (Arc 2424%N [(7,1)]) (Arc 2428%N []))
 Empty))) 2424%N (Test 6 (Arc 2424%N [(1,1)]) (Arc 2418%N []))
 (Branch (Branch (Branch (Branch Empty 2428%N (Test 7 (Arc 2428%N [(2,1)]) (Arc 2431%N []))
 Empty) 2431%N (Test 4 (Arc 2431%N [(1,1);(6,1)]) (Arc 2435%N []))
 Empty) 2435%N (Test 6 (Arc 2435%N [(4,1)]) (Arc 2438%N []))
 (Branch (Branch Empty 2438%N (Test 1 (Arc 2438%N [(6,1)]) (Arc 2441%N []))
 Empty) 2441%N (Test 2 (Arc 2441%N [(1,1)]) (Arc 2444%N []))
 Empty)) 2444%N (Test 1 (Arc 2444%N [(6,1);(7,1)]) (Arc 2448%N []))
 (Branch (Branch (Branch Empty 2448%N (Test 6 (Arc 2450%N [(7,1)]) (Arc 2454%N []))
 Empty) 2450%N (Test 6 (Arc 2450%N [(1,1)]) (Arc 2444%N []))
 Empty) 2454%N (Test 7 (Arc 2454%N [(2,1)]) (Arc 2457%N []))
 (Branch Empty 2457%N (Test 4 (Arc 2457%N [(1,1);(6,1)]) (Arc 2461%N []))
 Empty)))) 2461%N (Test 6 (Arc 2461%N [(4,1)]) (Arc 2464%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2464%N (Test 1 (Arc 2464%N [(6,1)]) (Arc 2467%N []))
 Empty) 2467%N (Test 2 (Arc 2467%N [(1,1)]) (Arc 2470%N []))
 Empty) 2470%N (Test 1 (Arc 2470%N [(6,1);(7,1)]) (Arc 2474%N []))
 (Branch (Branch Empty 2474%N (Test 6 (Arc 2476%N [(7,1)]) (Arc 2480%N []))
 Empty) 2476%N (Test 6 (Arc 2476%N [(1,1)]) (Arc 2470%N []))
 Empty)) 2480%N (Test 7 (Arc 2480%N [(2,1)]) (Arc 2483%N []))
 (Branch (Branch (Branch Empty 2483%N (Test 5 (Arc 2483%N [(1,1);(6,1)]) (Arc 2487%N []))
 Empty) 2487%N (Test 6 (Arc 2487%N [(5,1)]) (Arc 2490%N []))
 Empty) 2490%N (Test 2 (Arc 2492%N [(7,1)]) (Arc 2498%N []))
 (Branch Empty 2492%N (Test 6 (Arc 2490%N []) (Arc 2494%N []))
 Empty))) 2494%N (Test 7 (Arc 2494%N [(6,1)]) (Arc 2490%N []))
 (Branch (Branch (Branch (Branch Empty 2498%N (Test 7 (Arc 2498%N [(2,1)]) (Arc 2501%N []))
 Empty) 2501%N (Test 1 (Arc 2501%N [(6,1);(7,1)]) (Arc 2505%N []))
 Empty) 2505%N (Test 6 (Arc 2507%N [(7,1)]) (Arc 2511%N []))
 (Branch (Branch Empty 2507%N (Test 6 (Arc 2507%N [(1,1)]) (Arc 2501%N []))
 Empty) 2511%N (Test 7 (Arc 2511%N [(1,4)]) (Arc 2520%N [(1,3)]))
 Empty)) 2520%N (Test 1 (Arc 2520%N [(6,1)]) (Arc 2523%N []))
 (Branch (Branch (Branch Empty 2523%N (Test 2 (Arc 2523%N [(1,1)]) (Arc 2526%N []))
 Empty) 2526%N (Test 1 (Arc 2526%N [(6,1);(7,1)]) (Arc 2530%N []))
 Empty) 2530%N (Test 6 (Arc 2532%N [(7,1)]) (Arc 2536%N []))
 (Branch Empty 2532%N (Test 6 (Arc 2532%N [(1,1)]) (Arc 2526%N []))
 Empty))))) 2536%N (Test 7 (Arc 2536%N [(2,1)]) (Arc 2540%N [(1,1)]))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2540%N (Test 2 (Arc 2542%N [(7,1)]) (Arc 2548%N []))
 Empty) 2542%N (Test 6 (Arc 2540%N []) (Arc 2544%N []))
 Empty) 2544%N (Test 7 (Arc 2544%N [(6,1)]) (Arc 2540%N []))
 (Branch (Branch Empty 2548%N (Test 7 (Arc 2548%N [(2,1)]) (Arc 2551%N []))
 Empty) 2551%N (Test 1 (Arc 2551%N [(6,1);(7,1)]) (Arc 2555%N []))
 Empty)) 2555%N (Test 6 (Arc 2557%N [(7,1)]) (Arc 2561%N []))
 (Branch (Branch (Branch Empty 2557%N (Test 6 (Arc 2557%N [(1,1)]) (Arc 2551%N []))
 Empty) 2561%N (Test 7 (Arc 2561%N [(1,4)]) (Arc 2567%N []))
 Empty) 2567%N (Test 2 (Arc 2569%N [(7,1)]) (Arc 2575%N []))
 (Branch (Branch Empty 2569%N (Test 6 (Arc 2567%N []) (Arc 2571%N []))
 Empty) 2571%N (Test 7 (Arc 2571%N [(6,1)]) (Arc 2567%N []))
 Empty))) 2575%N (Test 7 (Arc 2575%N [(2,1)]) (Arc 2578%N []))
 (Branch (Branch (Branch (Branch Empty 2578%N (Test 1 (Arc 2578%N [(6,1);(7,1)]) (Arc 2582%N []))
 Empty) 2582%N (Test 6 (Arc 2584%N [(7,1)]) (Arc 2588%N []))
 Empty) 2584%N (Test 6 (Arc 2584%N [(1,1)]) (Arc 2578%N []))
 (Branch (Branch Empty 2588%N (Test 7 (Arc 2588%N [(1,4)]) (Arc 2596%N [(1,2)]))
 Empty) 2596%N (Test 1 (Arc 2596%N [(6,1)]) (Arc 2599%N []))
 Empty)) 2599%N (Test 2 (Arc 2599%N [(1,1)]) (Arc 2602%N []))
 (Branch (Branch (Branch Empty 2602%N (Test 1 (Arc 2602%N [(6,1);(7,1)]) (Arc 2606%N []))
 Empty) 2606%N (Test 6 (Arc 2608%N [(7,1)]) (Arc 2612%N []))
 Empty) 2608%N (Test 6 (Arc 2608%N [(1,1)]) (Arc 2602%N []))
 (Branch Empty 2612%N (Test 7 (Arc 2612%N [(2,1)]) (Arc 2616%N [(1,1)]))
 Empty)))) 2616%N (Test 2 (Arc 2618%N [(7,1)]) (Arc 2624%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2618%N (Test 6 (Arc 2616%N []) (Arc 2620%N []))
 Empty) 2620%N (Test 7 (Arc 2620%N [(6,1)]) (Arc 2616%N []))
 Empty) 2624%N (Test 7 (Arc 2624%N [(2,1)]) (Arc 2627%N []))
 (Branch (Branch Empty 2627%N (Test 1 (Arc 2627%N [(6,1);(7,1)]) (Arc 2631%N []))
 Empty) 2631%N (Test 6 (Arc 2633%N [(7,1)]) (Arc 2637%N []))
 Empty)) 2633%N (Test 6 (Arc 2633%N [(1,1)]) (Arc 2627%N []))
 (Branch (Branch (Branch Empty 2637%N (Test 7 (Arc 2637%N [(1,4)]) (Arc 2643%N []))
 Empty) 2643%N (Test 1 (Arc 2643%N [(6,1)]) (Arc 2646%N []))
 Empty) 2646%N (Test 2 (Arc 2646%N [(1,1)]) (Arc 2649%N []))
 (Branch Empty 2649%N (Test 1 (Arc 2649%N [(6,1);(7,1)]) (Arc 2653%N []))
 Empty))) 2653%N (Test 6 (Arc 2655%N [(7,1)]) (Arc 2659%N []))
 (Branch (Branch (Branch (Branch Empty 2655%N (Test 6 (Arc 2655%N [(1,1)]) (Arc 2649%N []))
 Empty) 2659%N (Test 7 (Arc 2659%N [(2,1)]) (Arc 2662%N []))
 Empty) 2662%N (Test 4 (Arc 2662%N [(1,1);(6,1)]) (Arc 2666%N []))
 (Branch (Branch Empty 2666%N (Test 6 (Arc 2666%N [(4,1)]) (Arc 2669%N []))
 Empty) 2669%N (Test 1 (Arc 2669%N [(6,1)]) (Arc 2672%N []))
 Empty)) 2672%N (Test 2 (Arc 2672%N [(1,1)]) (Arc 2675%N []))
 (Branch (Branch (Branch Empty 2675%N (Test 1 (Arc 2675%N [(6,1);(7,1)]) (Arc 2679%N []))
 Empty) 2679%N (Test 6 (Arc 2681%N [(7,1)]) (Arc 2685%N []))
 Empty) 2681%N (Test 6 (Arc 2681%N [(1,1)]) (Arc 2675%N []))
 (Branch Empty 2685%N (Test 7 (Arc 2685%N [(2,1)]) (Arc 2688%N []))
 Empty)))))) 2688%N (Test 5 (Arc 2688%N [(1,1);(6,1)]) (Arc 2692%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2692%N (Test 6 (Arc 2692%N [(5,1)]) (Arc 2695%N []))
 Empty) 2695%N (Test 2 (Arc 2697%N [(7,1)]) (Arc 2703%N []))
 Empty) 2697%N (Test 6 (Arc 2695%N []) (Arc 2699%N []))
 (Branch (Branch Empty 2699%N (Test 7 (Arc 2699%N [(6,1)]) (Arc 2695%N []))
 Empty) 2703%N (Test 7 (Arc 2703%N [(2,1)]) (Arc 2706%N []))
 Empty)) 2706%N (Test 1 (Arc 2706%N [(6,1);(7,1)]) (Arc 2710%N []))
 (Branch (Branch (Branch Empty 2710%N (Test 6 (Arc 2712%N [(7,1)]) (Arc 2716%N []))
 Empty) 2712%N (Test 6 (Arc 2712%N [(1,1)]) (Arc 2706%N []))
 Empty) 2716%N (Test 7 (Arc 2716%N [(1,4)]) (Arc 2723%N [(1,1)]))
 (Branch (Branch Empty 2723%N (Test 1 (Arc 2723%N [(6,1)]) (Arc 2726%N []))
 Empty) 2726%N (Test 2 (Arc 2726%N [(1,1)]) (Arc 2729%N []))
 Empty))) 2729%N (Test 1 (Arc 2729%N [(6,1);(7,1)]) (Arc 2733%N []))
 (Branch (Branch (Branch (Branch Empty 2733%N (Test 6 (Arc 2735%N [(7,1)]) (Arc 2739%N []))
 Empty) 2735%N (Test 6 (Arc 2735%N [(1,1)]) (Arc 2729%N []))
 Empty) 2739%N (Test 7 (Arc 2739%N [(2,1)]) (Arc 2742%N []))
 (Branch (Branch Empty 2742%N (Test 3 (Arc 2742%N [(1,1);(6,1)]) (Arc 2746%N []))
 Empty) 2746%N (Test 6 (Arc 2746%N [(3,1)]) (Arc 2749%N []))
 Empty)) 2749%N (Test 1 (Arc 2749%N [(6,1)]) (Arc 2752%N []))
 (Branch (Branch (Branch Empty 2752%N (Test 2 (Arc 2752%N [(1,1)]) (Arc 2755%N []))
 Empty) 2755%N (Test 1 (Arc 2755%N [(6,1);(7,1)]) (Arc 2759%N []))
 Empty) 2759%N (Test 6 (Arc 2761%N [(7,1)]) (Arc 2765%N []))
 (Branch Empty 2761%N (Test 6 (Arc 2761%N [(1,1)]) (Arc 2755%N []))
 Empty)))) 2765%N (Test 7 (Arc 2765%N [(2,1)]) (Arc 2768%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2768%N (Test 4 (Arc 2768%N [(1,1);(6,1)]) (Arc 2772%N []))
 Empty) 2772%N (Test 6 (Arc 2772%N [(4,1)]) (Arc 2775%N []))
 Empty) 2775%N (Test 1 (Arc 2775%N [(6,1)]) (Arc 2778%N []))
 (Branch (Branch Empty 2778%N (Test 2 (Arc 2778%N [(1,1)]) (Arc 2781%N []))
 Empty) 2781%N (Test 1 (Arc 2781%N [(6,1);(7,1)]) (Arc 2785%N []))
 Empty)) 2785%N (Test 6 (Arc 2787%N [(7,1)]) (Arc 2791%N []))
 (Branch (Branch (Branch Empty 2787%N (Test 6 (Arc 2787%N [(1,1)]) (Arc 2781%N []))
 Empty) 2791%N (Test 7 (Arc 2791%N [(2,1)]) (Arc 2794%N []))
 Empty) 2794%N (Test 5 (Arc 2794%N [(1,1);(6,1)]) (Arc 2798%N []))
 (Branch Empty 2798%N (Test 6 (Arc 2798%N [(5,1)]) (Arc 2801%N []))
 Empty))) 2801%N (Test 2 (Arc 2803%N [(7,1)]) (Arc 2809%N []))
 (Branch (Branch (Branch (Branch Empty 2803%N (Test 6 (Arc 2801%N []) (Arc 2805%N []))
 Empty) 2805%N (Test 7 (Arc 2805%N [(6,1)]) (Arc 2801%N []))
 Empty) 2809%N (Test 7 (Arc 2809%N [(2,1)]) (Arc 2812%N []))
 (Branch (Branch Empty 2812%N (Test 1 (Arc 2812%N [(6,1);(7,1)]) (Arc 2816%N []))
 Empty) 2816%N (Test 6 (Arc 2818%N [(7,1)]) (Arc 2822%N []))
 Empty)) 2818%N (Test 6 (Arc 2818%N [(1,1)]) (Arc 2812%N []))
 (Branch (Branch (Branch Empty 2822%N (Test 7 (Arc 2822%N [(1,4)]) (Arc 2829%N [(1,1)]))
 Empty) 2829%N (Test 2 (Arc 2831%N [(7,1)]) (Arc 2837%N []))
 Empty) 2831%N (Test 6 (Arc 2829%N []) (Arc 2833%N []))
 (Branch Empty 2833%N (Test 7 (Arc 2833%N [(6,1)]) (Arc 2829%N []))
 Empty))))) 2837%N (Test 7 (Arc 2837%N [(2,1)]) (Arc 2840%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2840%N (Test 1 (Arc 2840%N [(6,1);(7,1)]) (Arc 2844%N []))
 Empty) 2844%N (Test 6 (Arc 2846%N [(7,1)]) (Arc 2850%N []))
 Empty) 2846%N (Test 6 (Arc 2846%N [(1,1)]) (Arc 2840%N []))
 (Branch (Branch Empty 2850%N (Test 7 (Arc 2850%N [(1,4)]) (Arc 2858%N [(1,2)]))
 Empty) 2858%N (Test 2 (Arc 2860%N [(7,1)]) (Arc 2866%N []))
 Empty)) 2860%N (Test 6 (Arc 2858%N []) (Arc 2862%N []))
 (Branch (Branch (Branch Empty 2862%N (Test 7 (Arc 2862%N [(6,1)]) (Arc 2858%N []))
 Empty) 2866%N (Test 7 (Arc 2866%N [(2,1)]) (Arc 2869%N []))
 Empty) 2869%N (Test 1 (Arc 2869%N [(6,1);(7,1)]) (Arc 2873%N []))
 (Branch Empty 2873%N (Test 6 (Arc 2875%N [(7,1)]) (Arc 2879%N []))
 Empty))) 2875%N (Test 6 (Arc 2875%N [(1,1)]) (Arc 2869%N []))
 (Branch (Branch (Branch (Branch Empty 2879%N (Test 7 (Arc 2879%N [(1,4)]) (Arc 2885%N []))
 Empty) 2885%N (Test 1 (Arc 2885%N [(6,1)]) (Arc 2888%N []))
 Empty) 2888%N (Test 2 (Arc 2888%N [(1,1)]) (Arc 2891%N []))
 (Branch (Branch Empty 2891%N (Test 1 (Arc 2891%N [(6,1);(7,1)]) (Arc 2895%N []))
 Empty) 2895%N (Test 6 (Arc 2897%N [(7,1)]) (Arc 2901%N []))
 Empty)) 2897%N (Test 6 (Arc 2897%N [(1,1)]) (Arc 2891%N []))
 (Branch (Branch (Branch Empty 2901%N (Test 7 (Arc 2901%N [(2,1)]) (Arc 2904%N []))
 Empty) 2904%N (Test 3 (Arc 2904%N [(1,1);(6,1)]) (Arc 2908%N []))
 Empty) 2908%N (Test 6 (Arc 2908%N [(3,1)]) (Arc 2911%N []))
 (Branch Empty 2911%N (Test 1 (Arc 2911%N [(6,1)]) (Arc 2914%N []))
 Empty)))) 2914%N (Test 2 (Arc 2914%N [(1,1)]) (Arc 2917%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 2917%N (Test 1 (Arc 2917%N [(6,1);(7,1)]) (Arc 2921%N []))
 Empty) 2921%N (Test 6 (Arc 2923%N [(7,1)]) (Arc 2927%N []))
 Empty) 2923%N (Test 6 (Arc 2923%N [(1,1)]) (Arc 2917%N []))
 (Branch (Branch Empty 2927%N (Test 7 (Arc 2927%N [(2,1)]) (Arc 2930%N []))
 Empty) 2930%N (Test 5 (Arc 2930%N [(1,1);(6,1)]) (Arc 2934%N []))
 Empty)) 2934%N (Test 6 (Arc 2934%N [(5,1)]) (Arc 2937%N []))
 (Branch (Branch (Branch Empty 2937%N (Test 1 (Arc 2937%N [(6,1)]) (Arc 2940%N []))
 Empty) 2940%N (Test 2 (Arc 2940%N [(1,1)]) (Arc 2943%N []))
 Empty) 2943%N (Test 1 (Arc 2943%N [(6,1);(7,1)]) (Arc 2947%N []))
 (Branch Empty 2947%N (Test 6 (Arc 2949%N [(7,1)]) (Arc 2953%N []))
 Empty))) 2949%N (Test 6 (Arc 2949%N [(1,1)]) (Arc 2943%N []))
 (Branch (Branch (Branch (Branch Empty 2953%N (Test 7 (Arc 2953%N [(2,1)]) (Arc 2956%N []))
 Empty) 2956%N (Test 5 (Arc 2956%N [(1,1);(6,1)]) (Arc 2960%N []))
 Empty) 2960%N (Test 6 (Arc 2960%N [(5,1)]) (Arc 2963%N []))
 (Branch (Branch Empty 2963%N (Test 1 (Arc 2963%N [(6,1)]) (Arc 2966%N []))
 Empty) 2966%N (Test 2 (Arc 2966%N [(1,1)]) (Arc 2969%N []))
 Empty)) 2969%N (Test 1 (Arc 2969%N [(6,1);(7,1)]) (Arc 2973%N []))
 (Branch (Branch (Branch Empty 2973%N (Test 6 (Arc 2975%N [(7,1)]) (Arc 2979%N []))
 Empty) 2975%N (Test 6 (Arc 2975%N [(1,1)]) (Arc 2969%N []))
 Empty) 2979%N (Test 7 (Arc 2979%N [(2,1)]) (Arc 2982%N []))
 (Branch Empty 2982%N (Test 3 (Arc 2982%N [(1,1);(6,1)]) (Arc 2986%N []))
 Empty))))))) 2986%N (Test 6 (Arc 2986%N [(3,1)]) (Arc 2989%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2989%N (Test 2 (Arc 2991%N [(7,1)]) (Arc 2997%N []))
 Empty) 2991%N (Test 6 (Arc 2989%N []) (Arc 2993%N []))
 Empty) 2993%N (Test 7 (Arc 2993%N [(6,1)]) (Arc 2989%N []))
 (Branch (Branch Empty 2997%N (Test 7 (Arc 2997%N [(2,1)]) (Arc 3000%N []))
 Empty) 3000%N (Test 1 (Arc 3000%N [(6,1);(7,1)]) (Arc 3004%N []))
 Empty)) 3004%N (Test 6 (Arc 3006%N [(7,1)]) (Arc 3010%N []))
 (Branch (Branch (Branch Empty 3006%N (Test 6 (Arc 3006%N [(1,1)]) (Arc 3000%N []))
 Empty) 3010%N (Test 7 (Arc 3010%N [(1,4)]) (Arc 3017%N [(1,1)]))
 Empty) 3017%N (Test 1 (Arc 3017%N [(6,1)]) (Arc 3020%N []))
 (Branch (Branch Empty 3020%N (Test 2 (Arc 3020%N [(1,1)]) (Arc 3023%N []))
 Empty) 3023%N (Test 1 (Arc 3023%N [(6,1);(7,1)]) (Arc 3027%N []))
 Empty))) 3027%N (Test 6 (Arc 3029%N [(7,1)]) (Arc 3033%N []))
 (Branch (Branch (Branch (Branch Empty 3029%N (Test 6 (Arc 3029%N [(1,1)]) (Arc 3023%N []))
 Empty) 3033%N (Test 7 (Arc 3033%N [(2,1)]) (Arc 3036%N []))
 Empty) 3036%N (Test 4 (Arc 3036%N [(1,1);(6,1)]) (Arc 3040%N []))
 (Branch (Branch Empty 3040%N (Test 6 (Arc 3040%N [(4,1)]) (Arc 3043%N []))
 Empty) 3043%N (Test 1 (Arc 3043%N [(6,1)]) (Arc 3046%N []))
 Empty)) 3046%N (Test 2 (Arc 3046%N [(1,1)]) (Arc 3049%N []))
 (Branch (Branch (Branch Empty 3049%N (Test 1 (Arc 3049%N [(6,1);(7,1)]) (Arc 3053%N []))
 Empty) 3053%N (Test 6 (Arc 3055%N [(7,1)]) (Arc 3059%N []))
 Empty) 3055%N (Test 6 (Arc 3055%N [(1,1)]) (Arc 3049%N []))
 (Branch Empty 3059%N (Test 7 (Arc 3059%N [(2,1)]) (Arc 3062%N []))
 Empty)))) 3062%N (Test 3 (Arc 3062%N [(1,1);(6,1)]) (Arc 3066%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3066%N (Test 6 (Arc 3066%N [(3,1)]) (Arc 3069%N []))
 Empty) 3069%N (Test 1 (Arc 3069%N [(6,1)]) (Arc 3072%N []))
 Empty) 3072%N (Test 2 (Arc 3072%N [(1,1)]) (Arc 3075%N []))
 (Branch (Branch Empty 3075%N (Test 1 (Arc 3075%N [(6,1);(7,1)]) (Arc 3079%N []))
 Empty) 3079%N (Test 6 (Arc 3081%N [(7,1)]) (Arc 3085%N []))
 Empty)) 3081%N (Test 6 (Arc 3081%N [(1,1)]) (Arc 3075%N []))
 (Branch (Branch (Branch Empty 3085%N (Test 7 (Arc 3085%N [(2,1)]) (Arc 3088%N []))
 Empty) 3088%N (Test 4 (Arc 3088%N [(1,1);(6,1)]) (Arc 3092%N []))
 Empty) 3092%N (Test 6 (Arc 3092%N [(4,1)]) (Arc 3095%N []))
 (Branch Empty 3095%N (Test 1 (Arc 3095%N [(6,1)]) (Arc 3098%N []))
 Empty))) 3098%N (Test 2 (Arc 3098%N [(1,1)]) (Arc 3101%N []))
 (Branch (Branch (Branch (Branch Empty 3101%N (Test 1 (Arc 3101%N [(6,1);(7,1)]) (Arc 3105%N []))
 Empty) 3105%N (Test 6 (Arc 3107%N [(7,1)]) (Arc 3111%N []))
 Empty) 3107%N (Test 6 (Arc 3107%N [(1,1)]) (Arc 3101%N []))
 (Branch (Branch Empty 3111%N (Test 7 (Arc 3111%N [(2,1)]) (Arc 3114%N []))
 Empty) 3114%N (Test 3 (Arc 3114%N [(1,1);(6,1)]) (Arc 3118%N []))
 Empty)) 3118%N (Test 6 (Arc 3118%N [(3,1)]) (Arc 3121%N []))
 (Branch (Branch (Branch Empty 3121%N (Test 1 (Arc 3121%N [(6,1)]) (Arc 3124%N []))
 Empty) 3124%N (Test 2 (Arc 3124%N [(1,1)]) (Arc 3127%N []))
 Empty) 3127%N (Test 1 (Arc 3127%N [(6,1);(7,1)]) (Arc 3131%N []))
 (Branch Empty 3131%N (Test 6 (Arc 3133%N [(7,1)]) (Arc 3137%N []))
 Empty))))) 3133%N (Test 6 (Arc 3133%N [(1,1)]) (Arc 3127%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3137%N (Test 7 (Arc 3137%N [(2,1)]) (Arc 3140%N []))
 Empty) 3140%N (Test 3 (Arc 3140%N [(1,1);(6,1)]) (Arc 3144%N []))
 Empty) 3144%N (Test 6 (Arc 3144%N [(3,1)]) (Arc 3147%N []))
 (Branch (Branch Empty 3147%N (Test 1 (Arc 3147%N [(6,1)]) (Arc 3150%N []))
 Empty) 3150%N (Test 2 (Arc 3150%N [(1,1)]) (Arc 3153%N []))
 Empty)) 3153%N (Test 1 (Arc 3153%N [(6,1);(7,1)]) (Arc 3157%N []))
 (Branch (Branch (Branch Empty 3157%N (Test 6 (Arc 3159%N [(7,1)]) (Arc 3163%N []))
 Empty) 3159%N (Test 6 (Arc 3159%N [(1,1)]) (Arc 3153%N []))
 Empty) 3163%N (Test 7 (Arc 3163%N [(2,1)]) (Arc 3166%N []))
 (Branch Empty 3166%N (Test 4 (Arc 3166%N [(1,1);(6,1)]) (Arc 3170%N []))
 Empty))) 3170%N (Test 6 (Arc 3170%N [(4,1)]) (Arc 3173%N []))
 (Branch (Branch (Branch (Branch Empty 3173%N (Test 2 (Arc 3175%N [(7,1)]) (Arc 3181%N []))
 Empty) 3175%N (Test 6 (Arc 3173%N []) (Arc 3177%N []))
 Empty) 3177%N (Test 7 (Arc 3177%N [(6,1)]) (Arc 3173%N []))
 (Branch (Branch Empty 3181%N (Test 7 (Arc 3181%N [(2,1)]) (Arc 3184%N []))
 Empty) 3184%N (Test 1 (Arc 3184%N [(6,1);(7,1)]) (Arc 3188%N []))
 Empty)) 3188%N (Test 6 (Arc 3190%N [(7,1)]) (Arc 3194%N []))
 (Branch (Branch (Branch Empty 3190%N (Test 6 (Arc 3190%N [(1,1)]) (Arc 3184%N []))
 Empty) 3194%N (Test 7 (Arc 3194%N [(1,4)]) (Arc 3201%N [(1,1)]))
 Empty) 3201%N (Test 1 (Arc 3201%N [(6,1)]) (Arc 3204%N []))
 (Branch Empty 3204%N (Test 2 (Arc 3204%N [(1,1)]) (Arc 3207%N []))
 Empty)))) 3207%N (Test 1 (Arc 3207%N [(6,1);(7,1)]) (Arc 3211%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3211%N (Test 6 (Arc 3213%N [(7,1)]) (Arc 3217%N []))
 Empty) 3213%N (Test 6 (Arc 3213%N [(1,1)]) (Arc 3207%N []))
 Empty) 3217%N (Test 7 (Arc 3217%N [(2,1)]) (Arc 3220%N []))
 (Branch (Branch Empty 3220%N (Test 3 (Arc 3220%N [(1,1);(6,1)]) (Arc 3224%N []))
 Empty) 3224%N (Test 6 (Arc 3224%N [(3,1)]) (Arc 3227%N []))
 Empty)) 3227%N (Test 1 (Arc 3227%N [(6,1)]) (Arc 3230%N []))
 (Branch (Branch (Branch Empty 3230%N (Test 2 (Arc 3230%N [(1,1)]) (Arc 3233%N []))
 Empty) 3233%N (Test 1 (Arc 3233%N [(6,1);(7,1)]) (Arc 3237%N []))
 Empty) 3237%N (Test 6 (Arc 3239%N [(7,1)]) (Arc 3243%N []))
 (Branch Empty 3239%N (Test 6 (Arc 3239%N [(1,1)]) (Arc 3233%N []))
 Empty))) 3243%N (Test 7 (Arc 3243%N [(2,1)]) (Arc 3246%N []))
 (Branch (Branch (Branch (Branch Empty 3246%N (Test 5 (Arc 3246%N [(1,1);(6,1)]) (Arc 3250%N []))
 Empty) 3250%N (Test 6 (Arc 3250%N [(5,1)]) (Arc 3253%N []))
 Empty) 3253%N (Test 2 (Arc 3255%N [(7,1)]) (Arc 3261%N []))
 (Branch (Branch Empty 3255%N (Test 6 (Arc 3253%N []) (Arc 3257%N []))
 Empty) 3257%N (Test 7 (Arc 3257%N [(6,1)]) (Arc 3253%N []))
 Empty)) 3261%N (Test 7 (Arc 3261%N [(2,1)]) (Arc 3264%N []))
 (Branch (Branch (Branch Empty 3264%N (Test 1 (Arc 3264%N [(6,1);(7,1)]) (Arc 3268%N []))
 Empty) 3268%N (Test 6 (Arc 3270%N [(7,1)]) (Arc 3274%N []))
 Empty) 3270%N (Test 6 (Arc 3270%N [(1,1)]) (Arc 3264%N []))
 (Branch Empty 3274%N (Test 7 (Arc 3274%N [(1,4)]) (Arc 3281%N [(1,1)]))
 Empty)))))) 3281%N (Test 2 (Arc 3283%N [(7,1)]) (Arc 3289%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3283%N (Test 6 (Arc 3281%N []) (Arc 3285%N []))
 Empty) 3285%N (Test 7 (Arc 3285%N [(6,1)]) (Arc 3281%N []))
 Empty) 3289%N (Test 7 (Arc 3289%N [(2,1)]) (Arc 3292%N []))
 (Branch (Branch Empty 3292%N (Test 1 (Arc 3292%N [(6,1);(7,1)]) (Arc 3296%N []))
 Empty) 3296%N (Test 6 (Arc 3298%N [(7,1)]) (Arc 3302%N []))
 Empty)) 3298%N (Test 6 (Arc 3298%N [(1,1)]) (Arc 3292%N []))
 (Branch (Branch (Branch Empty 3302%N (Test 7 (Arc 3302%N [(1,4)]) (Arc 3308%N []))
 Empty) 3308%N (Test 2 (Arc 3310%N [(7,1)]) (Arc 3316%N []))
 Empty) 3310%N (Test 6 (Arc 3308%N []) (Arc 3312%N []))
 (Branch (Branch Empty 3312%N (Test 7 (Arc 3312%N [(6,1)]) (Arc 3308%N []))
 Empty) 3316%N (Test 7 (Arc 3316%N [(2,1)]) (Arc 3319%N []))
 Empty))) 3319%N (Test 1 (Arc 3319%N [(6,1);(7,1)]) (Arc 3323%N []))
 (Branch (Branch (Branch (Branch Empty 3323%N (Test 6 (Arc 3325%N [(7,1)]) (Arc 3329%N []))
 Empty) 3325%N (Test 6 (Arc 3325%N [(1,1)]) (Arc 3319%N []))
 Empty) 3329%N (Test 7 (Arc 3329%N [(1,4)]) (Arc 3337%N [(1,2)]))
 (Branch (Branch Empty 3337%N (Test 1 (Arc 3337%N [(6,1)]) (Arc 3340%N []))
 Empty) 3340%N (Test 2 (Arc 3340%N [(1,1)]) (Arc 3343%N []))
 Empty)) 3343%N (Test 1 (Arc 3343%N [(6,1);(7,1)]) (Arc 3347%N []))
 (Branch (Branch (Branch Empty 3347%N (Test 6 (Arc 3349%N [(7,1)]) (Arc 3353%N []))
 Empty) 3349%N (Test 6 (Arc 3349%N [(1,1)]) (Arc 3343%N []))
 Empty) 3353%N (Test 7 (Arc 3353%N [(2,1)]) (Arc 3356%N []))
 (Branch Empty 3356%N (Test 5 (Arc 3356%N [(1,1);(6,1)]) (Arc 3360%N []))
 Empty)))) 3360%N (Test 6 (Arc 3360%N [(5,1)]) (Arc 3363%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3363%N (Test 1 (Arc 3363%N [(6,1)]) (Arc 3366%N []))
 Empty) 3366%N (Test 2 (Arc 3366%N [(1,1)]) (Arc 3369%N []))
 Empty) 3369%N (Test 1 (Arc 3369%N [(6,1);(7,1)]) (Arc 3373%N []))
 (Branch (Branch Empty 3373%N (Test 6 (Arc 3375%N [(7,1)]) (Arc 3379%N []))
 Empty) 3375%N (Test 6 (Arc 3375%N [(1,1)]) (Arc 3369%N []))
 Empty)) 3379%N (Test 7 (Arc 3379%N [(2,1)]) (Arc 3382%N []))
 (Branch (Branch (Branch Empty 3382%N (Test 3 (Arc 3382%N [(1,1);(6,1)]) (Arc 3386%N []))
 Empty) 3386%N (Test 6 (Arc 3386%N [(3,1)]) (Arc 3389%N []))
 Empty) 3389%N (Test 1 (Arc 3389%N [(6,1)]) (Arc 3392%N []))
 (Branch Empty 3392%N (Test 2 (Arc 3392%N [(1,1)]) (Arc 3395%N []))
 Empty))) 3395%N (Test 1 (Arc 3395%N [(6,1);(7,1)]) (Arc 3399%N []))
 (Branch (Branch (Branch (Branch Empty 3399%N (Test 6 (Arc 3401%N [(7,1)]) (Arc 3405%N []))
 Empty) 3401%N (Test 6 (Arc 3401%N [(1,1)]) (Arc 3395%N []))
 Empty) 3405%N (Test 7 (Arc 3405%N [(2,1)]) (Arc 3408%N []))
 (Branch (Branch Empty 3408%N (Test 5 (Arc 3408%N [(1,1);(6,1)]) (Arc 3412%N []))
 Empty) 3412%N (Test 6 (Arc 3412%N [(5,1)]) (Arc 3415%N []))
 Empty)) 3415%N (Test 1 (Arc 3415%N [(6,1)]) (Arc 3418%N []))
 (Branch (Branch (Branch Empty 3418%N (Test 2 (Arc 3418%N [(1,1)]) (Arc 3421%N []))
 Empty) 3421%N (Test 1 (Arc 3421%N [(6,1);(7,1)]) (Arc 3425%N []))
 Empty) 3425%N (Test 6 (Arc 3427%N [(7,1)]) (Arc 3431%N []))
 (Branch Empty 3427%N (Test 6 (Arc 3427%N [(1,1)]) (Arc 3421%N []))
 Empty))))) 3431%N (Test 7 (Arc 3431%N [(2,1)]) (Arc 3434%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3434%N (Test 3 (Arc 3434%N [(1,1);(6,1)]) (Arc 3438%N []))
 Empty) 3438%N (Test 6 (Arc 3438%N [(3,1)]) (Arc 3441%N []))
 Empty) 3441%N (Test 1 (Arc 3441%N [(6,1)]) (Arc 3444%N []))
 (Branch (Branch Empty 3444%N (Test 2 (Arc 3444%N [(1,1)]) (Arc 3447%N []))
 Empty) 3447%N (Test 1 (Arc 3447%N [(6,1);(7,1)]) (Arc 3451%N []))
 Empty)) 3451%N (Test 6 (Arc 3453%N [(7,1)]) (Arc 3457%N []))
 (Branch (Branch (Branch Empty 3453%N (Test 6 (Arc 3453%N [(1,1)]) (Arc 3447%N []))
 Empty) 3457%N (Test 7 (Arc 3457%N [(2,1)]) (Arc 3460%N []))
 Empty) 3460%N (Test 5 (Arc 3460%N [(1,1);(6,1)]) (Arc 3464%N []))
 (Branch Empty 3464%N (Test 6 (Arc 3464%N [(5,1)]) (Arc 3467%N []))
 Empty))) 3467%N (Test 1 (Arc 3467%N [(6,1)]) (Arc 3470%N []))
 (Branch (Branch (Branch (Branch Empty 3470%N (Test 2 (Arc 3470%N [(1,1)]) (Arc 3473%N []))
 Empty) 3473%N (Test 1 (Arc 3473%N [(6,1);(7,1)]) (Arc 3477%N []))
 Empty) 3477%N (Test 6 (Arc 3479%N [(7,1)]) (Arc 3483%N []))
 (Branch (Branch Empty 3479%N (Test 6 (Arc 3479%N [(1,1)]) (Arc 3473%N []))
 Empty) 3483%N (Test 7 (Arc 3483%N [(2,1)]) (Arc 3486%N []))
 Empty)) 3486%N (Test 3 (Arc 3486%N [(1,1);(6,1)]) (Arc 3490%N []))
 (Branch (Branch (Branch Empty 3490%N (Test 6 (Arc 3490%N [(3,1)]) (Arc 3493%N []))
 Empty) 3493%N (Test 2 (Arc 3495%N [(7,1)]) (Arc 3501%N []))
 Empty) 3495%N (Test 6 (Arc 3493%N []) (Arc 3497%N []))
 (Branch Empty 3497%N (Test 7 (Arc 3497%N [(6,1)]) (Arc 3493%N []))
 Empty)))) 3501%N (Test 7 (Arc 3501%N [(2,1)]) (Arc 3504%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3504%N (Test 1 (Arc 3504%N [(6,1);(7,1)]) (Arc 3508%N []))
 Empty) 3508%N (Test 6 (Arc 3510%N [(7,1)]) (Arc 3514%N []))
 Empty) 3510%N (Test 6 (Arc 3510%N [(1,1)]) (Arc 3504%N []))
 (Branch (Branch Empty 3514%N (Test 7 (Arc 3514%N [(1,4)]) (Arc 3521%N [(1,1)]))
 Empty) 3521%N (Test 1 (Arc 3521%N [(6,1)]) (Arc 3524%N []))
 Empty)) 3524%N (Test 2 (Arc 3524%N [(1,1)]) (Arc 3527%N []))
 (Branch (Branch (Branch Empty 3527%N (Test 1 (Arc 3527%N [(6,1);(7,1)]) (Arc 3531%N []))
 Empty) 3531%N (Test 6 (Arc 3533%N [(7,1)]) (Arc 3537%N []))
 Empty) 3533%N (Test 6 (Arc 3533%N [(1,1)]) (Arc 3527%N []))
 (Branch Empty 3537%N (Test 7 (Arc 3537%N [(2,1)]) (Arc 3541%N [(1,1)]))
 Empty))) 3541%N (Test 2 (Arc 3543%N [(7,1)]) (Arc 3549%N []))
 (Branch (Branch (Branch (Branch Empty 3543%N (Test 6 (Arc 3541%N []) (Arc 3545%N []))
 Empty) 3545%N (Test 7 (Arc 3545%N [(6,1)]) (Arc 3541%N []))
 Empty) 3549%N (Test 7 (Arc 3549%N [(2,1)]) (Arc 3552%N []))
 (Branch (Branch Empty 3552%N (Test 1 (Arc 3552%N [(6,1);(7,1)]) (Arc 3556%N []))
 Empty) 3556%N (Test 6 (Arc 3558%N [(7,1)]) (Arc 3562%N []))
 Empty)) 3558%N (Test 6 (Arc 3558%N [(1,1)]) (Arc 3552%N []))
 (Branch (Branch (Branch Empty 3562%N (Test 7 (Arc 3562%N [(1,4)]) (Arc 3568%N []))
 Empty) 3568%N (Test 2 (Arc 3570%N [(7,1)]) (Arc 3576%N []))
 Empty) 3570%N (Test 6 (Arc 3568%N []) (Arc 3572%N []))
 (Branch Empty 3572%N (Test 7 (Arc 3572%N [(6,1)]) (Arc 3568%N []))
 Empty)))))))) 3576%N (Test 7 (Arc 3576%N [(2,1)]) (Arc 3579%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3579%N (Test 1 (Arc 3579%N [(6,1);(7,1)]) (Arc 3583%N []))
 Empty) 3583%N (Test 6 (Arc 3585%N [(7,1)]) (Arc 3589%N []))
 Empty) 3585%N (Test 6 (Arc 3585%N [(1,1)]) (Arc 3579%N []))
 (Branch (Branch Empty 3589%N (Test 7 (Arc 3589%N [(1,4)]) (Arc 3595%N []))
 Empty) 3595%N (Test 2 (Arc 3597%N [(7,1)]) (Arc 3603%N []))
 Empty)) 3597%N (Test 6 (Arc 3595%N []) (Arc 3599%N []))
 (Branch (Branch (Branch Empty 3599%N (Test 7 (Arc 3599%N [(6,1)]) (Arc 3595%N []))
 Empty) 3603%N (Test 7 (Arc 3603%N [(2,1)]) (Arc 3606%N []))
 Empty) 3606%N (Test 1 (Arc 3606%N [(6,1);(7,1)]) (Arc 3610%N []))
 (Branch (Branch Empty 3610%N (Test 6 (Arc 3612%N [(7,1)]) (Arc 3616%N []))
 Empty) 3612%N (Test 6 (Arc 3612%N [(1,1)]) (Arc 3606%N []))
 Empty))) 3616%N (Test 7 (Arc 3616%N [(1,4)]) (Arc 3624%N [(1,2)]))
 (Branch (Branch (Branch (Branch Empty 3624%N (Test 1 (Arc 3624%N [(6,1)]) (Arc 3627%N []))
 Empty) 3627%N (Test 2 (Arc 3627%N [(1,1)]) (Arc 3630%N []))
 Empty) 3630%N (Test 1 (Arc 3630%N [(6,1);(7,1)]) (Arc 3634%N []))
 (Branch (Branch Empty 3634%N (Test 6 (Arc 3636%N [(7,1)]) (Arc 3640%N []))
 Empty) 3636%N (Test 6 (Arc 3636%N [(1,1)]) (Arc 3630%N []))
 Empty)) 3640%N (Test 7 (Arc 3640%N [(2,1)]) (Arc 3644%N [(1,1)]))
 (Branch (Branch (Branch Empty 3644%N (Test 2 (Arc 3646%N [(7,1)]) (Arc 3652%N []))
 Empty) 3646%N (Test 6 (Arc 3644%N []) (Arc 3648%N []))
 Empty) 3648%N (Test 7 (Arc 3648%N [(6,1)]) (Arc 3644%N []))
 (Branch Empty 3652%N (Test 7 (Arc 3652%N [(2,1)]) (Arc 3655%N []))
 Empty)))) 3655%N (Test 1 (Arc 3655%N [(6,1);(7,1)]) (Arc 3659%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3659%N (Test 6 (Arc 3661%N [(7,1)]) (Arc 3665%N []))
 Empty) 3661%N (Test 6 (Arc 3661%N [(1,1)]) (Arc 3655%N []))
 Empty) 3665%N (Test 7 (Arc 3665%N [(1,4)]) (Arc 3671%N []))
 (Branch (Branch Empty 3671%N (Test 2 (Arc 3673%N [(7,1)]) (Arc 3679%N []))
 Empty) 3673%N (Test 6 (Arc 3671%N []) (Arc 3675%N []))
 Empty)) 3675%N (Test 7 (Arc 3675%N [(6,1)]) (Arc 3671%N []))
 (Branch (Branch (Branch Empty 3679%N (Test 7 (Arc 3679%N [(2,1)]) (Arc 3682%N []))
 Empty) 3682%N (Test 1 (Arc 3682%N [(6,1);(7,1)]) (Arc 3686%N []))
 Empty) 3686%N (Test 6 (Arc 3688%N [(7,1)]) (Arc 3692%N []))
 (Branch Empty 3688%N (Test 6 (Arc 3688%N [(1,1)]) (Arc 3682%N []))
 Empty))) 3692%N (Test 7 (Arc 3692%N [(1,4)]) (Arc 3698%N []))
 (Branch (Branch (Branch (Branch Empty 3698%N (Test 2 (Arc 3700%N [(7,1)]) (Arc 3706%N []))
 Empty) 3700%N (Test 6 (Arc 3698%N []) (Arc 3702%N []))
 Empty) 3702%N (Test 7 (Arc 3702%N [(6,1)]) (Arc 3698%N []))
 (Branch (Branch Empty 3706%N (Test 7 (Arc 3706%N [(2,1)]) (Arc 3709%N []))
 Empty) 3709%N (Test 1 (Arc 3709%N [(6,1);(7,1)]) (Arc 3713%N []))
 Empty)) 3713%N (Test 6 (Arc 3715%N [(7,1)]) (Arc 3719%N []))
 (Branch (Branch (Branch Empty 3715%N (Test 6 (Arc 3715%N [(1,1)]) (Arc 3709%N []))
 Empty) 3719%N (Test 7 (Arc 3719%N [(1,4)]) (Arc 3727%N [(1,2)]))
 Empty) 3727%N (Test 2 (Arc 3729%N [(7,1)]) (Arc 3735%N []))
 (Branch Empty 3729%N (Test 6 (Arc 3727%N []) (Arc 3731%N []))
 Empty))))) 3731%N (Test 7 (Arc 3731%N [(6,1)]) (Arc 3727%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3735%N (Test 7 (Arc 3735%N [(2,1)]) (Arc 3738%N []))
 Empty) 3738%N (Test 1 (Arc 3738%N [(6,1);(7,1)]) (Arc 3742%N []))
 Empty) 3742%N (Test 6 (Arc 3744%N [(7,1)]) (Arc 3748%N []))
 (Branch (Branch Empty 3744%N (Test 6 (Arc 3744%N [(1,1)]) (Arc 3738%N []))
 Empty) 3748%N (Test 7 (Arc 3748%N [(1,4)]) (Arc 3754%N []))
 Empty)) 3754%N (Test 2 (Arc 3756%N [(7,1)]) (Arc 3762%N []))
 (Branch (Branch (Branch Empty 3756%N (Test 6 (Arc 3754%N []) (Arc 3758%N []))
 Empty) 3758%N (Test 7 (Arc 3758%N [(6,1)]) (Arc 3754%N []))
 Empty) 3762%N (Test 7 (Arc 3762%N [(2,1)]) (Arc 3765%N []))
 (Branch Empty 3765%N (Test 1 (Arc 3765%N [(6,1);(7,1)]) (Arc 3769%N []))
 Empty))) 3769%N (Test 6 (Arc 3771%N [(7,1)]) (Arc 3775%N []))
 (Branch (Branch (Branch (Branch Empty 3771%N (Test 6 (Arc 3771%N [(1,1)]) (Arc 3765%N []))
 Empty) 3775%N (Test 7 (Arc 3775%N [(1,4)]) (Arc 3783%N [(1,2)]))
 Empty) 3783%N (Test 1 (Arc 3783%N [(6,1)]) (Arc 3786%N []))
 (Branch (Branch Empty 3786%N (Test 2 (Arc 3786%N [(1,1)]) (Arc 3789%N []))
 Empty) 3789%N (Test 1 (Arc 3789%N [(6,1);(7,1)]) (Arc 3793%N []))
 Empty)) 3793%N (Test 6 (Arc 3795%N [(7,1)]) (Arc 3799%N []))
 (Branch (Branch (Branch Empty 3795%N (Test 6 (Arc 3795%N [(1,1)]) (Arc 3789%N []))
 Empty) 3799%N (Test 7 (Arc 3799%N [(2,1)]) (Arc 3803%N [(1,1)]))
 Empty) 3803%N (Test 2 (Arc 3805%N [(7,1)]) (Arc 3811%N []))
 (Branch Empty 3805%N (Test 6 (Arc 3803%N []) (Arc 3807%N []))
 Empty)))) 3807%N (Test 7 (Arc 3807%N [(6,1)]) (Arc 3803%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3811%N (Test 7 (Arc 3811%N [(2,1)]) (Arc 3814%N []))
 Empty) 3814%N (Test 1 (Arc 3814%N [(6,1);(7,1)]) (Arc 3818%N []))
 Empty) 3818%N (Test 6 (Arc 3820%N [(7,1)]) (Arc 3824%N []))
 (Branch (Branch Empty 3820%N (Test 6 (Arc 3820%N [(1,1)]) (Arc 3814%N []))
 Empty) 3824%N (Test 7 (Arc 3824%N [(1,4)]) (Arc 3830%N []))
 Empty)) 3830%N (Test 2 (Arc 3832%N [(7,1)]) (Arc 3838%N []))
 (Branch (Branch (Branch Empty 3832%N (Test 6 (Arc 3830%N []) (Arc 3834%N []))
 Empty) 3834%N (Test 7 (Arc 3834%N [(6,1)]) (Arc 3830%N []))
 Empty) 3838%N (Test 7 (Arc 3838%N [(2,1)]) (Arc 3841%N []))
 (Branch Empty 3841%N (Test 1 (Arc 3841%N [(6,1);(7,1)]) (Arc 3845%N []))
 Empty))) 3845%N (Test 6 (Arc 3847%N [(7,1)]) (Arc 3851%N []))
 (Branch (Branch (Branch (Branch Empty 3847%N (Test 6 (Arc 3847%N [(1,1)]) (Arc 3841%N []))
 Empty) 3851%N (Test 7 (Arc 3851%N [(1,4)]) (Arc 3857%N []))
 Empty) 3857%N (Test 2 (Arc 3859%N [(7,1)]) (Arc 3865%N []))
 (Branch (Branch Empty 3859%N (Test 6 (Arc 3857%N []) (Arc 3861%N []))
 Empty) 3861%N (Test 7 (Arc 3861%N [(6,1)]) (Arc 3857%N []))
 Empty)) 3865%N (Test 7 (Arc 3865%N [(2,1)]) (Arc 3868%N []))
 (Branch (Branch (Branch Empty 3868%N (Test 1 (Arc 3868%N [(6,1);(7,1)]) (Arc 3872%N []))
 Empty) 3872%N (Test 6 (Arc 3874%N [(7,1)]) (Arc 3878%N []))
 Empty) 3874%N (Test 6 (Arc 3874%N [(1,1)]) (Arc 3868%N []))
 (Branch Empty 3878%N (Test 7 (Arc 3878%N [(1,4)]) (Arc 3886%N [(1,2)]))
 Empty)))))) 3886%N (Test 1 (Arc 3886%N [(6,1)]) (Arc 3889%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3889%N (Test 2 (Arc 3889%N [(1,1)]) (Arc 3892%N []))
 Empty) 3892%N (Test 1 (Arc 3892%N [(6,1);(7,1)]) (Arc 3896%N []))
 Empty) 3896%N (Test 6 (Arc 3898%N [(7,1)]) (Arc 3902%N []))
 (Branch (Branch Empty 3898%N (Test 6 (Arc 3898%N [(1,1)]) (Arc 3892%N []))
 Empty) 3902%N (Test 7 (Arc 3902%N [(2,1)]) (Arc 3906%N [(1,1)]))
 Empty)) 3906%N (Test 2 (Arc 3908%N [(7,1)]) (Arc 3914%N []))
 (Branch (Branch (Branch Empty 3908%N (Test 6 (Arc 3906%N []) (Arc 3910%N []))
 Empty) 3910%N (Test 7 (Arc 3910%N [(6,1)]) (Arc 3906%N []))
 Empty) 3914%N (Test 7 (Arc 3914%N [(2,1)]) (Arc 3917%N []))
 (Branch (Branch Empty 3917%N (Test 1 (Arc 3917%N [(6,1);(7,1)]) (Arc 3921%N []))
 Empty) 3921%N (Test 6 (Arc 3923%N [(7,1)]) (Arc 3927%N []))
 Empty))) 3923%N (Test 6 (Arc 3923%N [(1,1)]) (Arc 3917%N []))
 (Branch (Branch (Branch (Branch Empty 3927%N (Test 7 (Arc 3927%N [(1,4)]) (Arc 3933%N []))
 Empty) 3933%N (Test 2 (Arc 3935%N [(7,1)]) (Arc 3941%N []))
 Empty) 3935%N (Test 6 (Arc 3933%N []) (Arc 3937%N []))
 (Branch (Branch Empty 3937%N (Test 7 (Arc 3937%N [(6,1)]) (Arc 3933%N []))
 Empty) 3941%N (Test 7 (Arc 3941%N [(2,1)]) (Arc 3944%N []))
 Empty)) 3944%N (Test 1 (Arc 3944%N [(6,1);(7,1)]) (Arc 3948%N []))
 (Branch (Branch (Branch Empty 3948%N (Test 6 (Arc 3950%N [(7,1)]) (Arc 3954%N []))
 Empty) 3950%N (Test 6 (Arc 3950%N [(1,1)]) (Arc 3944%N []))
 Empty) 3954%N (Test 7 (Arc 3954%N [(1,4)]) (Arc 3960%N []))
 (Branch Empty 3960%N (Test 2 (Arc 3962%N [(7,1)]) (Arc 3968%N []))
 Empty)))) 3962%N (Test 6 (Arc 3960%N []) (Arc 3964%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 3964%N (Test 7 (Arc 3964%N [(6,1)]) (Arc 3960%N []))
 Empty) 3968%N (Test 7 (Arc 3968%N [(2,1)]) (Arc 3971%N []))
 Empty) 3971%N (Test 1 (Arc 3971%N [(6,1);(7,1)]) (Arc 3975%N []))
 (Branch (Branch Empty 3975%N (Test 6 (Arc 3977%N [(7,1)]) (Arc 3981%N []))
 Empty) 3977%N (Test 6 (Arc 3977%N [(1,1)]) (Arc 3971%N []))
 Empty)) 3981%N (Test 7 (Arc 3981%N [(1,4)]) (Arc 3989%N [(1,2)]))
 (Branch (Branch (Branch Empty 3989%N (Test 1 (Arc 3989%N [(6,1)]) (Arc 3992%N []))
 Empty) 3992%N (Test 2 (Arc 3992%N [(1,1)]) (Arc 3995%N []))
 Empty) 3995%N (Test 1 (Arc 3995%N [(6,1);(7,1)]) (Arc 3999%N []))
 (Branch Empty 3999%N (Test 6 (Arc 4001%N [(7,1)]) (Arc 4005%N []))
 Empty))) 4001%N (Test 6 (Arc 4001%N [(1,1)]) (Arc 3995%N []))
 (Branch (Branch (Branch (Branch Empty 4005%N (Test 7 (Arc 4005%N [(2,1)]) (Arc 4008%N []))
 Empty) 4008%N (Test 5 (Arc 4008%N [(1,1);(6,1)]) (Arc 4012%N []))
 Empty) 4012%N (Test 6 (Arc 4012%N [(5,1)]) (Arc 4015%N []))
 (Branch (Branch Empty 4015%N (Test 1 (Arc 4015%N [(6,1)]) (Arc 4018%N []))
 Empty) 4018%N (Test 2 (Arc 4018%N [(1,1)]) (Arc 4021%N []))
 Empty)) 4021%N (Test 1 (Arc 4021%N [(6,1);(7,1)]) (Arc 4025%N []))
 (Branch (Branch (Branch Empty 4025%N (Test 6 (Arc 4027%N [(7,1)]) (Arc 4031%N []))
 Empty) 4027%N (Test 6 (Arc 4027%N [(1,1)]) (Arc 4021%N []))
 Empty) 4031%N (Test 7 (Arc 4031%N [(2,1)]) (Arc 4034%N []))
 (Branch Empty 4034%N (Test 3 (Arc 4034%N [(1,1);(6,1)]) (Arc 4038%N []))
 Empty))))) 4038%N (Test 6 (Arc 4038%N [(3,1)]) (Arc 4041%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4041%N (Test 1 (Arc 4041%N [(6,1)]) (Arc 4044%N []))
 Empty) 4044%N (Test 2 (Arc 4044%N [(1,1)]) (Arc 4047%N []))
 Empty) 4047%N (Test 1 (Arc 4047%N [(6,1);(7,1)]) (Arc 4051%N []))
 (Branch (Branch Empty 4051%N (Test 6 (Arc 4053%N [(7,1)]) (Arc 4057%N []))
 Empty) 4053%N (Test 6 (Arc 4053%N [(1,1)]) (Arc 4047%N []))
 Empty)) 4057%N (Test 7 (Arc 4057%N [(2,1)]) (Arc 4060%N []))
 (Branch (Branch (Branch Empty 4060%N (Test 5 (Arc 4060%N [(1,1);(6,1)]) (Arc 4064%N []))
 Empty) 4064%N (Test 6 (Arc 4064%N [(5,1)]) (Arc 4067%N []))
 Empty) 4067%N (Test 1 (Arc 4067%N [(6,1)]) (Arc 4070%N []))
 (Branch Empty 4070%N (Test 2 (Arc 4070%N [(1,1)]) (Arc 4073%N []))
 Empty))) 4073%N (Test 1 (Arc 4073%N [(6,1);(7,1)]) (Arc 4077%N []))
 (Branch (Branch (Branch (Branch Empty 4077%N (Test 6 (Arc 4079%N [(7,1)]) (Arc 4083%N []))
 Empty) 4079%N (Test 6 (Arc 4079%N [(1,1)]) (Arc 4073%N []))
 Empty) 4083%N (Test 7 (Arc 4083%N [(2,1)]) (Arc 4086%N []))
 (Branch (Branch Empty 4086%N (Test 3 (Arc 4086%N [(1,1);(6,1)]) (Arc 4090%N []))
 Empty) 4090%N (Test 6 (Arc 4090%N [(3,1)]) (Arc 4093%N []))
 Empty)) 4093%N (Test 1 (Arc 4093%N [(6,1)]) (Arc 4096%N []))
 (Branch (Branch (Branch Empty 4096%N (Test 2 (Arc 4096%N [(1,1)]) (Arc 4099%N []))
 Empty) 4099%N (Test 1 (Arc 4099%N [(6,1);(7,1)]) (Arc 4103%N []))
 Empty) 4103%N (Test 6 (Arc 4105%N [(7,1)]) (Arc 4109%N []))
 (Branch Empty 4105%N (Test 6 (Arc 4105%N [(1,1)]) (Arc 4099%N []))
 Empty)))) 4109%N (Test 7 (Arc 4109%N [(2,1)]) (Arc 4112%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 4112%N (Test 5 (Arc 4112%N [(1,1);(6,1)]) (Arc 4116%N []))
 Empty) 4116%N (Test 6 (Arc 4116%N [(5,1)]) (Arc 4119%N []))
 Empty) 4119%N (Test 1 (Arc 4119%N [(6,1)]) (Arc 4122%N []))
 (Branch (Branch Empty 4122%N (Test 2 (Arc 4122%N [(1,1)]) (Arc 4125%N []))
 Empty) 4125%N (Test 1 (Arc 4125%N [(6,1);(7,1)]) (Arc 4129%N []))
 Empty)) 4129%N (Test 6 (Arc 4131%N [(7,1)]) (Arc 4135%N []))
 (Branch (Branch (Branch Empty 4131%N (Test 6 (Arc 4131%N [(1,1)]) (Arc 4125%N []))
 Empty) 4135%N (Test 7 (Arc 4135%N [(2,1)]) (Arc 4138%N []))
 Empty) 4138%N (Test 3 (Arc 4138%N [(1,1);(6,1)]) (Arc 4142%N []))
 (Branch Empty 4142%N (Test 6 (Arc 4142%N [(3,1)]) (Arc 4145%N []))
 Empty))) 4145%N (Test 2 (Arc 4147%N [(7,1)]) (Arc 4153%N []))
 (Branch (Branch (Branch (Branch Empty 4147%N (Test 6 (Arc 4145%N []) (Arc 4149%N []))
 Empty) 4149%N (Test 7 (Arc 4149%N [(6,1)]) (Arc 4145%N []))
 Empty) 4153%N (Test 7 (Arc 4153%N [(2,1)]) (Arc 4156%N []))
 (Branch (Branch Empty 4156%N (Test 1 (Arc 4156%N [(6,1);(7,1)]) (Arc 4160%N []))
 Empty) 4160%N (Test 6 (Arc 4162%N [(7,1)]) (Arc 4166%N []))
 Empty)) 4162%N (Test 6 (Arc 4162%N [(1,1)]) (Arc 4156%N []))
 (Branch (Branch (Branch Empty 4166%N (Test 7 (Arc 4166%N [(1,4)]) (Arc 4173%N [(1,1)]))
 Empty) 4173%N (Test 1 (Arc 4173%N [(6,1)]) (Arc 4176%N []))
 Empty) 4176%N (Test 2 (Arc 4176%N [(1,1)]) (Arc 4179%N []))
 (Branch Empty 4179%N (Test 1 (Arc 4179%N [(6,1);(7,1)]) (Arc 4183%N []))
 Empty))))))) 4183%N (Test 6 (Arc 4185%N [(7,1)]) (Arc 4189%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4185%N (Test 6 (Arc 4185%N [(1,1)]) (Arc 4179%N []))
 Empty) 4189%N (Test 7 (Arc 4189%N [(2,1)]) (Arc 4193%N [(1,1)]))
 Empty) 4193%N (Test 2 (Arc 4195%N [(7,1)]) (Arc 4201%N []))
 (Branch (Branch Empty 4195%N (Test 6 (Arc 4193%N []) (Arc 4197%N []))
 Empty) 4197%N (Test 7 (Arc 4197%N [(6,1)]) (Arc 4193%N []))
 Empty)) 4201%N (Test 7 (Arc 4201%N [(2,1)]) (Arc 4204%N []))
 (Branch (Branch (Branch Empty 4204%N (Test 1 (Arc 4204%N [(6,1);(7,1)]) (Arc 4208%N []))
 Empty) 4208%N (Test 6 (Arc 4210%N [(7,1)]) (Arc 4214%N []))
 Empty) 4210%N (Test 6 (Arc 4210%N [(1,1)]) (Arc 4204%N []))
 (Branch (Branch Empty 4214%N (Test 7 (Arc 4214%N [(1,4)]) (Arc 4220%N []))
 Empty) 4220%N (Test 2 (Arc 4222%N [(7,1)]) (Arc 4228%N []))
 Empty))) 4222%N (Test 6 (Arc 4220%N []) (Arc 4224%N []))
 (Branch (Branch (Branch (Branch Empty 4224%N (Test 7 (Arc 4224%N [(6,1)]) (Arc 4220%N []))
 Empty) 4228%N (Test 7 (Arc 4228%N [(2,1)]) (Arc 4231%N []))
 Empty) 4231%N (Test 1 (Arc 4231%N [(6,1);(7,1)]) (Arc 4235%N []))
 (Branch (Branch Empty 4235%N (Test 6 (Arc 4237%N [(7,1)]) (Arc 4241%N []))
 Empty) 4237%N (Test 6 (Arc 4237%N [(1,1)]) (Arc 4231%N []))
 Empty)) 4241%N (Test 7 (Arc 4241%N [(1,4)]) (Arc 4247%N []))
 (Branch (Branch (Branch Empty 4247%N (Test 2 (Arc 4249%N [(7,1)]) (Arc 4255%N []))
 Empty) 4249%N (Test 6 (Arc 4247%N []) (Arc 4251%N []))
 Empty) 4251%N (Test 7 (Arc 4251%N [(6,1)]) (Arc 4247%N []))
 (Branch Empty 4255%N (Test 7 (Arc 4255%N [(2,1)]) (Arc 4258%N []))
 Empty)))) 4258%N (Test 1 (Arc 4258%N [(6,1);(7,1)]) (Arc 4262%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 4262%N (Test 6 (Arc 4264%N [(7,1)]) (Arc 4268%N []))
 Empty) 4264%N (Test 6 (Arc 4264%N [(1,1)]) (Arc 4258%N []))
 Empty) 4268%N (Test 7 (Arc 4268%N [(1,4)]) (Arc 4276%N [(1,2)]))
 (Branch (Branch Empty 4276%N (Test 1 (Arc 4276%N [(6,1)]) (Arc 4279%N []))
 Empty) 4279%N (Test 2 (Arc 4279%N [(1,1)]) (Arc 4282%N []))
 Empty)) 4282%N (Test 1 (Arc 4282%N [(6,1);(7,1)]) (Arc 4286%N []))
 (Branch (Branch (Branch Empty 4286%N (Test 6 (Arc 4288%N [(7,1)]) (Arc 4292%N []))
 Empty) 4288%N (Test 6 (Arc 4288%N [(1,1)]) (Arc 4282%N []))
 Empty) 4292%N (Test 7 (Arc 4292%N [(2,1)]) (Arc 4296%N [(1,1)]))
 (Branch Empty 4296%N (Test 2 (Arc 4298%N [(7,1)]) (Arc 4304%N []))
 Empty))) 4298%N (Test 6 (Arc 4296%N []) (Arc 4300%N []))
 (Branch (Branch (Branch (Branch Empty 4300%N (Test 7 (Arc 4300%N [(6,1)]) (Arc 4296%N []))
 Empty) 4304%N (Test 7 (Arc 4304%N [(2,1)]) (Arc 4307%N []))
 Empty) 4307%N (Test 1 (Arc 4307%N [(6,1);(7,1)]) (Arc 4311%N []))
 (Branch (Branch Empty 4311%N (Test 6 (Arc 4313%N [(7,1)]) (Arc 4317%N []))
 Empty) 4313%N (Test 6 (Arc 4313%N [(1,1)]) (Arc 4307%N []))
 Empty)) 4317%N (Test 7 (Arc 4317%N [(1,4)]) (Arc 4323%N []))
 (Branch (Branch (Branch Empty 4323%N (Test 2 (Arc 4325%N [(7,1)]) (Arc 4331%N []))
 Empty) 4325%N (Test 6 (Arc 4323%N []) (Arc 4327%N []))
 Empty) 4327%N (Test 7 (Arc 4327%N [(6,1)]) (Arc 4323%N []))
 (Branch Empty 4331%N (Test 7 (Arc 4331%N [(2,1)]) (Arc 4334%N []))
 Empty))))) 4334%N (Test 1 (Arc 4334%N [(6,1);(7,1)]) (Arc 4338%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4338%N (Test 6 (Arc 4340%N [(7,1)]) (Arc 4344%N []))
 Empty) 4340%N (Test 6 (Arc 4340%N [(1,1)]) (Arc 4334%N []))
 Empty) 4344%N (Test 7 (Arc 4344%N [(1,4)]) (Arc 4350%N []))
 (Branch (Branch Empty 4350%N (Test 2 (Arc 4352%N [(7,1)]) (Arc 4358%N []))
 Empty) 4352%N (Test 6 (Arc 4350%N []) (Arc 4354%N []))
 Empty)) 4354%N (Test 7 (Arc 4354%N [(6,1)]) (Arc 4350%N []))
 (Branch (Branch (Branch Empty 4358%N (Test 7 (Arc 4358%N [(2,1)]) (Arc 4361%N []))
 Empty) 4361%N (Test 1 (Arc 4361%N [(6,1);(7,1)]) (Arc 4365%N []))
 Empty) 4365%N (Test 6 (Arc 4367%N [(7,1)]) (Arc 4371%N []))
 (Branch Empty 4367%N (Test 6 (Arc 4367%N [(1,1)]) (Arc 4361%N []))
 Empty))) 4371%N (Test 7 (Arc 4371%N [(1,4)]) (Arc 4379%N [(1,2)]))
 (Branch (Branch (Branch (Branch Empty 4379%N (Test 1 (Arc 4379%N [(6,1)]) (Arc 4382%N []))
 Empty) 4382%N (Test 2 (Arc 4382%N [(1,1)]) (Arc 4385%N []))
 Empty) 4385%N (Test 1 (Arc 4385%N [(6,1);(7,1)]) (Arc 4389%N []))
 (Branch (Branch Empty 4389%N (Test 6 (Arc 4391%N [(7,1)]) (Arc 4395%N []))
 Empty) 4391%N (Test 6 (Arc 4391%N [(1,1)]) (Arc 4385%N []))
 Empty)) 4395%N (Test 7 (Arc 4395%N [(2,1)]) (Arc 4399%N [(1,1)]))
 (Branch (Branch (Branch Empty 4399%N (Test 2 (Arc 4401%N [(7,1)]) (Arc 4407%N []))
 Empty) 4401%N (Test 6 (Arc 4399%N []) (Arc 4403%N []))
 Empty) 4403%N (Test 7 (Arc 4403%N [(6,1)]) (Arc 4399%N []))
 (Branch Empty 4407%N (Test 7 (Arc 4407%N [(2,1)]) (Arc 4410%N []))
 Empty)))) 4410%N (Test 1 (Arc 4410%N [(6,1);(7,1)]) (Arc 4414%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 4414%N (Test 6 (Arc 4416%N [(7,1)]) (Arc 4420%N []))
 Empty) 4416%N (Test 6 (Arc 4416%N [(1,1)]) (Arc 4410%N []))
 Empty) 4420%N (Test 7 (Arc 4420%N [(1,4)]) (Arc 4426%N []))
 (Branch (Branch Empty 4426%N (Test 2 (Arc 4428%N [(7,1)]) (Arc 4434%N []))
 Empty) 4428%N (Test 6 (Arc 4426%N []) (Arc 4430%N []))
 Empty)) 4430%N (Test 7 (Arc 4430%N [(6,1)]) (Arc 4426%N []))
 (Branch (Branch (Branch Empty 4434%N (Test 7 (Arc 4434%N [(2,1)]) (Arc 4437%N []))
 Empty) 4437%N (Test 1 (Arc 4437%N [(6,1);(7,1)]) (Arc 4441%N []))
 Empty) 4441%N (Test 6 (Arc 4443%N [(7,1)]) (Arc 4447%N []))
 (Branch Empty 4443%N (Test 6 (Arc 4443%N [(1,1)]) (Arc 4437%N []))
 Empty))) 4447%N (Test 7 (Arc 4447%N [(1,4)]) (Arc 4453%N []))
 (Branch (Branch (Branch (Branch Empty 4453%N (Test 2 (Arc 4455%N [(7,1)]) (Arc 4461%N []))
 Empty) 4455%N (Test 6 (Arc 4453%N []) (Arc 4457%N []))
 Empty) 4457%N (Test 7 (Arc 4457%N [(6,1)]) (Arc 4453%N []))
 (Branch (Branch Empty 4461%N (Test 7 (Arc 4461%N [(2,1)]) (Arc 4464%N []))
 Empty) 4464%N (Test 1 (Arc 4464%N [(6,1);(7,1)]) (Arc 4468%N []))
 Empty)) 4468%N (Test 6 (Arc 4470%N [(7,1)]) (Arc 4474%N []))
 (Branch (Branch (Branch Empty 4470%N (Test 6 (Arc 4470%N [(1,1)]) (Arc 4464%N []))
 Empty) 4474%N (Test 7 (Arc 4474%N [(1,4)]) (Arc 4482%N [(1,2)]))
 Empty) 4482%N (Test 2 (Arc 4484%N [(7,1)]) (Arc 4490%N []))
 (Branch Empty 4484%N (Test 6 (Arc 4482%N []) (Arc 4486%N []))
 Empty)))))) 4486%N (Test 7 (Arc 4486%N [(6,1)]) (Arc 4482%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4490%N (Test 7 (Arc 4490%N [(2,1)]) (Arc 4493%N []))
 Empty) 4493%N (Test 1 (Arc 4493%N [(6,1);(7,1)]) (Arc 4497%N []))
 Empty) 4497%N (Test 6 (Arc 4499%N [(7,1)]) (Arc 4503%N []))
 (Branch (Branch Empty 4499%N (Test 6 (Arc 4499%N [(1,1)]) (Arc 4493%N []))
 Empty) 4503%N (Test 7 (Arc 4503%N [(1,4)]) (Arc 4509%N []))
 Empty)) 4509%N (Test 1 (Arc 4509%N [(6,1)]) (Arc 4512%N []))
 (Branch (Branch (Branch Empty 4512%N (Test 2 (Arc 4512%N [(1,1)]) (Arc 4515%N []))
 Empty) 4515%N (Test 1 (Arc 4515%N [(6,1);(7,1)]) (Arc 4519%N []))
 Empty) 4519%N (Test 6 (Arc 4521%N [(7,1)]) (Arc 4525%N []))
 (Branch (Branch Empty 4521%N (Test 6 (Arc 4521%N [(1,1)]) (Arc 4515%N []))
 Empty) 4525%N (Test 7 (Arc 4525%N [(2,1)]) (Arc 4529%N [(1,1)]))
 Empty))) 4529%N (Test 2 (Arc 4531%N [(7,1)]) (Arc 4537%N []))
 (Branch (Branch (Branch (Branch Empty 4531%N (Test 6 (Arc 4529%N []) (Arc 4533%N []))
 Empty) 4533%N (Test 7 (Arc 4533%N [(6,1)]) (Arc 4529%N []))
 Empty) 4537%N (Test 7 (Arc 4537%N [(2,1)]) (Arc 4540%N []))
 (Branch (Branch Empty 4540%N (Test 1 (Arc 4540%N [(6,1);(7,1)]) (Arc 4544%N []))
 Empty) 4544%N (Test 6 (Arc 4546%N [(7,1)]) (Arc 4550%N []))
 Empty)) 4546%N (Test 6 (Arc 4546%N [(1,1)]) (Arc 4540%N []))
 (Branch (Branch (Branch Empty 4550%N (Test 7 (Arc 4550%N [(1,4)]) (Arc 4556%N []))
 Empty) 4556%N (Test 3 (Arc 4556%N [(6,1);(7,1)]) (Arc 4560%N []))
 Empty) 4560%N (Test 5 (Arc 4561%N []) (Arc 4564%N []))
 (Branch Empty 4561%N (Test 6 (Arc 4560%N []) (Arc 4565%N []))
 Empty)))) 4564%N (Test 6 (Arc 4565%N []) (Arc 4570%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 4565%N (Test 5 (Arc 4565%N []) (Arc 4567%N []))
 Empty) 4567%N (Test 6 (Arc 4565%N []) (Arc 4572%N []))
 Empty) 4570%N (Test 1 (Arc 4570%N []) (Arc 4572%N []))
 (Branch (Branch Empty 4572%N (Test 7 (Arc 4572%N [(6,1)]) (Arc 4575%N []))
 Empty) 4575%N (Test 4 (Arc 4575%N [(5,1)]) (Arc 4578%N []))
 Empty)) 4578%N (Test 5 (Arc 4579%N []) (Arc 4582%N []))
 (Branch (Branch (Branch Empty 4579%N (Test 6 (Arc 4578%N []) (Arc 4583%N []))
 Empty) 4582%N (Test 6 (Arc 4583%N []) (Arc 4588%N []))
 Empty) 4583%N (Test 5 (Arc 4583%N []) (Arc 4585%N []))
 (Branch Empty 4585%N (Test 6 (Arc 4583%N []) (Arc 0%N []))
 Empty))) 4588%N (Test 1 (Arc 4588%N []) (Arc 0%N []))
 (Branch (Branch (Branch (Branch Empty 4591%N (Test 8 (Arc 4593%N [(7,1)]) (Arc 4599%N []))
 Empty) 4593%N (Test 6 (Arc 4591%N []) (Arc 4595%N []))
 Empty) 4595%N (Test 7 (Arc 4595%N [(6,1)]) (Arc 4591%N []))
 (Branch (Branch Empty 4599%N (Test 7 (Arc 4599%N [(8,1)]) (Arc 4602%N []))
 Empty) 4602%N (Test 6 (Arc 4602%N [(4,1)]) (Arc 4605%N []))
 Empty)) 4605%N (Test 1 (Arc 4605%N [(6,1)]) (Arc 4608%N []))
 (Branch (Branch (Branch Empty 4608%N (Test 2 (Arc 4608%N [(1,1)]) (Arc 4611%N []))
 Empty) 4611%N (Test 1 (Arc 4611%N [(6,1);(7,1)]) (Arc 4615%N []))
 Empty) 4615%N (Test 6 (Arc 4617%N [(7,1)]) (Arc 4621%N []))
 (Branch Empty 4617%N (Test 6 (Arc 4617%N [(1,1)]) (Arc 4611%N []))
 Empty))))) 4621%N (Test 7 (Arc 4621%N [(2,1)]) (Arc 4624%N []))
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4624%N (Test 4 (Arc 4624%N [(1,1);(6,1)]) (Arc 4628%N []))
 Empty) 4628%N (Test 6 (Arc 4628%N [(4,1)]) (Arc 4631%N []))
 Empty) 4631%N (Test 2 (Arc 4633%N [(7,1)]) (Arc 4639%N []))
 (Branch (Branch Empty 4633%N (Test 6 (Arc 4631%N []) (Arc 4635%N []))
 Empty) 4635%N (Test 7 (Arc 4635%N [(6,1)]) (Arc 4631%N []))
 Empty)) 4639%N (Test 7 (Arc 4639%N [(2,1)]) (Arc 4642%N []))
 (Branch (Branch (Branch Empty 4642%N (Test 1 (Arc 4642%N [(6,1);(7,1)]) (Arc 4646%N []))
 Empty) 4646%N (Test 6 (Arc 4648%N [(7,1)]) (Arc 4652%N []))
 Empty) 4648%N (Test 6 (Arc 4648%N [(1,1)]) (Arc 4642%N []))
 (Branch Empty 4652%N (Test 7 (Arc 4652%N [(1,4)]) (Arc 4658%N []))
 Empty))) 4658%N (Test 1 (Arc 4658%N [(6,1)]) (Arc 4661%N []))
 (Branch (Branch (Branch (Branch Empty 4661%N (Test 5 (Arc 4662%N []) (Arc 4665%N []))
 Empty) 4662%N (Test 6 (Arc 4661%N []) (Arc 4666%N []))
 Empty) 4665%N (Test 6 (Arc 4666%N []) (Arc 4671%N []))
 (Branch (Branch Empty 4666%N (Test 5 (Arc 4666%N []) (Arc 4668%N []))
 Empty) 4668%N (Test 6 (Arc 4666%N []) (Arc 0%N []))
 Empty)) 4671%N (Test 1 (Arc 4671%N [(6,1)]) (Arc 4674%N []))
 (Branch (Branch (Branch Empty 4674%N (Test 2 (Arc 4674%N [(1,1)]) (Arc 4677%N []))
 Empty) 4677%N (Test 1 (Arc 4677%N [(6,1);(7,1)]) (Arc 4681%N []))
 Empty) 4681%N (Test 6 (Arc 4683%N [(7,1)]) (Arc 4687%N []))
 (Branch Empty 4683%N (Test 6 (Arc 4683%N [(1,1)]) (Arc 4677%N []))
 Empty)))) 4687%N (Test 7 (Arc 4687%N [(2,1)]) (Arc 4690%N []))
 (Branch (Branch (Branch (Branch (Branch Empty 4690%N (Test 4 (Arc 4690%N [(1,1);(6,1)]) (Arc 4694%N []))
 Empty) 4694%N (Test 6 (Arc 4694%N [(4,1)]) (Arc 0%N []))
 Empty) 4698%N (Test 1 (Arc 4698%N [(6,1)]) (Arc 4701%N []))
 (Branch (Branch Empty 4701%N (Test 2 (Arc 4701%N [(1,1)]) (Arc 4704%N []))
 Empty) 4704%N (Test 1 (Arc 4704%N [(6,1);(7,1)]) (Arc 4708%N []))
 Empty)) 4708%N (Test 6 (Arc 4710%N [(7,1)]) (Arc 4714%N []))
 (Branch (Branch (Branch Empty 4710%N (Test 6 (Arc 4710%N [(1,1)]) (Arc 4704%N []))
 Empty) 4714%N (Test 7 (Arc 4714%N [(2,1)]) (Arc 4717%N []))
 Empty) 4717%N (Test 5 (Arc 4717%N [(1,1);(6,1)]) (Arc 4721%N []))
 (Branch Empty 4721%N (Test 6 (Arc 4721%N [(5,1)]) (Arc 0%N []))
 Empty))) 4726%N (Test 5 (Arc 4727%N []) (Arc 4730%N []))
 (Branch (Branch (Branch (Branch Empty 4727%N (Test 6 (Arc 4726%N []) (Arc 4731%N []))
 Empty) 4730%N (Test 6 (Arc 4731%N []) (Arc 4736%N []))
 Empty) 4731%N (Test 5 (Arc 4731%N []) (Arc 4733%N []))
 (Branch (Branch Empty 4733%N (Test 6 (Arc 4731%N []) (Arc 4737%N []))
 Empty) 4736%N Halt
 Empty)) 4737%N (Test 2 (Arc 4739%N [(7,1)]) (Arc 4745%N []))
 (Branch (Branch (Branch Empty 4739%N (Test 6 (Arc 4737%N []) (Arc 4741%N []))
 Empty) 4741%N (Test 7 (Arc 4741%N [(6,1)]) (Arc 4737%N []))
 Empty) 4745%N (Test 7 (Arc 4745%N [(2,1)]) (Arc 4748%N []))
 (Branch Empty 4748%N (Test 6 (Arc 4748%N [(5,1)]) (Arc 0%N []))
 Empty)))))))))).

Definition k215 : graph := lookup k215_tree.
Definition vertices : list N := map fst (elements k215_tree).
Definition drains : list N := filter (drainb k215) vertices.
Definition core : list N := filter (fun v => negb (drainb k215 v)) vertices.

Definition rank_tree : tree nat :=
(Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2%N 2
 Empty) 7%N 1
 Empty) 13%N 1
 (Branch Empty 17%N 2
 Empty)) 20%N 1
 (Branch (Branch Empty 26%N 3
 Empty) 29%N 2
 (Branch Empty 32%N 1
 Empty))) 38%N 2
 (Branch (Branch (Branch Empty 42%N 6
 Empty) 45%N 5
 (Branch Empty 49%N 4
 Empty)) 52%N 3
 (Branch (Branch Empty 55%N 2
 Empty) 58%N 1
 (Branch Empty 64%N 2
 Empty)))) 68%N 3
 (Branch (Branch (Branch (Branch (Branch Empty 71%N 2
 Empty) 75%N 1
 Empty) 82%N 1
 (Branch Empty 86%N 2
 Empty)) 89%N 1
 (Branch (Branch Empty 95%N 2
 Empty) 99%N 4
 (Branch Empty 107%N 3
 Empty))) 110%N 2
 (Branch (Branch (Branch Empty 113%N 1
 Empty) 119%N 2
 (Branch Empty 123%N 6
 Empty)) 126%N 5
 (Branch (Branch Empty 130%N 4
 Empty) 133%N 3
 (Branch Empty 136%N 2
 Empty))))) 139%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 145%N 2
 Empty) 149%N 3
 Empty) 152%N 2
 (Branch Empty 156%N 1
 Empty)) 163%N 1
 (Branch (Branch Empty 167%N 2
 Empty) 170%N 1
 (Branch Empty 177%N 1
 Empty))) 181%N 2
 (Branch (Branch (Branch Empty 184%N 1
 Empty) 190%N 2
 (Branch Empty 194%N 1
 Empty)) 204%N 1
 (Branch (Branch Empty 208%N 5
 Empty) 211%N 4
 (Branch Empty 214%N 3
 Empty)))) 217%N 2
 (Branch (Branch (Branch (Branch Empty 220%N 1
 Empty) 226%N 2
 (Branch Empty 230%N 3
 Empty)) 233%N 2
 (Branch (Branch Empty 237%N 1
 Empty) 244%N 1
 (Branch Empty 248%N 2
 Empty))) 251%N 1
 (Branch (Branch (Branch Empty 257%N 2
 Empty) 261%N 4
 (Branch Empty 267%N 3
 Empty)) 270%N 2
 (Branch (Branch Empty 273%N 1
 Empty) 279%N 2
 (Branch Empty 283%N 6
 Empty)))))) 286%N 5
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 290%N 4
 Empty) 293%N 3
 Empty) 296%N 2
 (Branch Empty 299%N 1
 Empty)) 305%N 2
 (Branch (Branch Empty 309%N 3
 Empty) 312%N 2
 (Branch Empty 316%N 1
 Empty))) 323%N 1
 (Branch (Branch (Branch Empty 327%N 2
 Empty) 330%N 1
 (Branch Empty 336%N 2
 Empty)) 340%N 4
 (Branch (Branch Empty 346%N 3
 Empty) 349%N 2
 (Branch Empty 352%N 1
 Empty)))) 358%N 2
 (Branch (Branch (Branch (Branch Empty 362%N 6
 Empty) 365%N 5
 (Branch Empty 369%N 4
 Empty)) 372%N 3
 (Branch (Branch Empty 375%N 2
 Empty) 378%N 1
 (Branch Empty 384%N 2
 Empty))) 388%N 3
 (Branch (Branch (Branch Empty 391%N 2
 Empty) 395%N 1
 (Branch Empty 402%N 1
 Empty)) 406%N 2
 (Branch (Branch Empty 409%N 1
 Empty) 415%N 2
 (Branch Empty 419%N 1
 Empty))))) 429%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 433%N 2
 Empty) 436%N 1
 Empty) 442%N 2
 (Branch Empty 446%N 1
 Empty)) 456%N 1
 (Branch (Branch Empty 460%N 2
 Empty) 463%N 1
 (Branch Empty 469%N 2
 Empty))) 473%N 4
 (Branch (Branch (Branch Empty 479%N 3
 Empty) 482%N 2
 (Branch Empty 485%N 1
 Empty)) 491%N 2
 (Branch (Branch Empty 495%N 6
 Empty) 498%N 5
 (Branch Empty 502%N 4
 Empty)))) 505%N 3
 (Branch (Branch (Branch (Branch Empty 508%N 2
 Empty) 511%N 1
 (Branch Empty 517%N 2
 Empty)) 521%N 3
 (Branch (Branch Empty 524%N 2
 Empty) 528%N 1
 (Branch Empty 535%N 1
 Empty))) 539%N 2
 (Branch (Branch (Branch Empty 542%N 1
 Empty) 548%N 2
 (Branch Empty 552%N 4
 Empty)) 561%N 3
 (Branch (Branch Empty 564%N 2
 Empty) 567%N 1
 (Branch Empty 573%N 2
 Empty))))))) 577%N 6
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 580%N 5
 Empty) 584%N 4
 Empty) 587%N 3
 (Branch Empty 590%N 2
 Empty)) 593%N 1
 (Branch (Branch Empty 599%N 2
 Empty) 603%N 3
 (Branch Empty 606%N 2
 Empty))) 610%N 1
 (Branch (Branch (Branch Empty 617%N 1
 Empty) 621%N 2
 (Branch Empty 624%N 1
 Empty)) 630%N 2
 (Branch (Branch Empty 634%N 4
 Empty) 643%N 3
 (Branch Empty 646%N 2
 Empty)))) 649%N 1
 (Branch (Branch (Branch (Branch Empty 655%N 2
 Empty) 659%N 6
 (Branch Empty 662%N 5
 Empty)) 666%N 4
 (Branch (Branch Empty 669%N 3
 Empty) 672%N 2
 (Branch Empty 675%N 1
 Empty))) 681%N 2
 (Branch (Branch (Branch Empty 685%N 3
 Empty) 688%N 2
 (Branch Empty 692%N 1
 Empty)) 699%N 1
 (Branch (Branch Empty 703%N 2
 Empty) 706%N 1
 (Branch Empty 712%N 2
 Empty))))) 716%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 723%N 3
 Empty) 726%N 2
 Empty) 729%N 1
 (Branch Empty 735%N 2
 Empty)) 739%N 6
 (Branch (Branch Empty 742%N 5
 Empty) 746%N 4
 (Branch Empty 749%N 3
 Empty))) 752%N 2
 (Branch (Branch (Branch Empty 755%N 1
 Empty) 761%N 2
 (Branch Empty 765%N 3
 Empty)) 768%N 2
 (Branch (Branch Empty 772%N 1
 Empty) 779%N 1
 (Branch Empty 783%N 2
 Empty)))) 786%N 1
 (Branch (Branch (Branch (Branch Empty 792%N 2
 Empty) 796%N 1
 (Branch Empty 809%N 1
 Empty)) 813%N 2
 (Branch (Branch Empty 816%N 1
 Empty) 822%N 2
 (Branch Empty 826%N 1
 Empty))) 838%N 1
 (Branch (Branch (Branch Empty 842%N 2
 Empty) 845%N 1
 (Branch Empty 851%N 2
 Empty)) 855%N 1
 (Branch (Branch Empty 865%N 1
 Empty) 869%N 2
 (Branch Empty 872%N 1
 Empty)))))) 878%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 882%N 4
 Empty) 888%N 3
 Empty) 891%N 2
 (Branch Empty 894%N 1
 Empty)) 900%N 2
 (Branch (Branch Empty 904%N 6
 Empty) 907%N 5
 (Branch Empty 911%N 4
 Empty))) 914%N 3
 (Branch (Branch (Branch Empty 917%N 2
 Empty) 920%N 1
 (Branch Empty 926%N 2
 Empty)) 930%N 6
 (Branch (Branch Empty 933%N 5
 Empty) 937%N 4
 (Branch Empty 940%N 3
 Empty)))) 943%N 2
 (Branch (Branch (Branch (Branch Empty 946%N 1
 Empty) 952%N 2
 (Branch Empty 956%N 3
 Empty)) 959%N 2
 (Branch (Branch Empty 963%N 1
 Empty) 970%N 1
 (Branch Empty 974%N 2
 Empty))) 977%N 1
 (Branch (Branch (Branch Empty 983%N 2
 Empty) 987%N 4
 (Branch Empty 995%N 3
 Empty)) 998%N 2
 (Branch (Branch Empty 1001%N 1
 Empty) 1007%N 2
 (Branch Empty 1011%N 1
 Empty))))) 1019%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1023%N 2
 Empty) 1026%N 1
 Empty) 1032%N 2
 (Branch Empty 1036%N 1
 Empty)) 1046%N 1
 (Branch (Branch Empty 1050%N 2
 Empty) 1053%N 1
 (Branch Empty 1059%N 2
 Empty))) 1063%N 4
 (Branch (Branch (Branch Empty 1071%N 3
 Empty) 1074%N 2
 (Branch Empty 1077%N 1
 Empty)) 1083%N 2
 (Branch (Branch Empty 1087%N 1
 Empty) 1095%N 1
 (Branch Empty 1099%N 2
 Empty)))) 1102%N 1
 (Branch (Branch (Branch (Branch Empty 1108%N 2
 Empty) 1112%N 4
 (Branch Empty 1118%N 3
 Empty)) 1121%N 2
 (Branch (Branch Empty 1124%N 1
 Empty) 1130%N 2
 (Branch Empty 1134%N 3
 Empty))) 1137%N 2
 (Branch (Branch (Branch Empty 1141%N 1
 Empty) 1148%N 1
 (Branch Empty 1152%N 2
 Empty)) 1155%N 1
 (Branch (Branch Empty 1161%N 2
 Empty) 1165%N 4
 (Branch Empty 1171%N 3
 Empty)))))))) 1174%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1177%N 1
 Empty) 1183%N 2
 Empty) 1187%N 6
 (Branch Empty 1190%N 5
 Empty)) 1194%N 4
 (Branch (Branch Empty 1197%N 3
 Empty) 1200%N 2
 (Branch Empty 1203%N 1
 Empty))) 1209%N 2
 (Branch (Branch (Branch Empty 1213%N 3
 Empty) 1216%N 2
 (Branch Empty 1220%N 1
 Empty)) 1227%N 1
 (Branch (Branch Empty 1231%N 2
 Empty) 1234%N 1
 (Branch Empty 1240%N 2
 Empty)))) 1244%N 4
 (Branch (Branch (Branch (Branch (Branch Empty 1253%N 3
 Empty) 1256%N 2
 Empty) 1259%N 1
 (Branch Empty 1265%N 2
 Empty)) 1269%N 6
 (Branch (Branch Empty 1272%N 5
 Empty) 1276%N 4
 (Branch Empty 1279%N 3
 Empty))) 1282%N 2
 (Branch (Branch (Branch Empty 1285%N 1
 Empty) 1291%N 2
 (Branch Empty 1295%N 3
 Empty)) 1298%N 2
 (Branch (Branch Empty 1302%N 1
 Empty) 1309%N 1
 (Branch Empty 1313%N 2
 Empty))))) 1316%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1322%N 2
 Empty) 1326%N 4
 Empty) 1333%N 3
 (Branch Empty 1336%N 2
 Empty)) 1339%N 1
 (Branch (Branch Empty 1345%N 2
 Empty) 1349%N 6
 (Branch Empty 1352%N 5
 Empty))) 1356%N 4
 (Branch (Branch (Branch Empty 1359%N 3
 Empty) 1362%N 2
 (Branch Empty 1365%N 1
 Empty)) 1371%N 2
 (Branch (Branch Empty 1375%N 3
 Empty) 1378%N 2
 (Branch Empty 1382%N 1
 Empty)))) 1389%N 1
 (Branch (Branch (Branch (Branch Empty 1393%N 2
 Empty) 1396%N 1
 (Branch Empty 1402%N 2
 Empty)) 1406%N 1
 (Branch (Branch Empty 1417%N 1
 Empty) 1421%N 2
 (Branch Empty 1424%N 1
 Empty))) 1430%N 2
 (Branch (Branch (Branch Empty 1434%N 1
 Empty) 1444%N 1
 (Branch Empty 1448%N 2
 Empty)) 1451%N 1
 (Branch (Branch Empty 1457%N 2
 Empty) 1461%N 4
 (Branch Empty 1467%N 3
 Empty)))))) 1470%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1473%N 1
 Empty) 1479%N 2
 Empty) 1483%N 6
 (Branch Empty 1486%N 5
 Empty)) 1490%N 4
 (Branch (Branch Empty 1493%N 3
 Empty) 1496%N 2
 (Branch Empty 1499%N 1
 Empty))) 1505%N 2
 (Branch (Branch (Branch Empty 1509%N 6
 Empty) 1512%N 5
 (Branch Empty 1516%N 4
 Empty)) 1519%N 3
 (Branch (Branch Empty 1522%N 2
 Empty) 1525%N 1
 (Branch Empty 1531%N 2
 Empty)))) 1535%N 3
 (Branch (Branch (Branch (Branch Empty 1538%N 2
 Empty) 1542%N 1
 (Branch Empty 1549%N 1
 Empty)) 1553%N 2
 (Branch (Branch Empty 1556%N 1
 Empty) 1562%N 2
 (Branch Empty 1566%N 1
 Empty))) 1578%N 1
 (Branch (Branch (Branch Empty 1582%N 2
 Empty) 1585%N 1
 (Branch Empty 1591%N 2
 Empty)) 1595%N 4
 (Branch (Branch Empty 1603%N 3
 Empty) 1606%N 2
 (Branch Empty 1609%N 1
 Empty))))) 1615%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1619%N 6
 Empty) 1622%N 5
 Empty) 1626%N 4
 (Branch Empty 1629%N 3
 Empty)) 1632%N 2
 (Branch (Branch Empty 1635%N 1
 Empty) 1641%N 2
 (Branch Empty 1645%N 6
 Empty))) 1648%N 5
 (Branch (Branch (Branch Empty 1652%N 4
 Empty) 1655%N 3
 (Branch Empty 1658%N 2
 Empty)) 1661%N 1
 (Branch (Branch Empty 1667%N 2
 Empty) 1671%N 3
 (Branch Empty 1674%N 2
 Empty)))) 1678%N 1
 (Branch (Branch (Branch (Branch Empty 1685%N 1
 Empty) 1689%N 2
 (Branch Empty 1692%N 1
 Empty)) 1698%N 2
 (Branch (Branch Empty 1702%N 1
 Empty) 1714%N 1
 (Branch Empty 1718%N 2
 Empty))) 1721%N 1
 (Branch (Branch (Branch Empty 1727%N 2
 Empty) 1731%N 1
 (Branch Empty 1743%N 1
 Empty)) 1747%N 2
 (Branch (Branch Empty 1750%N 1
 Empty) 1756%N 2
 (Branch Empty 1760%N 4
 Empty))))))) 1766%N 3
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1769%N 2
 Empty) 1772%N 1
 Empty) 1778%N 2
 (Branch Empty 1782%N 6
 Empty)) 1785%N 5
 (Branch (Branch Empty 1789%N 4
 Empty) 1792%N 3
 (Branch Empty 1795%N 2
 Empty))) 1798%N 1
 (Branch (Branch (Branch Empty 1804%N 2
 Empty) 1808%N 3
 (Branch Empty 1811%N 2
 Empty)) 1815%N 1
 (Branch (Branch Empty 1822%N 1
 Empty) 1826%N 2
 (Branch Empty 1829%N 1
 Empty)))) 1835%N 2
 (Branch (Branch (Branch (Branch Empty 1839%N 4
 Empty) 1848%N 3
 (Branch Empty 1851%N 2
 Empty)) 1854%N 1
 (Branch (Branch Empty 1860%N 2
 Empty) 1864%N 6
 (Branch Empty 1867%N 5
 Empty))) 1871%N 4
 (Branch (Branch (Branch Empty 1874%N 3
 Empty) 1877%N 2
 (Branch Empty 1880%N 1
 Empty)) 1886%N 2
 (Branch (Branch Empty 1890%N 3
 Empty) 1893%N 2
 (Branch Empty 1897%N 1
 Empty))))) 1904%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1908%N 2
 Empty) 1911%N 1
 Empty) 1917%N 2
 (Branch Empty 1921%N 4
 Empty)) 1928%N 3
 (Branch (Branch Empty 1931%N 2
 Empty) 1934%N 1
 (Branch Empty 1940%N 2
 Empty))) 1944%N 6
 (Branch (Branch (Branch Empty 1947%N 5
 Empty) 1951%N 4
 (Branch Empty 1954%N 3
 Empty)) 1957%N 2
 (Branch (Branch Empty 1960%N 1
 Empty) 1966%N 2
 (Branch Empty 1970%N 3
 Empty)))) 1973%N 2
 (Branch (Branch (Branch (Branch Empty 1977%N 1
 Empty) 1984%N 1
 (Branch Empty 1988%N 2
 Empty)) 1991%N 1
 (Branch (Branch Empty 1997%N 2
 Empty) 2001%N 1
 (Branch Empty 2012%N 1
 Empty))) 2016%N 2
 (Branch (Branch (Branch Empty 2019%N 1
 Empty) 2025%N 2
 (Branch Empty 2029%N 1
 Empty)) 2039%N 1
 (Branch (Branch Empty 2043%N 2
 Empty) 2046%N 1
 (Branch Empty 2052%N 2
 Empty)))))) 2056%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2062%N 3
 Empty) 2065%N 2
 Empty) 2068%N 1
 (Branch Empty 2074%N 2
 Empty)) 2078%N 6
 (Branch (Branch Empty 2081%N 5
 Empty) 2085%N 4
 (Branch Empty 2088%N 3
 Empty))) 2091%N 2
 (Branch (Branch (Branch Empty 2094%N 1
 Empty) 2100%N 2
 (Branch Empty 2104%N 6
 Empty)) 2107%N 5
 (Branch (Branch Empty 2111%N 4
 Empty) 2114%N 3
 (Branch Empty 2117%N 2
 Empty)))) 2120%N 1
 (Branch (Branch (Branch (Branch Empty 2126%N 2
 Empty) 2130%N 3
 (Branch Empty 2133%N 2
 Empty)) 2137%N 1
 (Branch (Branch Empty 2144%N 1
 Empty) 2148%N 2
 (Branch Empty 2151%N 1
 Empty))) 2157%N 2
 (Branch (Branch (Branch Empty 2161%N 1
 Empty) 2171%N 1
 (Branch Empty 2175%N 2
 Empty)) 2178%N 1
 (Branch (Branch Empty 2184%N 2
 Empty) 2188%N 4
 (Branch Empty 2196%N 3
 Empty))))) 2199%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2202%N 1
 Empty) 2208%N 2
 Empty) 2212%N 6
 (Branch Empty 2215%N 5
 Empty)) 2219%N 4
 (Branch (Branch Empty 2222%N 3
 Empty) 2225%N 2
 (Branch Empty 2228%N 1
 Empty))) 2234%N 2
 (Branch (Branch (Branch Empty 2238%N 3
 Empty) 2241%N 2
 (Branch Empty 2245%N 1
 Empty)) 2252%N 1
 (Branch (Branch Empty 2256%N 2
 Empty) 2259%N 1
 (Branch Empty 2265%N 2
 Empty)))) 2269%N 4
 (Branch (Branch (Branch (Branch Empty 2277%N 3
 Empty) 2280%N 2
 (Branch Empty 2283%N 1
 Empty)) 2289%N 2
 (Branch (Branch Empty 2293%N 6
 Empty) 2296%N 5
 (Branch Empty 2300%N 4
 Empty))) 2303%N 3
 (Branch (Branch (Branch Empty 2306%N 2
 Empty) 2309%N 1
 (Branch Empty 2315%N 2
 Empty)) 2319%N 3
 (Branch (Branch Empty 2322%N 2
 Empty) 2326%N 1
 (Branch Empty 2333%N 1
 Empty))))))))) 2337%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2340%N 1
 Empty) 2346%N 2
 Empty) 2350%N 1
 (Branch Empty 2362%N 1
 Empty)) 2366%N 2
 (Branch (Branch Empty 2369%N 1
 Empty) 2375%N 2
 (Branch Empty 2379%N 1
 Empty))) 2389%N 1
 (Branch (Branch (Branch Empty 2393%N 2
 Empty) 2396%N 1
 (Branch Empty 2402%N 2
 Empty)) 2406%N 4
 (Branch (Branch Empty 2412%N 3
 Empty) 2415%N 2
 (Branch Empty 2418%N 1
 Empty)))) 2424%N 2
 (Branch (Branch (Branch (Branch (Branch Empty 2428%N 6
 Empty) 2431%N 5
 Empty) 2435%N 4
 (Branch Empty 2438%N 3
 Empty)) 2441%N 2
 (Branch (Branch Empty 2444%N 1
 Empty) 2450%N 2
 (Branch Empty 2454%N 6
 Empty))) 2457%N 5
 (Branch (Branch (Branch Empty 2461%N 4
 Empty) 2464%N 3
 (Branch Empty 2467%N 2
 Empty)) 2470%N 1
 (Branch (Branch Empty 2476%N 2
 Empty) 2480%N 3
 (Branch Empty 2483%N 2
 Empty))))) 2487%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2494%N 1
 Empty) 2498%N 2
 Empty) 2501%N 1
 (Branch Empty 2507%N 2
 Empty)) 2511%N 4
 (Branch (Branch Empty 2520%N 3
 Empty) 2523%N 2
 (Branch Empty 2526%N 1
 Empty))) 2532%N 2
 (Branch (Branch (Branch Empty 2536%N 1
 Empty) 2544%N 1
 (Branch Empty 2548%N 2
 Empty)) 2551%N 1
 (Branch (Branch Empty 2557%N 2
 Empty) 2561%N 1
 (Branch Empty 2571%N 1
 Empty)))) 2575%N 2
 (Branch (Branch (Branch (Branch Empty 2578%N 1
 Empty) 2584%N 2
 (Branch Empty 2588%N 4
 Empty)) 2596%N 3
 (Branch (Branch Empty 2599%N 2
 Empty) 2602%N 1
 (Branch Empty 2608%N 2
 Empty))) 2612%N 1
 (Branch (Branch (Branch Empty 2620%N 1
 Empty) 2624%N 2
 (Branch Empty 2627%N 1
 Empty)) 2633%N 2
 (Branch (Branch Empty 2637%N 4
 Empty) 2643%N 3
 (Branch Empty 2646%N 2
 Empty)))))) 2649%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2655%N 2
 Empty) 2659%N 6
 Empty) 2662%N 5
 (Branch Empty 2666%N 4
 Empty)) 2669%N 3
 (Branch (Branch Empty 2672%N 2
 Empty) 2675%N 1
 (Branch Empty 2681%N 2
 Empty))) 2685%N 3
 (Branch (Branch (Branch Empty 2688%N 2
 Empty) 2692%N 1
 (Branch Empty 2699%N 1
 Empty)) 2703%N 2
 (Branch (Branch Empty 2706%N 1
 Empty) 2712%N 2
 (Branch Empty 2716%N 4
 Empty)))) 2723%N 3
 (Branch (Branch (Branch (Branch Empty 2726%N 2
 Empty) 2729%N 1
 (Branch Empty 2735%N 2
 Empty)) 2739%N 6
 (Branch (Branch Empty 2742%N 5
 Empty) 2746%N 4
 (Branch Empty 2749%N 3
 Empty))) 2752%N 2
 (Branch (Branch (Branch Empty 2755%N 1
 Empty) 2761%N 2
 (Branch Empty 2765%N 6
 Empty)) 2768%N 5
 (Branch (Branch Empty 2772%N 4
 Empty) 2775%N 3
 (Branch Empty 2778%N 2
 Empty))))) 2781%N 1
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2787%N 2
 Empty) 2791%N 3
 Empty) 2794%N 2
 (Branch Empty 2798%N 1
 Empty)) 2805%N 1
 (Branch (Branch Empty 2809%N 2
 Empty) 2812%N 1
 (Branch Empty 2818%N 2
 Empty))) 2822%N 1
 (Branch (Branch (Branch Empty 2833%N 1
 Empty) 2837%N 2
 (Branch Empty 2840%N 1
 Empty)) 2846%N 2
 (Branch (Branch Empty 2850%N 1
 Empty) 2862%N 1
 (Branch Empty 2866%N 2
 Empty)))) 2869%N 1
 (Branch (Branch (Branch (Branch Empty 2875%N 2
 Empty) 2879%N 4
 (Branch Empty 2885%N 3
 Empty)) 2888%N 2
 (Branch (Branch Empty 2891%N 1
 Empty) 2897%N 2
 (Branch Empty 2901%N 6
 Empty))) 2904%N 5
 (Branch (Branch (Branch Empty 2908%N 4
 Empty) 2911%N 3
 (Branch Empty 2914%N 2
 Empty)) 2917%N 1
 (Branch (Branch Empty 2923%N 2
 Empty) 2927%N 6
 (Branch Empty 2930%N 5
 Empty))))))) 2934%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2937%N 3
 Empty) 2940%N 2
 Empty) 2943%N 1
 (Branch Empty 2949%N 2
 Empty)) 2953%N 6
 (Branch (Branch Empty 2956%N 5
 Empty) 2960%N 4
 (Branch Empty 2963%N 3
 Empty))) 2966%N 2
 (Branch (Branch (Branch Empty 2969%N 1
 Empty) 2975%N 2
 (Branch Empty 2979%N 3
 Empty)) 2982%N 2
 (Branch (Branch Empty 2986%N 1
 Empty) 2993%N 1
 (Branch Empty 2997%N 2
 Empty)))) 3000%N 1
 (Branch (Branch (Branch (Branch Empty 3006%N 2
 Empty) 3010%N 4
 (Branch Empty 3017%N 3
 Empty)) 3020%N 2
 (Branch (Branch Empty 3023%N 1
 Empty) 3029%N 2
 (Branch Empty 3033%N 6
 Empty))) 3036%N 5
 (Branch (Branch (Branch Empty 3040%N 4
 Empty) 3043%N 3
 (Branch Empty 3046%N 2
 Empty)) 3049%N 1
 (Branch (Branch Empty 3055%N 2
 Empty) 3059%N 6
 (Branch Empty 3062%N 5
 Empty))))) 3066%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3069%N 3
 Empty) 3072%N 2
 Empty) 3075%N 1
 (Branch Empty 3081%N 2
 Empty)) 3085%N 6
 (Branch (Branch Empty 3088%N 5
 Empty) 3092%N 4
 (Branch Empty 3095%N 3
 Empty))) 3098%N 2
 (Branch (Branch (Branch Empty 3101%N 1
 Empty) 3107%N 2
 (Branch Empty 3111%N 6
 Empty)) 3114%N 5
 (Branch (Branch Empty 3118%N 4
 Empty) 3121%N 3
 (Branch Empty 3124%N 2
 Empty)))) 3127%N 1
 (Branch (Branch (Branch (Branch Empty 3133%N 2
 Empty) 3137%N 6
 (Branch Empty 3140%N 5
 Empty)) 3144%N 4
 (Branch (Branch Empty 3147%N 3
 Empty) 3150%N 2
 (Branch Empty 3153%N 1
 Empty))) 3159%N 2
 (Branch (Branch (Branch Empty 3163%N 3
 Empty) 3166%N 2
 (Branch Empty 3170%N 1
 Empty)) 3177%N 1
 (Branch (Branch Empty 3181%N 2
 Empty) 3184%N 1
 (Branch Empty 3190%N 2
 Empty)))))) 3194%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3201%N 3
 Empty) 3204%N 2
 Empty) 3207%N 1
 (Branch Empty 3213%N 2
 Empty)) 3217%N 6
 (Branch (Branch Empty 3220%N 5
 Empty) 3224%N 4
 (Branch Empty 3227%N 3
 Empty))) 3230%N 2
 (Branch (Branch (Branch Empty 3233%N 1
 Empty) 3239%N 2
 (Branch Empty 3243%N 3
 Empty)) 3246%N 2
 (Branch (Branch Empty 3250%N 1
 Empty) 3257%N 1
 (Branch Empty 3261%N 2
 Empty)))) 3264%N 1
 (Branch (Branch (Branch (Branch Empty 3270%N 2
 Empty) 3274%N 1
 (Branch Empty 3285%N 1
 Empty)) 3289%N 2
 (Branch (Branch Empty 3292%N 1
 Empty) 3298%N 2
 (Branch Empty 3302%N 1
 Empty))) 3312%N 1
 (Branch (Branch (Branch Empty 3316%N 2
 Empty) 3319%N 1
 (Branch Empty 3325%N 2
 Empty)) 3329%N 4
 (Branch (Branch Empty 3337%N 3
 Empty) 3340%N 2
 (Branch Empty 3343%N 1
 Empty))))) 3349%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3353%N 6
 Empty) 3356%N 5
 Empty) 3360%N 4
 (Branch Empty 3363%N 3
 Empty)) 3366%N 2
 (Branch (Branch Empty 3369%N 1
 Empty) 3375%N 2
 (Branch Empty 3379%N 6
 Empty))) 3382%N 5
 (Branch (Branch (Branch Empty 3386%N 4
 Empty) 3389%N 3
 (Branch Empty 3392%N 2
 Empty)) 3395%N 1
 (Branch (Branch Empty 3401%N 2
 Empty) 3405%N 6
 (Branch Empty 3408%N 5
 Empty)))) 3412%N 4
 (Branch (Branch (Branch (Branch Empty 3415%N 3
 Empty) 3418%N 2
 (Branch Empty 3421%N 1
 Empty)) 3427%N 2
 (Branch (Branch Empty 3431%N 6
 Empty) 3434%N 5
 (Branch Empty 3438%N 4
 Empty))) 3441%N 3
 (Branch (Branch (Branch Empty 3444%N 2
 Empty) 3447%N 1
 (Branch Empty 3453%N 2
 Empty)) 3457%N 6
 (Branch (Branch Empty 3460%N 5
 Empty) 3464%N 4
 (Branch Empty 3467%N 3
 Empty)))))))) 3470%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3473%N 1
 Empty) 3479%N 2
 Empty) 3483%N 3
 (Branch Empty 3486%N 2
 Empty)) 3490%N 1
 (Branch (Branch Empty 3497%N 1
 Empty) 3501%N 2
 (Branch Empty 3504%N 1
 Empty))) 3510%N 2
 (Branch (Branch (Branch Empty 3514%N 4
 Empty) 3521%N 3
 (Branch Empty 3524%N 2
 Empty)) 3527%N 1
 (Branch (Branch Empty 3533%N 2
 Empty) 3537%N 1
 (Branch Empty 3545%N 1
 Empty)))) 3549%N 2
 (Branch (Branch (Branch (Branch (Branch Empty 3552%N 1
 Empty) 3558%N 2
 Empty) 3562%N 1
 (Branch Empty 3572%N 1
 Empty)) 3576%N 2
 (Branch (Branch Empty 3579%N 1
 Empty) 3585%N 2
 (Branch Empty 3589%N 1
 Empty))) 3599%N 1
 (Branch (Branch (Branch Empty 3603%N 2
 Empty) 3606%N 1
 (Branch Empty 3612%N 2
 Empty)) 3616%N 4
 (Branch (Branch Empty 3624%N 3
 Empty) 3627%N 2
 (Branch Empty 3630%N 1
 Empty))))) 3636%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3640%N 1
 Empty) 3648%N 1
 Empty) 3652%N 2
 (Branch Empty 3655%N 1
 Empty)) 3661%N 2
 (Branch (Branch Empty 3665%N 1
 Empty) 3675%N 1
 (Branch Empty 3679%N 2
 Empty))) 3682%N 1
 (Branch (Branch (Branch Empty 3688%N 2
 Empty) 3692%N 1
 (Branch Empty 3702%N 1
 Empty)) 3706%N 2
 (Branch (Branch Empty 3709%N 1
 Empty) 3715%N 2
 (Branch Empty 3719%N 1
 Empty)))) 3731%N 1
 (Branch (Branch (Branch (Branch Empty 3735%N 2
 Empty) 3738%N 1
 (Branch Empty 3744%N 2
 Empty)) 3748%N 1
 (Branch (Branch Empty 3758%N 1
 Empty) 3762%N 2
 (Branch Empty 3765%N 1
 Empty))) 3771%N 2
 (Branch (Branch (Branch Empty 3775%N 4
 Empty) 3783%N 3
 (Branch Empty 3786%N 2
 Empty)) 3789%N 1
 (Branch (Branch Empty 3795%N 2
 Empty) 3799%N 1
 (Branch Empty 3807%N 1
 Empty)))))) 3811%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3814%N 1
 Empty) 3820%N 2
 Empty) 3824%N 1
 (Branch Empty 3834%N 1
 Empty)) 3838%N 2
 (Branch (Branch Empty 3841%N 1
 Empty) 3847%N 2
 (Branch Empty 3851%N 1
 Empty))) 3861%N 1
 (Branch (Branch (Branch Empty 3865%N 2
 Empty) 3868%N 1
 (Branch Empty 3874%N 2
 Empty)) 3878%N 4
 (Branch (Branch Empty 3886%N 3
 Empty) 3889%N 2
 (Branch Empty 3892%N 1
 Empty)))) 3898%N 2
 (Branch (Branch (Branch (Branch Empty 3902%N 1
 Empty) 3910%N 1
 (Branch Empty 3914%N 2
 Empty)) 3917%N 1
 (Branch (Branch Empty 3923%N 2
 Empty) 3927%N 1
 (Branch Empty 3937%N 1
 Empty))) 3941%N 2
 (Branch (Branch (Branch Empty 3944%N 1
 Empty) 3950%N 2
 (Branch Empty 3954%N 1
 Empty)) 3964%N 1
 (Branch (Branch Empty 3968%N 2
 Empty) 3971%N 1
 (Branch Empty 3977%N 2
 Empty))))) 3981%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3989%N 3
 Empty) 3992%N 2
 Empty) 3995%N 1
 (Branch Empty 4001%N 2
 Empty)) 4005%N 6
 (Branch (Branch Empty 4008%N 5
 Empty) 4012%N 4
 (Branch Empty 4015%N 3
 Empty))) 4018%N 2
 (Branch (Branch (Branch Empty 4021%N 1
 Empty) 4027%N 2
 (Branch Empty 4031%N 6
 Empty)) 4034%N 5
 (Branch (Branch Empty 4038%N 4
 Empty) 4041%N 3
 (Branch Empty 4044%N 2
 Empty)))) 4047%N 1
 (Branch (Branch (Branch (Branch Empty 4053%N 2
 Empty) 4057%N 6
 (Branch Empty 4060%N 5
 Empty)) 4064%N 4
 (Branch (Branch Empty 4067%N 3
 Empty) 4070%N 2
 (Branch Empty 4073%N 1
 Empty))) 4079%N 2
 (Branch (Branch (Branch Empty 4083%N 6
 Empty) 4086%N 5
 (Branch Empty 4090%N 4
 Empty)) 4093%N 3
 (Branch (Branch Empty 4096%N 2
 Empty) 4099%N 1
 (Branch Empty 4105%N 2
 Empty))))))) 4109%N 6
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4112%N 5
 Empty) 4116%N 4
 Empty) 4119%N 3
 (Branch Empty 4122%N 2
 Empty)) 4125%N 1
 (Branch (Branch Empty 4131%N 2
 Empty) 4135%N 3
 (Branch Empty 4138%N 2
 Empty))) 4142%N 1
 (Branch (Branch (Branch Empty 4149%N 1
 Empty) 4153%N 2
 (Branch Empty 4156%N 1
 Empty)) 4162%N 2
 (Branch (Branch Empty 4166%N 4
 Empty) 4173%N 3
 (Branch Empty 4176%N 2
 Empty)))) 4179%N 1
 (Branch (Branch (Branch (Branch Empty 4185%N 2
 Empty) 4189%N 1
 (Branch Empty 4197%N 1
 Empty)) 4201%N 2
 (Branch (Branch Empty 4204%N 1
 Empty) 4210%N 2
 (Branch Empty 4214%N 1
 Empty))) 4224%N 1
 (Branch (Branch (Branch Empty 4228%N 2
 Empty) 4231%N 1
 (Branch Empty 4237%N 2
 Empty)) 4241%N 1
 (Branch (Branch Empty 4251%N 1
 Empty) 4255%N 2
 (Branch Empty 4258%N 1
 Empty))))) 4264%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4268%N 4
 Empty) 4276%N 3
 Empty) 4279%N 2
 (Branch Empty 4282%N 1
 Empty)) 4288%N 2
 (Branch (Branch Empty 4292%N 1
 Empty) 4300%N 1
 (Branch Empty 4304%N 2
 Empty))) 4307%N 1
 (Branch (Branch (Branch Empty 4313%N 2
 Empty) 4317%N 1
 (Branch Empty 4327%N 1
 Empty)) 4331%N 2
 (Branch (Branch Empty 4334%N 1
 Empty) 4340%N 2
 (Branch Empty 4344%N 1
 Empty)))) 4354%N 1
 (Branch (Branch (Branch (Branch Empty 4358%N 2
 Empty) 4361%N 1
 (Branch Empty 4367%N 2
 Empty)) 4371%N 4
 (Branch (Branch Empty 4379%N 3
 Empty) 4382%N 2
 (Branch Empty 4385%N 1
 Empty))) 4391%N 2
 (Branch (Branch (Branch Empty 4395%N 1
 Empty) 4403%N 1
 (Branch Empty 4407%N 2
 Empty)) 4410%N 1
 (Branch (Branch Empty 4416%N 2
 Empty) 4420%N 1
 (Branch Empty 4430%N 1
 Empty)))))) 4434%N 2
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4437%N 1
 Empty) 4443%N 2
 Empty) 4447%N 1
 (Branch Empty 4457%N 1
 Empty)) 4461%N 2
 (Branch (Branch Empty 4464%N 1
 Empty) 4470%N 2
 (Branch Empty 4474%N 1
 Empty))) 4486%N 1
 (Branch (Branch (Branch Empty 4490%N 2
 Empty) 4493%N 1
 (Branch Empty 4499%N 2
 Empty)) 4503%N 4
 (Branch (Branch Empty 4509%N 3
 Empty) 4512%N 2
 (Branch Empty 4515%N 1
 Empty)))) 4521%N 2
 (Branch (Branch (Branch (Branch Empty 4525%N 1
 Empty) 4533%N 1
 (Branch Empty 4537%N 2
 Empty)) 4540%N 1
 (Branch (Branch Empty 4546%N 2
 Empty) 4550%N 2
 (Branch Empty 4556%N 1
 Empty))) 4565%N 1
 (Branch (Branch (Branch Empty 4570%N 3
 Empty) 4572%N 2
 (Branch Empty 4575%N 1
 Empty)) 4583%N 1
 (Branch (Branch Empty 4588%N 1
 Empty) 4595%N 1
 (Branch Empty 4599%N 5
 Empty))))) 4602%N 4
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4605%N 3
 Empty) 4608%N 2
 Empty) 4611%N 1
 (Branch Empty 4617%N 2
 Empty)) 4621%N 3
 (Branch (Branch Empty 4624%N 2
 Empty) 4628%N 1
 (Branch Empty 4635%N 1
 Empty))) 4639%N 2
 (Branch (Branch (Branch Empty 4642%N 1
 Empty) 4648%N 2
 (Branch Empty 4652%N 2
 Empty)) 4658%N 1
 (Branch (Branch Empty 4666%N 1
 Empty) 4671%N 3
 (Branch Empty 4674%N 2
 Empty)))) 4677%N 1
 (Branch (Branch (Branch (Branch Empty 4683%N 2
 Empty) 4687%N 3
 (Branch Empty 4690%N 2
 Empty)) 4694%N 1
 (Branch (Branch Empty 4698%N 3
 Empty) 4701%N 2
 (Branch Empty 4704%N 1
 Empty))) 4710%N 2
 (Branch (Branch (Branch Empty 4714%N 3
 Empty) 4717%N 2
 (Branch Empty 4721%N 1
 Empty)) 4731%N 1
 (Branch (Branch Empty 4741%N 1
 Empty) 4745%N 2
 (Branch Empty 4748%N 1
 Empty)))))))))).

Definition drain_rank (v : N) : nat :=
  match lookup rank_tree v with Some k => k | None => 0 end.

Definition rank_ok (v : N) : bool :=
  match k215 v with
  | Some (Test _ _ b) =>
      Nat.ltb (drain_rank (destination b)) (drain_rank v) && Nat.leb (drain_rank v) 6
  | _ => false
  end.

Theorem vertex_count : length vertices = 1426.
Proof. vm_compute; reflexivity. Qed.
Theorem drain_count : length drains = 1059.
Proof. vm_compute; reflexivity. Qed.
Theorem core_count : length core = 367.
Proof. vm_compute; reflexivity. Qed.

Theorem vertices_nodup : NoDup vertices.
Proof.
  assert (E : nodup N.eq_dec vertices = vertices) by (vm_compute; reflexivity).
  rewrite <- E; apply NoDup_nodup.
Qed.

Theorem core_nodup : NoDup core.
Proof. apply NoDup_filter; exact vertices_nodup. Qed.

Definition definedb (v : N) : bool :=
  match k215 v with Some _ => true | None => false end.

Theorem vertices_defined_checked : forallb definedb vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem member_defined v : In v vertices -> exists x, k215 v = Some x.
Proof.
  intro Hv; pose proof vertices_defined_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  unfold definedb in H; destruct (k215 v) as [x|] eqn:E; [eauto|discriminate].
Qed.

Theorem all_drains_valid : forall v, In v drains -> drainb k215 v = true.
Proof.
  intros v H; apply filter_In in H; exact (proj2 H).
Qed.

Theorem drain_ranks_checked : forallb rank_ok drains = true.
Proof. vm_compute; reflexivity. Qed.

Theorem drain_rank_decreases v r a b :
  In v drains -> k215 v = Some (Test r a b) ->
  drain_rank (destination b) < drain_rank v /\ drain_rank v <= 6.
Proof.
  intros Hv E.
  pose proof drain_ranks_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  unfold rank_ok in H; rewrite E in H.
  rewrite Bool.andb_true_iff, Nat.ltb_lt, Nat.leb_le in H; exact H.
Qed.

Theorem normalization_targets_checked :
  forallb (fun v => existsb (N.eqb (target 6 k215 v)) core) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem normalizes_to_core v : In v vertices -> In (target 6 k215 v) core.
Proof.
  intro Hv; pose proof normalization_targets_checked as H.
  rewrite forallb_forall in H; specialize (H v Hv).
  apply existsb_exists in H; destruct H as [w [Hw E]].
  apply N.eqb_eq in E; subst; assumption.
Qed.

Theorem every_vertex_normalizes v :
  In v vertices -> drainb k215 (target 6 k215 v) = false.
Proof.
  intro Hv; pose proof (normalizes_to_core v Hv) as H.
  apply filter_In in H; destruct H as [_ H]; apply Bool.negb_true_iff in H; exact H.
Qed.

Theorem defined_vertex_member v x : k215 v = Some x -> In v vertices.
Proof.
  intro H; unfold k215 in H; apply lookup_member in H.
  apply (in_map fst) in H; exact H.
Qed.

Theorem all_defined_normalize_to_core v x R :
  k215 v = Some x -> In (fst (normalize 6 k215 v R)) core.
Proof.
  intro H; rewrite normalize_target.
  apply normalizes_to_core; eapply defined_vertex_member; eauto.
Qed.

Theorem k215_normalization_correct v R :
  halts k215 v R <->
    halts k215 (fst (normalize 6 k215 v R)) (snd (normalize 6 k215 v R)).
Proof. apply normalize_halts_iff. Qed.

Theorem entry_is_core : In 0%N core.
Proof.
  assert (H : existsb (N.eqb 0%N) core = true) by (vm_compute; reflexivity).
  apply existsb_exists in H; destruct H as [w [Hw E]].
  apply N.eqb_eq in E; subst; assumption.
Qed.

Definition destinations_ok (x : N * node) : bool :=
  match snd x with
  | Halt => true
  | Test _ a b =>
      existsb (N.eqb (destination a)) vertices && existsb (N.eqb (destination b)) vertices
  end.

Theorem graph_closed_checked : forallb destinations_ok (elements k215_tree) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma destination_member v r a b : k215 v = Some (Test r a b) ->
  In (destination a) vertices /\ In (destination b) vertices.
Proof.
  intro Hv; unfold k215 in Hv; apply lookup_member in Hv.
  pose proof graph_closed_checked as H; rewrite forallb_forall in H.
  specialize (H (v, Test r a b) Hv); simpl in H.
  apply Bool.andb_true_iff in H; destruct H as [Ha Hb].
  split; [apply existsb_exists in Ha; destruct Ha as [w [Hw E]]|
          apply existsb_exists in Hb; destruct Hb as [w [Hw E]]];
    apply N.eqb_eq in E; subst; assumption.
Qed.

Theorem k215_closed v r a b : k215 v = Some (Test r a b) ->
  (exists x, k215 (destination a) = Some x) /\
  (exists x, k215 (destination b) = Some x).
Proof.
  intro H; destruct (destination_member _ _ _ _ H) as [Ha Hb].
  split; apply member_defined; assumption.
Qed.

Theorem step_destination_member v R w Q :
  step k215 v R w Q -> In w vertices.
Proof.
  intro H; destruct H.
  - exact (proj2 (destination_member _ _ _ _ H)).
  - exact (proj1 (destination_member _ _ _ _ H)).
Qed.

Theorem accelerated_successor_in_core v R w Q :
  step k215 v R w Q -> In (fst (normalize 6 k215 w Q)) core.
Proof.
  intro H; rewrite normalize_target.
  apply normalizes_to_core; eapply step_destination_member; eauto.
Qed.

Theorem k215_core_halts_iff v R : core_halts 6 k215 v R <-> halts k215 v R.
Proof. apply core_halts_iff. Qed.

Theorem k215_normalized_core_halts_iff v R :
  core_halts 6 k215 (fst (normalize 6 k215 v R)) (snd (normalize 6 k215 v R))
  <-> halts k215 v R.
Proof. apply normalized_core_halts_iff. Qed.

Theorem core_has_one_halt :
  length (filter (fun v => match k215 v with Some Halt => true | _ => false end) core) = 1.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions k215_core_halts_iff.
Print Assumptions k215_normalized_core_halts_iff.
Print Assumptions accelerated_successor_in_core.

Print Assumptions k215_normalization_correct.
Print Assumptions all_defined_normalize_to_core.
Print Assumptions drain_rank_decreases.
