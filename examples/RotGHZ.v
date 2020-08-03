Require Import Typing.
Require Import MoreExamples.

Definition sqrtX (n : nat) : prog := H' n; S' n; H' n.

