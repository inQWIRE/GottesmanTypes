Require Import Typing.

(** * Superdense coding *)

Definition bell00 : prog := H' 2; CNOT 2 3.

Definition encode : prog := CZ 0 2; CNOT 1 2.

Definition decode : prog := CNOT 2 3; H' 2.

Definition superdense := bell00 ; encode; decode.

Lemma superdenseTypesQPL : superdense :: (Z ⊗ Z ⊗ Z ⊗ Z → I ⊗ I ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.

Lemma superdenseTypes : superdense :: (Z ⊗ I ⊗ I ⊗ I → Z ⊗ I ⊗ I ⊗ I) ∩
                                     (I ⊗ Z ⊗ I ⊗ I → I ⊗ Z ⊗ I ⊗ I) ∩
                                     (I ⊗ I ⊗ Z ⊗ I → Z ⊗ I ⊗ Z ⊗ I) ∩
                                     (I ⊗ I ⊗ I ⊗ Z → I ⊗ Z ⊗ I ⊗ Z).
Proof. type_check_base. Qed.

(* Could replace I ⊗ Z ⊗ I ⊗ I with Z 2, I 1, I 3, I 4 *)
(* From which we derive  Z 2 × (I 1 ⊗ I 3 ⊗ I 4) *)

(* Could also derive I ⊗ Z_s ⊗ I ⊗ I *)
(* But this doesn't work for the 1st and 3rd being separable from 2nd and 4th. *)


  
(** * GHZ state *)

Definition GHZ3 : prog := H' 0; CNOT 0 1; CNOT 1 2.

Lemma GHZ3Types : GHZ3 :: (Z ⊗ I ⊗ I → X ⊗ X ⊗ X) ∩
                         (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ I) ∩
                         (I ⊗ I ⊗ Z → I ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.

(* Note: The second and third cases do contain GHZ as eigenvectors, as we'd expect.
   But didn't we say these are separable? *)

(** Honda motivating example *)

Definition SEP0 := GHZ3; CNOT 0 1; CNOT 0 2.

Lemma SEP0Types : SEP0 :: (Z ⊗ I ⊗ I → X ⊗ I ⊗ I) ∩
                         (I ⊗ Z ⊗ I → I ⊗ Z ⊗ I) ∩
                         (I ⊗ I ⊗ Z → I ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.

Definition SEP0' := GHZ3; CNOT 1 0; CNOT 2 1.

Lemma SEP0Types' : SEP0' :: (Z ⊗ I ⊗ I → I ⊗ I ⊗ X) ∩
                           (I ⊗ Z ⊗ I → Z ⊗ I ⊗ I) ∩
                           (I ⊗ I ⊗ Z → I ⊗ Z ⊗ I).
Proof. type_check_base. Qed.


(* Result : X × Z × Z *)

(** Unentangling one qubit *)
Definition PSEP01 := GHZ3; CNOT 0 1.

Lemma PSEPTypes01 : PSEP01 :: (Z ⊗ I ⊗ I → X ⊗ I ⊗ X) ∩
                             (I ⊗ Z ⊗ I → I ⊗ Z ⊗ I) ∩
                             (I ⊗ I ⊗ Z → Z ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.


Definition PSEP10 := GHZ3; CNOT 1 0.

Lemma PSEPTypes10 : PSEP10 :: (Z ⊗ I ⊗ I → I ⊗ X ⊗ X) ∩
                             (I ⊗ Z ⊗ I → Z ⊗ I ⊗ I) ∩
                             (I ⊗ I ⊗ Z → I ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.


Definition PSEP02 := GHZ3; CNOT 0 2.

Lemma PSEPTypes02 : PSEP02 :: (Z ⊗ I ⊗ I → X ⊗ X ⊗ I) ∩
                             (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ I) ∩
                             (I ⊗ I ⊗ Z → Z ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.

Definition PSEP20 := GHZ3; CNOT 2 0.

Lemma PSEPTypes20 : PSEP20 :: (Z ⊗ I ⊗ I → I ⊗ X ⊗ X) ∩
                             (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ Z) ∩
                             (I ⊗ I ⊗ Z → I ⊗ Z ⊗ Z).
Proof. type_check_base. Qed.


(* works *)
Definition PSEP12 := GHZ3; CNOT 1 2.

Lemma PSEPTypes12 : PSEP12 :: (Z ⊗ I ⊗ I → X ⊗ X ⊗ I) ∩
                             (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ I) ∩
                             (I ⊗ I ⊗ Z → I ⊗ I ⊗ Z).
Proof. type_check_base. Qed.

Definition PSEP21 := GHZ3; CNOT 2 1.

Lemma PSEPTypes21 : PSEP21 :: (Z ⊗ I ⊗ I → X ⊗ I ⊗ X) ∩
                             (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ Z) ∩
                             (I ⊗ I ⊗ Z → I ⊗ Z ⊗ I).
Proof. type_check_base. Qed.

(* In all cases results should have one qubit unentangled *)

