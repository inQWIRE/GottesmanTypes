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

(* Result : X × Z × Z *)

(** Unentangling one qubit *)

Definition PSEP := GHZ3; CNOT 1 2.

Lemma PSEPTypes : PSEP :: (Z ⊗ I ⊗ I → X ⊗ X ⊗ I) ∩
                         (I ⊗ Z ⊗ I → Z ⊗ Z ⊗ I) ∩
                         (I ⊗ I ⊗ Z → I ⊗ I ⊗ Z).
Proof. type_check_base. Qed.
