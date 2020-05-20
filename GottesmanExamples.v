(** * Examples from Gottesman Paper *)

Require Import Typing.

(* Example 1 *)

Lemma SWAP_X1 : (SWAP 0 1) :: X ⊗ I → I ⊗ X.
Proof. type_check_base. Qed.  

Lemma SWAPTypes : (SWAP 0 1) :: (X ⊗ I → I ⊗ X) ∩ (I ⊗ X → X ⊗ I) ∩
                               (Z ⊗ I → I ⊗ Z) ∩ (I ⊗ Z → Z ⊗ I).
Proof. type_check_base. Qed.  

(* Add a lemma that this being true on X and Z makes it
   true on all bases?
   Then we can prove a more general version of SWAP_basis *)

(* Example 2 *)

Definition had_cnot : prog := H' 0; H' 1; CNOT 0 1; H' 0; H' 1.

Lemma had_cnot_types : had_cnot :: (X ⊗ I → X ⊗ I) ∩ (I ⊗ X → X ⊗ X) ∩
                                  (Z ⊗ I → Z ⊗ Z) ∩ (I ⊗ Z → I ⊗ Z).
Proof. type_check_base. Qed.
  

(* TODO: Want a general notion of equality between programs. *)

(* TODO: Need to get h_basis_to_config coercion working *)

(* Example 3 *)

Definition hitite : prog := H' 0; S' 1; CNOT 0 1; H' 1; CNOT 0 1.

Lemma hititeTypes : hitite :: (X ⊗ I → Z ⊗ I)             ∩ (I ⊗ X → -(I ⊗ Y)) ∩
                             (Z ⊗ I → (X * Z) ⊗ (X * Z)) ∩ (I ⊗ Z → Z ⊗ X).
Proof. type_check_base. Qed.
  
(* Example 4 *)

Definition cnot_notc : prog := CNOT 0 1; CNOT 1 0.

Lemma cnot_notc_Types : cnot_notc :: (X ⊗ I → I ⊗ X) ∩ (I ⊗ X → X ⊗ X) ∩
                                    (Z ⊗ I → Z ⊗ Z) ∩ (I ⊗ Z → Z ⊗ I).
Proof. type_check_base. Qed.

(* Example 5 *)

Definition bell : prog := H' 0; CNOT 0 1.

Lemma bellTypes : bell :: (Z ⊗ I → X ⊗ X) ∩ (I ⊗ Z → Z ⊗ Z).
Proof. type_check_base. Qed.

(* Our own tests *)
Lemma bell_ZZ : bell :: (Z ⊗ Z → (X * Z) ⊗ (X * Z)).
Proof. type_check_base. Qed.

Lemma bell_ZZ' : bell :: (Z ⊗ Z → -(Y ⊗ Y)).
Proof. type_check_base. Qed.

(* Example 6 *)

(* Can we represent this as a program? *)

(* Example 7 *)

Definition ec_code : prog :=
  H' 3; CNOT 0 2; CNOT 1 2; CNOT 3 0; CNOT 3 1; CNOT 3 2.

(* What to prove? *)

(* Example 8 *)

(* Example 9 *)

(* Now with measurement! *)

(* Example 10: Teleportation *)

(* Measurement-free teleportation with bell initialization *)

Definition bell' : prog := H' 1; CNOT 1 2.

Definition alice : prog := CNOT 0 1; H' 0.

Definition bob : prog := CNOT 1 2; CZ 0 2.

Definition teleport : prog := bell'; alice; bob.

Lemma teleportTypes : teleport :: (X ⊗ I ⊗ I → I ⊗ X ⊗ X) ∩ (Z ⊗ I ⊗ I → X ⊗ I ⊗ Z).
Proof. type_check_base. Qed.
  
