Require Import DerivedGates.
Require Import Separability.

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

(** ** Superdense Coding Separability *)

Lemma superdense_types_sep : superdense :: Z × Z × Z × Z → Z × Z × Z × Z.
Proof.
  rewrite sep_expansion4 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  type_check_base.
  type_check_base.
  type_check_base.
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I ⊗ I)); auto with sep_db.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I)); auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite cap_I_l; auto with sep_db.
Qed.
