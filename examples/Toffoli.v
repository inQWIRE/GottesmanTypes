Require Import Separability.

(** * Toffoli general spec *)

Definition TDAG n : prog := Z' n; S' n; T' n.

Definition TOFFOLI a b c :=
  H' c;
  CNOT b c; TDAG c;
  CNOT a c; T' c;
  CNOT b c; TDAG c;
  CNOT a c; T' b; T' c; H' c;
  CNOT a b; T' a; TDAG b;
  CNOT a b.

Lemma ToffoliTypes: TOFFOLI 0 1 2 :: (Z ⊗ I ⊗ I → Z ⊗ I ⊗ I) ∩
                                    (I ⊗ Z ⊗ I → I ⊗ Z ⊗ I) ∩
                                    (I ⊗ I ⊗ X → I ⊗ I ⊗ X).
Proof. type_check_base. Qed.

Lemma ToffoliSep: TOFFOLI 0 1 2 :: Z × Z × X → Z × Z × X.
Proof.
  rewrite sep_expansion3 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  type_check_base.
  type_check_base.
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_l Z (I ⊗ I)); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I)); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l); auto with sep_db.
Qed.
