Require Import Separability.

(** * The Top type *)

Parameter top : GType.
Notation "⊤" := top.

Axiom SingletonTop : Singleton ⊤.
Hint Resolve SingletonTop : sing_db.

(* ⊤ an annihilator for * ? *)
Axiom mul_top_l : forall A, ⊤ * A = ⊤.
Axiom mul_top_r : forall A, A * ⊤ = ⊤.
Lemma neg_top : - ⊤ = ⊤.
Proof. rewrite <- (mul_I_l ⊤), <- neg_dist_l, mul_top_r, mul_top_r. easy. Qed.
Lemma i_top : i ⊤ = ⊤.
Proof. rewrite <- (mul_I_l ⊤), <- i_dist_l, mul_top_r, mul_top_r. easy. Qed.
Hint Rewrite mul_top_l mul_top_r neg_top i_top : mul_db.

Axiom TTypes : T' 0 :: (Z → Z) ∩ (X → ⊤).
Axiom HTop : H' 0 :: ⊤ → ⊤.
Axiom STop : S' 0 :: ⊤ → ⊤.
Axiom TTop : T' 0 :: ⊤ → ⊤.
Axiom CNOTTop : CNOT 0 1 :: (I ⊗ ⊤ → ⊤ ⊗ ⊤) ∩ (⊤ ⊗ I → ⊤ ⊗ ⊤).

Hint Resolve TTypes HTop STop TTop CNOTTop : base_types_db.

Lemma ZTop : Z' 0 :: ⊤ → ⊤.
Proof. type_check_base. Qed.

Lemma XTop : X' 0 :: ⊤ → ⊤.
Proof. type_check_base. Qed.

Lemma YTop : Y' 0 :: ⊤ → ⊤.
Proof. type_check_base. Qed.


Lemma CZTop : CZ 0 1 :: ⊤ ⊗ ⊤ → ⊤ ⊗ ⊤.
Proof. type_check_base. Qed.

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

Lemma ToffoliTypes: TOFFOLI 0 1 2 :: (Z ⊗ I ⊗ I → Z ⊗ I ⊗ I) ∩ (X ⊗ I ⊗ I → ⊤ ⊗ ⊤ ⊗ ⊤) ∩
                                    (I ⊗ Z ⊗ I → I ⊗ Z ⊗ I) ∩ (X ⊗ I ⊗ I → ⊤ ⊗ ⊤ ⊗ ⊤) ∩
                                    (I ⊗ I ⊗ Z → ⊤ ⊗ ⊤ ⊗ ⊤) ∩ (I ⊗ I ⊗ X → I ⊗ I ⊗ X).
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
