Require Import Types.
Require Import Typing.
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

Ltac type_check_base :=
  repeat apply cap_intro;
  repeat eapply arrow_comp; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Singleton _       => auto 50 with sing_db
         | |- ?g :: ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :: - ?A → ?B    => apply arrow_neg
         | |- ?g :: i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :: ?A * ?B → _ => apply arrow_mul
         | |- ?g :: (?A * ?B) ⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :: I ⊗ (?A * ?B) → _ => rewrite decompose_tensor_mult_r
         | |- ?g (S _) (S _) :: ?T => apply tensor_inc2
         | |- ?g 0 (S (S _)) :: ?T => apply tensor_inc2_r
         | |- ?g (S _) 0 :: ?T   => apply tensor2_comm
         | |- ?g 0 1 :: ?T       => apply tensor_base2
         | |- ?g (S _) :: ?T     => is_prog1 g; apply tensor_inc
         | |- ?g 0 :: ?T         => is_prog1 g; apply tensor_base
         | |- ?g :: ?A ⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B)
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?B = ?B'          => tryif is_evar B then fail else
             (repeat rewrite mul_tensor_dist);
             (repeat normalize_mul); try reflexivity
         end.


Ltac type_check_top :=
  type_check_base;
  repeat match goal with
  | |- context[i (⊤ ⊗ _)] => rewrite <- i_tensor_dist_l
  | |- context[i (_ ⊗ _)] => rewrite <- i_tensor_dist_r
  | |- context[- (⊤ ⊗ _)] => rewrite <- neg_tensor_dist_l
  | |- context[- (_ ⊗ _)] => rewrite <- neg_tensor_dist_r
  end; normalize_mul; try reflexivity.
                                   

Lemma ToffoliTypes: TOFFOLI 0 1 2 :: (Z ⊗ I ⊗ I → Z ⊗ I ⊗ I) ∩ (X ⊗ I ⊗ I → ⊤ ⊗ ⊤ ⊗ ⊤) ∩
                                    (I ⊗ Z ⊗ I → I ⊗ Z ⊗ I) ∩ (X ⊗ I ⊗ I → ⊤ ⊗ ⊤ ⊗ ⊤) ∩
                                    (I ⊗ I ⊗ Z → ⊤ ⊗ ⊤ ⊗ ⊤) ∩ (I ⊗ I ⊗ X → I ⊗ I ⊗ X).
Proof. type_check_top. Qed.

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
