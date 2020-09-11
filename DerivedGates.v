Require Export Programs.

(* I, X, Y and Z as derived gates *)
Definition Z' n : prog := S' n ; S' n.
Definition X' n : prog := H' n ; Z' n; H' n.
Definition Y' n : prog := S' n; X' n; Z' n; S' n.
Definition I' n : prog := H' n; H' n.

(* Other common gates *)
Definition CZ m n : prog := H' n ; CNOT m n ; H' n.
Definition SWAP m n : prog := CNOT m n; CNOT n m; CNOT m n.

Lemma ITypes : I' 0 :: (X → X) ∩ (Z → Z).
Proof. type_check_base. Qed.

Lemma ZTypes : Z' 0 :: (X → -X) ∩ (Z → Z).
Proof. type_check_base. Qed.

Lemma XTypes : X' 0 :: (X → X) ∩ (Z → -Z).
Proof. type_check_base. Qed.

Lemma YTypes : Y' 0 :: (X → -X) ∩ (Z → -Z).
Proof. type_check_base. Qed.

Lemma CZTypes : CZ 0 1 :: (X ⊗ I → X ⊗ Z) ∩ (I ⊗ X → Z ⊗ X) ∩
                         (Z ⊗ I → Z ⊗ I) ∩ (I ⊗ Z → I ⊗ Z).
Proof. type_check_base. Qed.

Lemma SWAPTypes : (SWAP 0 1) :: (X ⊗ I → I ⊗ X) ∩ (I ⊗ X → X ⊗ I) ∩
                               (Z ⊗ I → I ⊗ Z) ∩ (I ⊗ Z → Z ⊗ I).
Proof. type_check_base. Qed.

(* Types on Y *)

Lemma HTypesY : H' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma STypesY : S' 0 :: Y → - X.
Proof. type_check_base. Qed.

Lemma ITypesY : I' 0 :: Y → Y.
Proof. type_check_base. Qed.

Lemma XTypesY : X' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma ZTypesY : Z' 0 :: Y → - Y.
Proof. type_check_base. Qed.

Lemma YTypesY : Y' 0 :: Y → Y.
Proof. type_check_base. Qed.

Lemma CNOTTypesY : CNOT 0 1 :: (Y ⊗ I → Y ⊗ X) ∩ (I ⊗ Y → Z ⊗ Y).
Proof. type_check_base.
       (* need to automate this for CNOT case or add rules to base db *)
       (* exists in old typecheck *)
       rewrite (i_tensor_dist _ 0); simpl; try easy.
       rewrite decompose_tensor_mult_l; auto with sing_db.
       type_check_base.
       (* need broader tactic than show_tensor_eq *)
       rewrite <- i_dist_l.
       rewrite <- dist_i_tensor.
       rewrite mul_tensor; trivial.
       show_tensor_eq.

       rewrite (i_tensor_dist _ 1); simpl; try easy.
       rewrite decompose_tensor_mult_r; auto with sing_db.
       type_check_base.
       (* need broader tactic than show_tensor_eq *)
       rewrite <- i_dist_l.
       rewrite <- dist_i_tensor.
       rewrite mul_tensor; trivial.
       show_tensor_eq.
Qed.

Hint Resolve CNOTTypesY : base_types_db.

Lemma CZTypesY : CZ 0 1 :: (Y ⊗ I → Y ⊗ Z) ∩ (I ⊗ Y → Z ⊗ Y).
Proof. type_check_base.
       simpl.
       rewrite ZmulX, i_neg_comm.
       erewrite cons_neg_tensor.
       3: rewrite dist_neg_tensor, neg_inv; easy.
       2: rewrite <- (neg_inv I); easy.
       rewrite dist_neg_tensor.
       type_check_base.
       type_check_base.
       simpl. rewrite <- dist_neg_tensor.
       show_tensor_eq.
Qed.




