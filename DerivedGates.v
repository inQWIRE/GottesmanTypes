Require Export Programs.

Ltac list_gt2 l :=
  let H := fresh in 
  assert (H : length l > 2) by (simpl; lia);
  clear H.

Ltac type_check_base :=
  repeat apply cap_intro;
  repeat eapply SeqTypes; (* will automatically unfold compound progs *)
  repeat (match goal with
         | |- context[?A * ?B]  => progress (rewrite <- (normalize_mul_eq (A * B)); simpl)
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- Singleton ?S      => tryif is_evar S then fail else auto 50 with sing_db
         | |- ?g :: ?A → ?B      => tryif is_evar B then fail else eapply Geq_arrow_r
         | |- ?g :: - ?A → ?B    => apply arrow_neg
         | |- ?g :: i ?A → ?B    => apply arrow_i
         | |- U1 ?u _ :: tensor ?A → ?B => eapply tensor_types1; [|easy]
         | |- U2 ?u (S _) _ :: tensor ?A → ?B =>
           eapply tensor_types2; [lia| |easy|easy]
         | |- U2 ?u _ _ :: tensor ?A → ?B =>
           list_gt2 A; eapply tensor_types2; [lia| |easy|easy]
         | |- ?g :: ?A * ?B → _  => apply arrow_mul
         | |- ?g :: ?A ⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             (* should be able to rewrite directly
             eapply Geq_arrow_l; [|rewrite decompose_tensor; reflexivity] *)
             rewrite decompose_tensor
         | |- ?B == ?B'               => rewrite mul_tensor by reflexivity
         | |- tensor ?B == tensor ?B' => tryif has_evar B then fail else show_tensor_eq
         | |- ?B == ?B'               => tryif has_evar B then fail else show_mul_eq
         end; simpl).  


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
       Search tensor mul.
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
       Search neg tensor.
       erewrite cons_neg_tensor.
       3: rewrite dist_neg_tensor, neg_inv; easy.
       2: rewrite <- (neg_inv I); easy.
       rewrite dist_neg_tensor.
       type_check_base.
       type_check_base.
       simpl. rewrite <- dist_neg_tensor.
       show_tensor_eq.
Qed.




