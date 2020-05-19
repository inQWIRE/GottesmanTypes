(** * Examples from Gottesman Paper *)

Require Import Typing.

Hint Resolve SI SX SZ S_neg S_i S_mul : sing_db.


(** Tensor Laws *)
Axiom tensor_assoc : forall A B C, A ⊗ (B ⊗ C) = (A ⊗ B) ⊗ C.  

Axiom neg_tensor_dist_l : forall A B, -A ⊗ B = - (A ⊗ B).
Axiom neg_tensor_dist_r : forall A B, A ⊗ -B = - (A ⊗ B).
Axiom i_tensor_dist_l : forall A B, i A ⊗ B = i (A ⊗ B).
Axiom i_tensor_dist_r : forall A B, A ⊗ i B = i (A ⊗ B).

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Axiom mul_tensor_dist : forall A B C D,
    Singleton A ->
    Singleton C ->
    (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D).

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗ B = (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite I_1_l, I_1_r. (* rename to mul_I_l, mul_I_r *)
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall A B,
    Singleton A ->
    Singleton B ->
    (A * B) ⊗ I = (A ⊗ I) * (B ⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite I_1_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall A B,
    I ⊗ (A * B) = (I ⊗ A) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite I_1_l.
  easy.
Qed.
  
Hint Rewrite neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.

Axiom tensor_base : forall g E A A',
    Singleton A ->
    g 0 :: (A → A') ->
    g 0 ::  A ⊗ E → A' ⊗ E.

Axiom tensor_inc : forall g n E A A',
    Singleton E ->
    g n :: (A → A') ->
    g (s n) ::  E ⊗ A → E ⊗ A'.

Axiom tensor_base2 : forall g E A A' B B',
    Singleton A ->
    Singleton B ->
    g 0 1 :: (A ⊗ B → A' ⊗ B') ->
    g 0 1 :: (A ⊗ B ⊗ E → A' ⊗ B' ⊗ E).

Axiom tensor_inc2 : forall (g : nat -> nat -> prog) m n E A A' B B',
    Singleton E ->
    g m n :: (A ⊗ B → A' ⊗ B') ->
    g (s m) (s n) ::  E ⊗ A ⊗ B → E ⊗ A' ⊗ B'.

Axiom tensor_inc2_r : forall (g : nat -> nat -> prog) m n E A A' B B',
    Singleton A ->
    Singleton E ->
    g m n :: (A ⊗ B → A' ⊗ B') ->
    g m (s n) ::  A ⊗ E ⊗ B → A' ⊗ E ⊗ B'.

Axiom TypesI2 : forall p, p :: I ⊗ I → I ⊗ I.
Hint Resolve TypesI TypesI2 : base_types_db.

Ltac is_I A :=
  match A with
  | I => idtac
  end.

Ltac is_prog1 A :=
  match A with
  | H' => idtac
  | S' => idtac
  | T' => idtac
  end. 
              
Ltac is_prog2 A :=
  match A with
  | CNOT => idtac
  end.

Ltac normalize_mul :=
  repeat match goal with
  | |- context[(?A ⊗ ?B) ⊗ ?C] => rewrite <- (tensor_assoc A B C)
  end;
  repeat (rewrite mul_tensor_dist by auto with sing_db);
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc X Z _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc ).

(* Reduces to sequence of H, S and CNOT *)
Ltac type_check_base :=
  repeat apply cap_intro;
  repeat eapply arrow_comp; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- ?g :: ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :: - ?A → ?B    => apply arrow_neg
         | |- ?g :: i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :: ?A * ?B → _ => apply arrow_mul
         | |- ?g :: (?A * ?B) ⊗ I → _ => rewrite decompose_tensor_mult_l; auto with sing_db
         | |- ?g :: I ⊗ (?A * ?B) → _ => rewrite decompose_tensor_mult_r; auto with sing_db
         | |- ?g (S _) (S _) :: ?T => apply tensor_inc2; auto with sing_db
         | |- ?g 0 (S (S _)) :: ?T => apply tensor_inc2_r; auto with sing_db
         | |- ?g (S _) 0 :: ?T   => apply tensor2_comm; auto with sing_db
         | |- ?g 0 1 :: ?T       => apply tensor_base2; auto with sing_db
         | |- ?g (S _) :: ?T     => is_prog1 g; apply tensor_inc; auto with sing_db
         | |- ?g 0 :: ?T         => is_prog1 g; apply tensor_base; auto with sing_db
         | |- ?g :: ?A ⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B); auto with sing_db
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?B = ?B'          => tryif is_evar B then fail else normalize_mul; easy
         end.

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
  
(* Example 11: Remove XOR *)

(** * Own examples *)

(** * Proofs about derived unitaries *)

Lemma X_X1 : @h_eval 1 (X 0) [XX] = [XX].
Proof. reflexivity. Qed.
Lemma X_Z1 : @h_eval 1 (X 0) [ZZ] = [-1 * ZZ].
Proof. reflexivity. Qed.
Lemma Y_X1 : @h_eval 1 (Y 0) [XX] = [-1 * XX].
Proof. reflexivity. Qed.
Lemma Y_Z1 : @h_eval 1 (Y 0) [ZZ] = [-1 * ZZ].
Proof. reflexivity. Qed.
Lemma Z_X1 : @h_eval 1 (Z 0) [XX] = [-1 * XX].
Proof. reflexivity. Qed.
Lemma Z_Z1 : @h_eval 1 (Z 0) [ZZ] = [ZZ].
Proof. reflexivity. Qed.

Lemma CZ_X1 : @h_eval 2 (CZ 0 1) [XX,II] = [XX,ZZ].
Proof. reflexivity. Qed.
Lemma CZ_Z1 : @h_eval 2 (CZ 0 1) [ZZ,II] = [ZZ,II].
Proof. reflexivity. Qed.
Lemma CZ_X2 : @h_eval 2 (CZ 0 1) [II,XX] = [ZZ,XX].
Proof. reflexivity. Qed.
Lemma CZ_Z2 : @h_eval 2 (CZ 0 1) [II,ZZ] = [II,ZZ].
Proof. reflexivity. Qed.

(* Superdense coding *)

Definition bell00 : prog 4 :=
  H 2;
  CNOT 2 3.

Definition encode : prog 4 :=
    CZ 0 2; CNOT 1 2.

Definition decode : prog 4 :=
  CNOT 2 3;
  H 2.

Definition superdense := bell00 ; encode; decode.

Compute (h_eval superdense [ZZ,ZZ,ZZ,ZZ]). (* I, I, Z, Z *)
Compute (h_eval superdense [II,ZZ,ZZ,ZZ]). (* Z, I, Z, Z *)
Compute (h_eval superdense [ZZ,II,ZZ,ZZ]). (* I, Z, Z, Z *)
Compute (h_eval superdense [II,II,ZZ,ZZ]). (* Z, Z, Z, Z *)
Compute (h_eval superdense [ZZ,ZZ,ZZ,II]). (* I, Z, Z, I *)
Compute (h_eval superdense [ZZ,ZZ,II,ZZ]). (* Z, I, I, Z *)

Compute (h_eval superdense [ZZ,II,II,II]). (* Z, I, I, I *)
Compute (h_eval superdense [II,ZZ,II,II]). (* I, Z, I, I *)
Compute (h_eval superdense [II,II,ZZ,II]). (* Z, I, Z, I *)
Compute (h_eval superdense [II,II,II,ZZ]). (* I, Z, I, Z *)


Lemma superdense_ZZ : h_eval superdense [ZZ,ZZ,ZZ,ZZ] = [II,II,ZZ,ZZ].
Proof. reflexivity. Qed.

(* GHZ state *)

Compute (h_eval (CNOT 0 1) [XX*ZZ, ZZ]). (* X, XZ *)

Definition GHZ3 : prog :=
  H 0;
  CNOT 0 1;
  CNOT 1 2.

Compute (h_eval GHZ3 [ZZ,ZZ,ZZ]). (* XZ, X, XZ *)

Compute (h_eval GHZ3 [XX,II,II]). (* Z, I, I *)
Compute (h_eval GHZ3 [II,XX,II]). (* I, X, X *)
Compute (h_eval GHZ3 [II,II,XX]). (* I, I, X *)
Compute (h_eval GHZ3 [II,ZZ,ZZ]). (* Z, I, Z *)
Compute (h_eval GHZ3 [XX,ZZ,ZZ]). (* I, I, Z *)
Compute (h_eval GHZ3 [XX,II,ZZ]). (* Z, Z, Z *)
Compute (h_eval GHZ3 [XX,ZZ,II]). (* I, Z, I *)

Compute (h_eval GHZ3 [ZZ,II,II]). (* X, X, X *)
Compute (h_eval GHZ3 [II,ZZ,II]). (* Z, Z, I *)
Compute (h_eval GHZ3 [II,II,ZZ]). (* I, Z, Z *)


Compute (h_eval (CNOT 1 2; CNOT 0 1) [XX*ZZ,XX,XX*ZZ]). (* X, Z, Z ??? *)
Compute (h_eval (CNOT 0 1; CNOT 1 2) [XX*ZZ,XX,XX*ZZ]). (* X, Z, Z ??? *)

(** Honda motivating example *)

Definition SEP0 := GHZ3 ; CNOT 0 1; CNOT 0 2.

Compute (h_eval SEP0 [ZZ,II,II]). (* X, I, I *)
Compute (h_eval SEP0 [II,ZZ,II]). (* I, Z, I *)
Compute (h_eval SEP0 [II,II,ZZ]). (* I, Z, Z *) (* becomes I, I, Z *)

(* Result : X × Z × Z *)

(** Unentangling one qubit *)

Compute (h_eval (GHZ3;CNOT 1 2) [ZZ,II,II]). (* X, X, I *)
Compute (h_eval (GHZ3;CNOT 1 2) [II,ZZ,II]). (* Z, Z, I *)
Compute (h_eval (GHZ3;CNOT 1 2) [II,II,ZZ]). (* I, I, Z *)

Compute (h_eval (GHZ3;CNOT 2 1) [ZZ,II,II]). (* X, I, X *)
Compute (h_eval (GHZ3;CNOT 2 1) [II,ZZ,II]). (* Z, Z, Z *) (* becomes Z, I, Z *)
Compute (h_eval (GHZ3;CNOT 2 1) [II,II,ZZ]). (* I, Z, I *)
