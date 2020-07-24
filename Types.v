(** Types *)
Require Export List.
Import ListNotations.

Inductive GType :=
| I : GType
| X : GType
| Z : GType
| i : GType -> GType
| neg : GType -> GType
| mul : GType -> GType -> GType
| tensor : list GType ->  GType
| cap : GType -> GType -> GType
| arrow : GType -> GType -> GType
| blank : GType
| times : GType -> GType -> GType.

Notation "A ⊗ B ⊗ .. ⊗ Z" := (tensor (cons A (cons B .. (cons Z nil) ..))) (at level 50).
Notation "'_'" := blank.
Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
Infix "×" := times (at level 60, no associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X * Z)).

Inductive Singleton : GType -> Prop :=
| SI : Singleton I
| SX : Singleton X
| SZ : Singleton Z
| S_neg : forall A, Singleton A -> Singleton (neg A)
| S_i :   forall A, Singleton A -> Singleton (i A)
| S_mul : forall A B, Singleton A -> Singleton B -> Singleton (A * B).

Hint Resolve SI SX SZ S_neg S_i S_mul : sing_db.

Lemma SY : Singleton Y.
Proof. auto with sing_db. Qed.

Parameter Geq : GType -> GType -> Prop.
Infix "==" := Geq (at level 100).

(* Multiplication laws *)

Axiom mul_assoc : forall A B C, A * (B * C) == A * B * C.
Axiom mul_I_l : forall A, I * A == A.
Axiom mul_I_r : forall A, A * I == A.
Axiom Xsqr : X * X == I.
Axiom Zsqr : Z * Z == I.
Axiom ZmulX : Z * X == - (X * Z).

Axiom neg_inv : forall A, - - A == A.
Axiom neg_dist_l : forall A B, -A * B == - (A * B).
Axiom neg_dist_r : forall A B, A * -B == - (A * B).

Axiom i_sqr : forall A, i (i A) == -A.
Axiom i_dist_l : forall A B, i A * B == i (A * B).
Axiom i_dist_r : forall A B, A * i B == i (A * B).

Axiom i_neg_comm : forall A, i (-A) == -i A.

Hint Rewrite mul_I_l mul_I_r Xsqr Zsqr ZmulX neg_inv neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.

(** ** Tensor Laws *)

Axiom neg_tensor_dist : forall A t1 t2,
    tensor (t1 ++ [-A] ++ t2) == - tensor (t1 ++ [A] ++ t2).
Axiom i_tensor_dist : forall A t1 t2,
    tensor (t1 ++ [i A] ++ t2) == i (tensor (t1 ++ [A] ++ t2)).

Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1 with
  | [] => []
  | x :: xs => match l2 with
             | [] => []
             | y :: ys => f x y :: map2 f xs ys
             end
  end.

Axiom map_mul_tensor : forall l1 l2, tensor l1 * tensor l2 == tensor (map2 mul l1 l2).

(*
Fixpoint normalize_mul (G : GType) : GType :=
  match G with
  | A * I => normalize_mul A
  | I * B => normalize_mul B
  | X * X => I 
  | Z * Z => I 
  | -A * -B => normalize_mul A 
 *)

(* Assumes every element of l is normalized *)
(*
Fixpoint normalize_list (l : list GType) : bool * bool * list GType :=
  match l with
  | nil => (false, false, l)
  | A :: As => match A with (* could normalize_mul A here *)
             | - i A' => let (opp, im, As') := normalize_list As in
                        if im then (opp, false, A :: As') else (negb opp, true, A :: As')
             | - A'   => let (opp, im, As') := normalize_list As in
                        (negb opp, im, As')
             | i A'   => let (opp, im, As') := normalize_list As in
                        if im then (negb opp, false, A :: As') else (opp, true, A :: As')
             | A'     => let (opp, im, As') := normalize_list As in
                        (opp, im, A :: As')

               
             end
  end.
                          Fixpoint normalize_tensor : 
*)

(** ** Multiplication & Tensor Laws *)



Axiom mul_tensor_dist : forall A B C D,
  length A = length C ->
  length B = length D ->    
  tensor (A ++ B) * tensor (C ++ D) = (A * C) ⊗ (B * D).

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗ B = (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall A B,
    Singleton A ->
    Singleton B ->
    (A * B) ⊗ I = (A ⊗ I) * (B ⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall A B,
    I ⊗ (A * B) = (I ⊗ A) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.
  
Hint Rewrite neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.

(** ** Intersection Laws *)

Axiom cap_idem : forall A, A ∩ A = A.

Axiom cap_comm : forall A B, A ∩ B = B ∩ A.

Axiom cap_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.

Axiom cap_I_l : forall A,
  Singleton A ->
  I ∩ A = A.

Lemma cap_I_r : forall A,
  Singleton A ->
  A ∩ I = A.
Proof. intros; rewrite cap_comm, cap_I_l; easy. Qed.


(* Note: I haven't proven that this works or terminates.
   An anticommutative monoidal solver would be ideal here. *)
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

Lemma Ysqr : Y * Y = I. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulZ : X * Z = - Z * X. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulY : X * Y = i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulX : Y * X = -i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma ZmulY : Z * Y = -i X. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulZ : Y * Z = i X. Proof. normalize_mul. reflexivity. Qed.
