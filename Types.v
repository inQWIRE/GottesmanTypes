(** Types *)
Require Import Setoid.

Inductive GType :=
| I : GType
| X : GType
| Z : GType
| i : GType -> GType
| neg : GType -> GType
| mul :    GType -> GType -> GType
| tensor : GType -> GType ->  GType
| cap :    GType -> GType -> GType
| arrow :  GType -> GType -> GType
| blank :  GType (* for separability *).
(* | times :  GType -> GType -> GType. *)

Notation "'□'" := blank.
Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
(* Infix "×" := times (at level 49, right associativity). *)
Infix "⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X * Z)).

(* Could just use size = 1 ? *)
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

(** ** Equality between GTypes *)

Parameter Geq : GType -> GType -> Prop.
Infix "==" := Geq (at level 80).

Axiom Geq_refl  : forall A, A == A.
Axiom Geq_sym   : forall A B, A == B -> B == A.
Axiom Geq_trans : forall A B C, A == B -> B == C -> A == C.

Add Parametric Relation : GType Geq
  reflexivity proved by Geq_refl
  symmetry proved by Geq_sym
  transitivity proved by Geq_trans
  as mat_equiv_rel.

Axiom neg_compat    : forall x y, x == y -> - x == - y.
Axiom i_compat      : forall x y, x == y -> i x == i y.
Axiom mul_compat    : forall x y, x == y -> forall x0 y0, x0 == y0 -> x * x0 == y * y0.
Axiom tensor_compat : forall x y, x == y -> forall x0 y0, x0 == y0 -> x ⊗ x0 == y ⊗ y0.
Axiom cap_compat    : forall x y, x == y -> forall x0 y0, x0 == y0 -> x ∩ x0 == y ∩ y0.
Axiom arrow_compat  : forall x y, x == y -> forall x0 y0, x0 == y0 -> x → x0 == y → y0.

Add Parametric Morphism : neg with signature Geq ==> Geq as neg_mor.
Proof. apply neg_compat. Qed.
Add Parametric Morphism : i with signature Geq ==> Geq as i_mor.
Proof. apply i_compat. Qed.
Add Parametric Morphism : mul with signature Geq ==> Geq ==> Geq as mul_mor.
Proof. apply mul_compat. Qed.
Add Parametric Morphism : tensor with signature Geq ==> Geq ==> Geq as tensor_mor.
Proof. apply tensor_compat. Qed.
Add Parametric Morphism : cap with signature Geq ==> Geq ==> Geq as cap_mor.
Proof. apply cap_compat. Qed.
Add Parametric Morphism : arrow with signature Geq ==> Geq ==> Geq as arrow_mor.
Proof. apply arrow_compat. Qed.

(** ** Multiplication laws *)

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

Axiom tensor_assoc : forall A B C, A ⊗ (B ⊗ C) = (A ⊗ B) ⊗ C.  

Axiom neg_tensor_dist_l : forall A B, -A ⊗ B = - (A ⊗ B).
Axiom neg_tensor_dist_r : forall A B, A ⊗ -B = - (A ⊗ B).
Axiom i_tensor_dist_l : forall A B, i A ⊗ B = i (A ⊗ B).
Axiom i_tensor_dist_r : forall A B, A ⊗ i B = i (A ⊗ B).

(** ** Multiplication & Tensor Laws *)

(* Tensor length. Currently treats blank as having length 1 but could be 0 as well *)
Fixpoint size G :=
  match G with
  | - G' => size G'
  | i G' => size G'
  | G1 ⊗ G2 => size G1 + size G2
  | G1 * G2 => size G1 (* should equal size G2 *)
  | G1 ∩ G2 => size G1 (* should equal size G2 *)   
  | G1 → G2 => 0       (* not defined over arrows *)
  | _       => 1
  end.

Axiom mul_tensor_dist : forall A B C D,
  size A = size C ->
  size B = size D ->    
  (A ⊗ B) * (C ⊗ D) == (A * C) ⊗ (B * D).

Lemma singleton_size : forall A,
    Singleton A ->
    size A = 1.
Proof. induction 1; auto. Qed.

(* previously used Singleton A and B*)
Lemma decompose_tensor : forall A B,
    size A = 1 ->
    size B = 1 ->
    A ⊗ B == (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall A B,
    size A = size B ->
    (A * B) ⊗ I == (A ⊗ I) * (B ⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall A B,
    size A = size B ->
    I ⊗ (A * B) == (I ⊗ A) * (I ⊗ B).
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

(* Previously used Singleton A *)
Axiom cap_I_l : forall A, size A = 1 -> I ∩ A = A.

Lemma cap_I_r : forall A, size A = 1 -> A ∩ I = A.
Proof. intros; rewrite cap_comm, cap_I_l; easy. Qed.

(* Note: I haven't proven that this works or terminates.
   An anticommutative monoidal solver would be ideal here. *)
Ltac normalize_mul :=
  repeat match goal with
  | |- context[(?A ⊗ ?B) ⊗ ?C] => rewrite <- (tensor_assoc A B C)
  end;
  repeat (rewrite mul_tensor_dist by easy);
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc X Z _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc ).

Lemma Ysqr : Y * Y == I. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulZ : X * Z == - Z * X. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulY : X * Y == i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulX : Y * X == -i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma ZmulY : Z * Y == -i X. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulZ : Y * Z == i X. Proof. normalize_mul. reflexivity. Qed.
