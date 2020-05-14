(** Types *)

(* This won't work with equality due to inversion.
Inductive coefficient :=
| Gi
| Gneg.

Inductive GType :=
| I
| X
| Z
| scale : coefficient -> GType -> GType
| mul : GType -> GType -> GType
| tensor : GType -> GType -> GType
| cap : GType -> GType -> GType
| arrow : GType -> GType -> GType.
 *)

Parameter GType : Type.
Parameter I : GType.
Parameter X : GType.
Parameter Z : GType.
Parameter i : GType -> GType.
Parameter neg : GType -> GType.
Parameter mul : GType -> GType -> GType.
Parameter tensor : GType -> GType -> GType.
Parameter cap : GType -> GType -> GType.
Parameter arrow : GType -> GType -> GType.

Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
Infix "⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X * Z)).

(* Multiplication laws *)

Axiom mul_assoc : forall A B C, A * (B * C) = A * B * C.
Axiom I_1_l : forall A, I * A = A.
Axiom I_1_r : forall A, A * I = A.
Axiom Xsqr : X * X = I.
Axiom Zsqr : Z * Z = I.
Axiom ZmulX : Z * X = - (X * Z).

Axiom neg_inv : forall A, - - A = A.
Axiom neg_dist_l : forall A B, -A * B = - (A * B).
Axiom neg_dist_r : forall A B, A * -B = - (A * B).

Axiom i_sqr : forall A, i (i A) = -A.
Axiom i_dist_l : forall A B, i A * B = i (A * B).
Axiom i_dist_r : forall A B, A * i B = i (A * B).

Axiom i_neg_comm : forall A, i (-A) = -i A.

Hint Rewrite I_1_l I_1_r Xsqr Zsqr ZmulX neg_inv neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.

(* Note: I haven't proven that this works or terminates.
   An anticommutative monoidal solver would be ideal here. *)
Ltac normalize_mul :=
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc X Z _);
      autorewrite with mul_db;
      try rewrite mul_assoc ).

Lemma Ysqr : Y * Y = I. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulZ : X * Z = - Z * X. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulY : X * Y = i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulX : Y * X = -i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma ZmulY : Z * Y = -i X. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulZ : Y * Z = i X. Proof. normalize_mul. reflexivity. Qed.
