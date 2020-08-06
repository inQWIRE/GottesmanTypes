(** Types *)
Require Import Setoid.
Require Import List.

Inductive GType :=
| I : GType
| X : GType
| Z : GType
| i : GType -> GType
| neg : GType -> GType
| mul :    GType -> GType -> GType
| tensor : list GType ->  GType
| cap :    GType -> GType -> GType
| arrow :  GType -> GType -> GType
| blank :  GType (* for separability *).
(* | times :  GType -> GType -> GType. *)

Notation "'□'" := blank.
Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
(* Infix "×" := times (at level 49, right associativity). *)
(* Infix "⊗" := tensor (at level 51, right associativity). *)
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation "x ⊗ y ⊗ .. ⊗ z" := (tensor (cons x (cons y .. (cons z nil) ..))) (at level 51, y at next level).


Notation Y := (i (X * Z)).
Notation "⊥" := (X ∩ Y).

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

Definition Geq_opt oA oB :=
  match oA, oB with
  | Some A, Some B => A == B
  | None,   None   => True
  | _,      _      => False
  end.
  
Definition Geq_list (l1 l2 : list GType) := forall k,
  Geq_opt (nth_error l1 k) (nth_error l2 k).
(*  Geq (nth k l1 ⊥) (nth k l2). *)
    
Add Parametric Relation : GType Geq
  reflexivity proved by Geq_refl
  symmetry proved by Geq_sym
  transitivity proved by Geq_trans
  as Geq_rel.

Lemma Geq_opt_refl  : forall A, Geq_opt A A. Proof. destruct A; simpl; easy. Qed.
Lemma Geq_opt_sym  : forall A B, Geq_opt A B -> Geq_opt B A.
Proof. destruct A, B; simpl; easy. Qed.
Lemma Geq_opt_trans : forall A B C, Geq_opt A B -> Geq_opt B C -> Geq_opt A C.
Proof. destruct A, B, C; simpl; try easy. apply Geq_trans. Qed.

Add Parametric Relation : (option GType) Geq_opt
  reflexivity proved by Geq_opt_refl
  symmetry proved by Geq_opt_sym
  transitivity proved by Geq_opt_trans
  as Geq_opt_rel.

Lemma Geq_list_refl  : forall l, Geq_list l l.
Proof. induction l; intros []; simpl; easy. Qed.
Lemma Geq_list_sym   : forall l1 l2, Geq_list l1 l2 -> Geq_list l2 l1.
Proof. intros. intro k. apply Geq_opt_sym. easy. Qed.
Lemma Geq_list_trans : forall l1 l2 l3, Geq_list l1 l2 -> Geq_list l2 l3 -> Geq_list l1 l3.
Proof. intros. intro k. eapply Geq_opt_trans; easy. Qed.

Add Parametric Relation : (list GType) Geq_list
  reflexivity proved by Geq_list_refl
  symmetry proved by Geq_list_sym
  transitivity proved by Geq_list_trans
  as Geq_list_rel.

Axiom neg_compat    : forall x y, x == y -> - x == - y.
Axiom i_compat      : forall x y, x == y -> i x == i y.
Axiom mul_compat    : forall x y, x == y -> forall x0 y0, x0 == y0 -> x * x0 == y * y0.
Axiom cap_compat    : forall x y, x == y -> forall x0 y0, x0 == y0 -> x ∩ x0 == y ∩ y0.
Axiom arrow_compat  : forall x y, x == y -> forall x0 y0, x0 == y0 -> x → x0 == y → y0.
Axiom tensor_compat : forall l1 l2, Geq_list l1 l2 -> tensor l1 == tensor l2.

Add Parametric Morphism : neg with signature Geq ==> Geq as neg_mor.
Proof. apply neg_compat. Qed.
Add Parametric Morphism : i with signature Geq ==> Geq as i_mor.
Proof. apply i_compat. Qed.
Add Parametric Morphism : mul with signature Geq ==> Geq ==> Geq as mul_mor.
Proof. apply mul_compat. Qed.
Add Parametric Morphism : cap with signature Geq ==> Geq ==> Geq as cap_mor.
Proof. apply cap_compat. Qed.
Add Parametric Morphism : arrow with signature Geq ==> Geq ==> Geq as arrow_mor.
Proof. apply arrow_compat. Qed.
Add Parametric Morphism : tensor with signature Geq_list ==> Geq as tensor_mor.
Proof. apply tensor_compat. Qed.
Add Parametric Morphism : cons with signature Geq ==> Geq_list ==> Geq_list as cons_mor.
Proof.
  intros. intro k.
  induction k; simpl; easy.
Qed.


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

Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | a :: l1', b :: l2' => f a b :: (map2 f l1' l2')
  | _, _ => nil
  end.

Fixpoint update l k (A : GType) :=
  match k, l with
  | 0,    A' :: As => A :: As
  | S k', A' :: As => A' :: (update As k' A)
  | _,    _       => nil
  end.
  
Axiom neg_tensor_dist : forall l k A,
  nth k l ⊥ == - A ->
  tensor l == - tensor (update l k A).

Axiom i_tensor_dist : forall l k A,
  nth k l ⊥ == i A ->
  tensor l == i (tensor (update l k A)).

(** ** Multiplication & Tensor Laws *)

(*
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
*)

Axiom mul_tensor : forall l1 l2,
  length l1 = length l2 ->
  tensor l1 * tensor l2 == tensor (map2 mul l1 l2).

(*
Lemma singleton_size : forall A,
    Singleton A ->
    length A = 1.
Proof. induction 1; auto. Qed.
 *)

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗ B == (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor; auto with sing_db; simpl.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

(* Let's figure out if we need these before updating  
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
*)  

Hint Rewrite neg_tensor_dist neg_tensor_dist i_tensor_dist i_tensor_dist : tensor_db.

(** ** Intersection Laws *)

Axiom cap_idem : forall A, A ∩ A = A.

Axiom cap_comm : forall A B, A ∩ B = B ∩ A.

Axiom cap_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.

Axiom cap_I_l : forall A, Singleton A -> I ∩ A = A.

Lemma cap_I_r : forall A, Singleton A -> A ∩ I = A.
Proof. intros; rewrite cap_comm, cap_I_l; easy. Qed.

Lemma cap_I_tensor_l : forall l n,
  length l = n ->
  tensor (repeat I n) * tensor l == tensor l.
Proof.
  intros; subst.
  rewrite mul_tensor by (apply repeat_length).
  apply tensor_compat.
  induction l; simpl; try easy.
  rewrite mul_I_l.
  rewrite IHl.
  reflexivity.
Qed.

Definition flags_to_coefficients (bbA : bool * bool * GType) :=
  match bbA with
  | (false, false, A) => A
  | (false, true,  A) => i A
  | (true,  false, A) => - A
  | (true,  true,  A) => - i A
  end.

Infix "⊻" := xorb (at level 40). 

(* Input: singleton GType *)
(* Output: negated flag, imaginary flag, coefficient-free singleton GType *)
Fixpoint remove_coefficients_flags (A : GType) : bool * bool * GType:=
  match A with
  | - A' => match remove_coefficients_flags A' with
           (opp, im, A'') => (negb opp, im, A'')
           end
  | i A' => match remove_coefficients_flags A' with
           (opp, im,  A'') => (opp ⊻ im, negb im, A'')
           end
  | A1 * A2 => match remove_coefficients_flags A1, remove_coefficients_flags A2 with
              (opp1, im1,  A1'), (opp2, im2, A2') =>
                (opp1 ⊻ opp2 ⊻ (im1 && im2), im1 ⊻ im2, A1' * A2')
              end
  | A'   => (false, false, A')
  end.

Lemma remove_coefficients_flags_eq : forall A,
    flags_to_coefficients (remove_coefficients_flags A) == A.
Proof.
  intros.
  induction A; try easy.
  - simpl.
    destruct (remove_coefficients_flags A) as [[opp im] A'] eqn:E.
    destruct im, opp; simpl in *; auto; rewrite <- IHA; autorewrite with mul_db; easy.
  - simpl.
    destruct (remove_coefficients_flags A) as [[opp im] A'] eqn:E.
    destruct im, opp; simpl in *; auto; rewrite <- IHA; autorewrite with mul_db; easy.
  - simpl.
    destruct (remove_coefficients_flags A1) as [[opp1 im1] A1'] eqn:E1.
    destruct (remove_coefficients_flags A2) as [[opp2 im2] A2'] eqn:E2.
    destruct im1, opp1, im2, opp2; simpl in *; auto; rewrite <- IHA1, <- IHA2;
      autorewrite with mul_db; easy.
Qed.    

(*
Lemma remove_coefficients_flags_eq : forall A,
    Singleton A ->
    flags_to_coefficients (remove_coefficients_flags A) == A.
Proof.
  intros.
  induction A; try easy.
  - inversion H; subst. specialize (IHA H1). clear H H1.
    simpl.
    destruct (remove_coefficients_flags A) as [[opp im] A'] eqn:E.
    destruct im, opp; simpl in *; auto; rewrite <- IHA; autorewrite with mul_db; easy.
  - inversion H; subst. specialize (IHA H1). clear H H1.
    simpl.
    destruct (remove_coefficients_flags A) as [[opp im] A'] eqn:E.
    destruct im, opp; simpl in *; auto; rewrite <- IHA; autorewrite with mul_db; easy.
  - inversion H; subst. specialize (IHA1 H2). specialize (IHA2 H3). clear H H2 H3.
    simpl.
    destruct (remove_coefficients_flags A1) as [[opp1 im1] A1'] eqn:E1.
    destruct (remove_coefficients_flags A2) as [[opp2 im2] A2'] eqn:E2.
    destruct im1, opp1, im2, opp2; simpl in *; auto; rewrite <- IHA1, <- IHA2;
      autorewrite with mul_db; easy.
Qed.    
*)

(* Input: singleton GType, no coefficients *)
(* Output: negated flag, coefficient-free singleton GType without multiplication *)
Fixpoint normalize_mul_flags (A : GType) : bool * GType :=
  match A with
  | A1 * A2 => let (opp1, A1') := normalize_mul_flags A1 in
              let (opp2, A2') := normalize_mul_flags A2 in
              let opp := opp1 ⊻ opp2 in
              match A1', A2' with
              | I, X => (opp, X) 
              | I, Z => (opp, Z) 
              | I, I => (opp, I) 
              | X, I => (opp, X)
              | X, X => (opp, I) 
              | X, Z => (opp, X * Z) 
              | Z, I => (opp, Z) 
              | Z, X => (negb opp, X * Z)
              | Z, Z => (opp, I) 
              | _,  _  => (false, A)
              end
  | A'      => (false, A')
  end.


Lemma normalize_mul_flags_eq : forall A,
  let (opp, A') := normalize_mul_flags A in (* use eq/Geq instead? *)
  flags_to_coefficients (opp, false, A') == A.
Proof.
  intros.
  induction A; simpl; try easy.
  destruct (normalize_mul_flags A1) as [opp1 A1'] eqn:E1.
  destruct (normalize_mul_flags A2) as [opp2 A2'] eqn:E2.
  simpl in *.
  destruct A1', A2'; try easy;
  inversion E1; inversion E2; subst;
  simpl; autorewrite with mul_db;
  rewrite <- IHA1, <- IHA2;
  destruct opp1, opp2; simpl; autorewrite with mul_db; easy.
Qed.

Lemma normalize_mul_flags_eq' : forall A A' opp im,
  normalize_mul_flags A = (opp, A') ->
  flags_to_coefficients (opp, im, A') == if im then i A else A.
Proof.
  induction A; intros A' opp im H;
    simpl in H; inversion H; subst; try easy.
  destruct (normalize_mul_flags A1) as [opp1 A1'] eqn:E1.
  destruct (normalize_mul_flags A2) as [opp2 A2'] eqn:E2.
  simpl in *.
  specialize (IHA1 _ _ false eq_refl).
  specialize (IHA2 _ _ false eq_refl).
  destruct A1', A2';
  inversion H; subst;
  destruct opp1, opp2, im; simpl in *;
  rewrite <- IHA1, <- IHA2;
  autorewrite with mul_db; try easy.
Qed.

Definition normalize_mul (A : GType) : GType :=
  match (remove_coefficients_flags A) with
    (opp, im, A') => match normalize_mul_flags A' with
                      (opp', A'') => flags_to_coefficients (opp ⊻ opp', im, A'')
                    end
  end.

Arguments normalize_mul A /.

Lemma normalize_mul_eq : forall A, normalize_mul A == A.
Proof.
  intros. unfold normalize_mul.
  destruct (remove_coefficients_flags A) as [[opp im] A'] eqn:E1.
  destruct (normalize_mul_flags A') as [opp' A''] eqn:E2.
  specialize (remove_coefficients_flags_eq A) as RC.
  rewrite E1 in RC.
  simpl in RC.
  rewrite <- RC in *.
  clear E1 RC.
  specialize (normalize_mul_flags_eq' A' A'' opp' im E2) as NM.
  destruct opp, opp', im; simpl in *; rewrite <- NM; autorewrite with mul_db; easy.
Qed.  
  
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
