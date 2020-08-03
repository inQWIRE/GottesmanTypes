Require Export Programs.
Require Export DerivedGates.
Require Import Setoid.

(* Non-I Singleton's *)
Inductive Pauli : GType -> Prop :=
| PX : Pauli X
| PZ : Pauli Z
| PXZ : Pauli (X * Z)
| Pim : forall A, Pauli A -> Pauli (i A)
| Pneg : forall A, Pauli A -> Pauli (- A).

Lemma Pauli_Singleton : forall A, Pauli A -> Singleton A.
Proof.
  intros A H; induction H; auto with sing_db.
Qed.  

Inductive all_I : GType -> Prop :=
| all_I_sing : all_I I
| all_I_tensor  : forall T1 T2, all_I T1 -> all_I T2 -> all_I (T1 ⊗ T2).

Axiom cap_I_l_gen : forall A IS,
  size IS = size A ->
  all_I IS ->
  IS ∩ A = A.

Lemma cap_I_r_gen : forall A IS,
  size IS = size A ->
  all_I IS ->  
  A ∩ IS = A.
Proof. intros; rewrite cap_comm; rewrite cap_I_l_gen; easy. Qed.

Hint Constructors Pauli : sep_db.
Hint Resolve Pauli_Singleton : sep_db.
Hint Resolve all_I_sing all_I_tensor : sep_db.

(* TODO: Move elsewhere. To own file? *)
Require Import List.
Import ListNotations.

Fixpoint list_to_tensor (l : list GType) : GType :=
  match l with
  | []  => □ (* failure *)
  | [A] => A
  | A :: As => A ⊗ (list_to_tensor As)
  end.

Fixpoint tensor_to_list (A : GType) : list GType :=
  match A with
  | A ⊗ B => tensor_to_list A ++ tensor_to_list B
  | _     => [A]
  end.

Lemma tensor_to_list_inv : forall l,
    l <> [] ->
    Forall (fun A => Singleton A) l ->
    tensor_to_list (list_to_tensor l) = l.
Proof.
  intros l H F.
  induction l; try easy.
  clear H.
  simpl.
  destruct l.
  destruct a; try easy. inversion F. inversion H1.
  Local Opaque list_to_tensor.
  simpl.
  rewrite IHl; try easy.
  Local Transparent list_to_tensor.
  destruct a; try easy. inversion F. inversion H1.
  inversion F; easy.
Qed.

Lemma tensor_to_list_non_empty : forall G,
    tensor_to_list G <> [].
Proof.
  induction G; simpl; try easy.
  intros F. apply app_eq_nil in F as [F1 F2].
  auto.
Qed.

Lemma list_to_tensor_dist : forall l1 l2,
    l1 <> [] ->
    l2 <> [] ->
    list_to_tensor (l1 ++ l2) == list_to_tensor l1 ⊗ list_to_tensor l2.
Proof.
  intros l1 l2 H.
  induction l1; intros; try easy.
  simpl. clear H.
  destruct (l1 ++ l2) eqn:E.
  - apply app_eq_nil in E as [E1 E2]; subst. easy.
  - destruct l1.
    simpl in E.
    rewrite E.
    reflexivity.
    rewrite IHl1; trivial.
    rewrite tensor_assoc. easy.
    easy.
Qed.    
  
Lemma list_to_tensor_inv : forall G,
    list_to_tensor (tensor_to_list G) == G.
Proof.
  induction G; try easy.
  simpl.
  rewrite list_to_tensor_dist; try apply tensor_to_list_non_empty.
  rewrite IHG1, IHG2.
  easy.
Qed.
  
Definition pad (l r : nat) (P A : GType) :=
  list_to_tensor (repeat P l ++ [A] ++ repeat P r).

(*
Fixpoint padl (l : nat) (P A : GType) :=
  match l with
  | 0 => A
  | S l' => P ⊗ padl l' P A
  end.
  
Fixpoint pad (l r : nat) (P A : GType) :=
  match r with
  | 0    => padl l P A
  | S r' => (pad l r' P (A ⊗ P)) 
  end.
 *)

Compute (pad 2 3 I X).

Definition padI l r A := pad l r I A.
Definition padB l r A := pad l r □ A.

Require Import Arith.
Require Import Bool.

(* Update in a tensor *)
Fixpoint tupdate (n : nat) (T A : GType) :=    
  match T with
  | T1 ⊗ T2  => if n <? size T1 then tupdate n T1 A ⊗ T2
               else T1 ⊗ tupdate (n - size T1) T2 A
  | T1 ∩ T2  => tupdate n T1 A ∩ tupdate n T2 A
  | _        => if (n =? 0) && (size T =? 1) then A (* success *)
               else T (* failure *)
  end.

(* get singleton from tensor *)
Fixpoint tget (n : nat) (T : GType) : GType :=    
  match T with
  | T1 ⊗ T2  => if n <? size T1 then tget n T1 else tget (n - size T1) T2
  | _        => if (n =? 0) && (size T =? 1) then T (* success *)
               else □ (* failure *)
  end.

Compute tget 2 (X ⊗ Z ⊗ X*Z ⊗ -Z ⊗ Y).
Compute tupdate 2 (X ⊗ Z ⊗ X*Z ⊗ -Z ⊗ Y) (i Y).

(* Need more generalizable versions of both of these *)
Axiom singleton_sep : forall l r A,
  Pauli A ->
  padI l r A == padB l r A.

Axiom singleton_sep_propagate : forall l r A B,
  Pauli A -> 
  padB l r A ∩ B == padB l r A ∩ tupdate l B □.

Fixpoint sep_of_list_aux (l r : nat) (Gs : list GType) : GType :=
  match Gs with
  | []     => □
  | [A]    => padB l r A
  | A :: As => padB l r A ∩ sep_of_list_aux (l + 1) (r - 1) As
  end.

Definition sep_of_list (Gs : list GType) : GType :=
  sep_of_list_aux 0 (length Gs - 1) Gs.

Import ListNotations.

Compute sep_of_list (X :: Y :: Z :: -X :: []).

Notation "x × y × .. × z" := (sep_of_list (cons x (cons y .. (cons z nil) ..))) (at level 90).

Compute (X × Y × Z).

Axiom times_assoc : forall A B C, A × (B × C) = (A × B) × C.

Axiom all_I_sep_l : forall A IS,
  Pauli A ->
  all_I IS ->
  A ⊗ IS = A × IS.

Axiom all_I_sep_r : forall A IS,
  Pauli A ->
  all_I IS ->
  IS ⊗ A = IS × A.

Axiom sep_cap_I_l : forall A B C,
  Pauli A ->
  A × B ∩ I ⊗ C = A × (B ∩ C).

Axiom sep_cap_I_r : forall A B C,
  Pauli B ->
  A × B ∩ C ⊗ I = (A ∩ C) × B.

Axiom sep_cap_same_l : forall A B C,
  Pauli A ->
  A × B ∩ A ⊗ C = A × (B ∩ C).

Axiom sep_cap_same_r : forall A B C,
  Pauli B ->
  A × B ∩ C ⊗ B = (A ∩ C) × B.


(* Not valid. Hence: I ⊗ I <> I × I. *)
Lemma invalid_expansion : X ⊗ I ⊗ I = X × I × I.
Proof.
  rewrite all_I_sep_l; auto with sep_db sing_db.
  rewrite all_I_sep_r; auto with sep_db sing_db.
Abort.

Lemma sep_expansion2 : forall A B,
  Pauli A ->
  Pauli B ->
  A × B = A ⊗ I ∩ I ⊗ B.
Proof.
  intros.
  rewrite all_I_sep_l; auto with sep_db.
  rewrite sep_cap_I_l; auto.
  rewrite cap_I_l; auto with sep_db.
Qed.
    
Lemma sep_expansion3 : forall A B C,
  Pauli A ->
  Pauli B ->
  Pauli C ->
  A × B × C = A ⊗ I ⊗ I ∩ I ⊗ B ⊗ I ∩ I ⊗ I ⊗ C.
Proof.
  intros.
  rewrite (all_I_sep_l A); auto with sep_db.
  rewrite sep_cap_I_l; auto.
  rewrite (cap_I_l_gen (B ⊗ I)); auto with sep_db.
  rewrite sep_cap_I_l; auto.
  rewrite <- sep_expansion2; auto.
Qed.  

Lemma sep_expansion4 : forall A B C D,
  Pauli A ->
  Pauli B ->
  Pauli C ->
  Pauli D ->
  A × B × C × D = A ⊗ I ⊗ I ⊗ I ∩ I ⊗ B ⊗ I ⊗ I ∩ I ⊗ I ⊗ C ⊗ I ∩ I ⊗ I ⊗ I ⊗ D.
Proof.
  intros.
  rewrite (all_I_sep_l A); auto with sep_db.
  rewrite sep_cap_I_l; auto.
  rewrite (cap_I_l_gen (B ⊗ I ⊗ I)); auto with sep_db.
  rewrite sep_cap_I_l; auto.
  rewrite sep_cap_I_l; auto.
  rewrite <- sep_expansion3; auto.
Qed.  

(** * Examples *)

(** ** CNOT *)

Lemma CNOT_ZX : CNOT 0 1 :: Z × X → Z × X.
Proof.
  rewrite sep_expansion2; auto with sep_db.
  apply cap_arrow_distributes.
  type_check_base.
Qed.

Lemma CNOT_ZZ : CNOT 0 1 :: Z × Z → Z × Z.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  rewrite all_I_sep_l; auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

Lemma CNOT_XX : CNOT 0 1 :: X × X → X × X.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  rewrite (all_I_sep_r X I); auto with sep_db.
  rewrite cap_comm.
  rewrite sep_cap_same_r; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

(** ** SWAP *)

Lemma SWAP_XX : SWAP 0 1 :: X × X → X × X.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_r X I); auto with sep_db.
  rewrite sep_cap_I_r; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

Lemma SWAP_XZ : SWAP 0 1 :: X × Z → Z × X.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_r X I); auto with sep_db.
  rewrite sep_cap_I_r; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

Lemma SWAP_ZX : SWAP 0 1 :: Z × X → X × Z.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_r Z I); auto with sep_db.
  rewrite sep_cap_I_r; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

Lemma SWAP_ZZ : SWAP 0 1 :: Z × Z → Z × Z.
Proof.
  rewrite sep_expansion2 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes.  
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_r Z I); auto with sep_db.
  rewrite sep_cap_I_r; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.
      

(*

(* Attempt to generalize sep_expansion lemmas. *)

Require Import List.

Parameter bot : GType.
Notation "⊥" := bot.
Parameter tensor_id : GType.
Notation "∅" := tensor_id.
Axiom tensor_id_l : forall A, ∅ ⊗ A = A.
Axiom tensor_id_r : forall A, A ⊗ ∅ = A.
Axiom times_id_l : forall A, ∅ × A = A.
Axiom times_id_r : forall A, A × ∅ = A.

Fixpoint big_times (l : list GType) : GType :=
  match l with
  | nil => ∅
  | cons A TS => A × big_times TS
  end.

Fixpoint repeat_I (n : nat) : GType :=
  match n with
  | 0 => ∅
  | s n' => I ⊗ repeat_I n'
  end.

Definition pauli_at (A : GType) (m n : nat) : GType :=
  repeat_I m ⊗ A ⊗ repeat_I n.

Fixpoint to_sep_list' (l : list GType) (m n : nat) :=
  match n with
  | 0    => pauli_at (hd ⊥ l) m 0
  | s n' => pauli_at (hd ⊥ l) m n ∩ to_sep_list' (tl l) (s m) n'
  end.

Definition to_sep_list (l : list GType) := to_sep_list' l 0 (length l - 1).

Lemma sep_expansion : forall (l : list GType),
  length l <> 0 ->
  Forall Pauli l ->
  big_times l = to_sep_list l.
Proof.
  intros.
  induction l; try contradiction.
  destruct l as [| b l].
  - cbv.
    rewrite tensor_id_l, tensor_id_r, times_id_r.
    easy.
  - unfold to_sep_list in *.
    simpl in *.
    rewrite IHl; inversion H0; subst; try easy.
    unfold pauli_at. simpl.
    rewrite tensor_id_l.
(* works, but not worth it. We'll use Ltac. *)
Abort.

*)
