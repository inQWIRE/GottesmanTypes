Require Export Typing.
Require Import MoreExamples.
Require Import Setoid.

(* Intersection rules *)
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

(*
(* Defining separability *)

Inductive Separable : nat -> GType -> Prop :=
| sep_sing : forall A, Pauli A -> Separable 0 A
| sep_I_l : forall A k, Separable k A -> Separable (s k) (I ⊗ A)
| sep_I_r : forall A k, Separable k A -> Separable k (A ⊗ I).
*)


Parameter times : GType -> GType -> GType.

Infix "×" := times (at level 49, right associativity).

Axiom times_cap_dist_l : forall A B C,
  A × (B ∩ C) = A × B ∩ A × C.                         

Axiom times_cap_dist_r : forall A B C,
 (A ∩ B) × C = A × C ∩ B × C.

Inductive all_I : GType -> Prop :=
| all_I_sing : all_I I
| all_I_tensor  : forall T1 T2, all_I T1 -> all_I T2 -> all_I (T1 ⊗ T2).

(* Should have a size restriction *)
Axiom cap_I_l_gen : forall A IS,
  all_I IS ->  
  IS ∩ A = A.

Lemma cap_I_r_gen : forall A IS,
  all_I IS ->  
  A ∩ IS = A.
Proof. intros; rewrite cap_comm, cap_I_l_gen; easy. Qed.

Hint Constructors Pauli : sep_db.
Hint Resolve Pauli_Singleton : sep_db.
Hint Resolve all_I_sing all_I_tensor : sep_db.

(* Could get Z ⊗ (Z ⊗ I) = Z ⊗ (Z × I). 
   This isn't separable at all (it includes the GHZ states), 
   so Z ⊗ (Z × I) must not imply separability?. *) 

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

(** ** GHZ SEP *)

Lemma SEP0_ZZZ : SEP0 :: Z × Z × Z → X × Z × Z.
Proof.
  rewrite sep_expansion3 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  type_check_base.
  type_check_base.
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_l X _); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I)); auto with sep_db.
  rewrite (all_I_sep_l Z I); auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite cap_I_l; auto with sing_db.
Qed.

(** Unentangling one qubit *)

Lemma PSEP10_ZZZ : PSEP10 :: Z × Z × Z → Z × (X ⊗ X ∩ Z ⊗ Z).
Proof.
  rewrite sep_expansion3 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  type_check_base.
  type_check_base.
  type_check_base.
  normalize_mul.
  rewrite (cap_comm (I ⊗ _)).
  rewrite (all_I_sep_l Z (I ⊗ I)); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (X ⊗ X)); auto with sep_db.
Qed.
      
(** ** Superdense Coding *)

Lemma superdense_types_sep : superdense :: Z × Z × Z × Z → Z × Z × Z × Z.
Proof.
  rewrite sep_expansion4 at 1; auto with sep_db.
  eapply eq_arrow_r.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  apply cap_arrow_distributes; apply cap_intro.
  type_check_base.
  type_check_base.
  type_check_base.
  type_check_base.
  normalize_mul.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I ⊗ I)); auto with sep_db.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite (cap_I_l_gen (Z ⊗ I)); auto with sep_db.
  rewrite sep_cap_same_l; auto with sep_db.
  rewrite (all_I_sep_l Z); auto with sep_db.
  rewrite sep_cap_I_l; auto with sep_db.
  rewrite cap_I_l; auto with sep_db.
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
