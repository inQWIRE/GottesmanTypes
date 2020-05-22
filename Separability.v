Require Import Typing.
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

Axiom all_I_separable_l : forall A IS,
  Pauli A ->
  all_I IS ->
  A ⊗ IS = A × IS.

Axiom all_I_separable_r : forall A IS,
  Pauli A ->
  all_I IS ->
  IS ⊗ A = IS × A.

Axiom separable_cap_I : forall A B C,
  Pauli A ->
  A × B ∩ I ⊗ C = A × (B ∩ C).

Axiom separable_cap_S : forall A B C,
  Pauli A ->
  A × B ∩ A ⊗ C = A × (B ∩ C).

(* Not valid. Hence: I ⊗ I <> I × I. *)
Lemma bad_expansion : X ⊗ I ⊗ I = X × I × I.
Proof.
  rewrite all_I_separable_l; auto with sep_db sing_db.
  rewrite all_I_separable_r; auto with sep_db sing_db.
Abort.
  
Lemma times_expansion2 : forall A B,
  Pauli A ->
  Pauli B ->
  A × B = A ⊗ I ∩ I ⊗ B.
Proof.
  intros.
  rewrite all_I_separable_l; auto with sep_db.
  rewrite separable_cap_I; auto.
  rewrite cap_I_l; auto with sep_db.
Qed.

Lemma times_expansion3 : forall A B C,
  Pauli A ->
  Pauli B ->
  Pauli C ->
  A × B × C = A ⊗ I ⊗ I ∩ I ⊗ B ⊗ I ∩ I ⊗ I ⊗ C.
Proof.
  intros.
  rewrite (all_I_separable_l A); auto with sep_db.
  rewrite separable_cap_I; auto.
  rewrite (cap_I_l_gen (B ⊗ I)); auto with sep_db.
  rewrite separable_cap_I; auto.
  rewrite <- times_expansion2; auto.
Qed.  

Lemma times_expansion4 : forall A B C D,
  Pauli A ->
  Pauli B ->
  Pauli C ->
  Pauli D ->
  A × B × C × D = A ⊗ I ⊗ I ⊗ I ∩ I ⊗ B ⊗ I ⊗ I ∩ I ⊗ I ⊗ C ⊗ I ∩ I ⊗ I ⊗ I ⊗ D.
Proof.
  intros.
  rewrite (all_I_separable_l A); auto with sep_db.
  rewrite separable_cap_I; auto.
  rewrite (cap_I_l_gen (B ⊗ I ⊗ I)); auto with sep_db.
  rewrite separable_cap_I; auto.
  rewrite separable_cap_I; auto.
  rewrite <- times_expansion3; auto.
Qed.  


  (* Examples *)


