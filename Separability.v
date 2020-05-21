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


Parameter times : GType -> GType -> GType.

Infix "×" := times (at level 49, right associativity).

Inductive all_I : GType -> Prop :=
| all_I_sing : all_I I
| all_I_tensor  : forall T1 T2, all_I T1 -> all_I T2 -> all_I (T1 ⊗ T2).

Hint Resolve all_I_sing all_I_tensor : sep_db.

(* Could get Z ⊗ (Z ⊗ I) = Z ⊗ (Z × I). 
   This isn't separable at all (it includes the GHZ states), 
   so Z ⊗ (Z × I) must not imply separability?. *) 

Axiom times_assoc : forall A B C, A × (B × C) = (A × B) × C.

Axiom all_I_separable_l : forall A B,
  Singleton A ->
  all_I B ->
  A ⊗ B = A × B.

Axiom all_I_separable_r : forall A B,
  Singleton B ->
  all_I A ->
  A ⊗ B = A × B.

Axiom separable_cap_I : forall A B C,
  Singleton A ->
  A × B ∩ I ⊗ C = A × (B ∩ C).

Axiom separable_cap_S : forall A B C,
  Singleton A ->
  A × B ∩ A ⊗ C = A × (B ∩ C).

Lemma times_expansion2 : forall A B,
  Singleton A ->
  Singleton B ->
  A × B = A ⊗ I ∩ I ⊗ B.
Proof.
  intros.
  rewrite <- (cap_I_l B) at 1; auto.
  rewrite <- separable_cap_I; auto.
  rewrite <- all_I_separable_l; auto with sep_db.
Qed.

Lemma times_expansion3 : forall A B C,
  Singleton A ->
  Singleton B ->
  Singleton C ->
  A × B × C = A ⊗ I ⊗ I ∩ I ⊗ B ⊗ I ∩ I ⊗ I ⊗ C.
Proof.
  intros.
  rewrite <- (cap_I_l C) at 1; auto.
  rewrite <- separable_cap_I; auto.
  rewrite <- (all_I_separable_l B); auto with sep_db.
  rewrite <- separable_cap_I; auto.
  rewrite (all_I_separable_l B) at 1; auto with sep_db.
  rewrite times_assoc.
  rewrite (times_expansion2 A B); auto.
  (* not sure if there's a valid distribution rule, 
     or happy with what we have *)
  
Qed.  

  (* Examples *)


